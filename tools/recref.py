#!/usr/bin/env python3
"""Reference derivation of recursors for inductive blocks (single, mutual,
nested), checked against an export's own recursors -- the algorithm the
Bend kernel ports. Locally nameless: free variables are fresh constants,
abstracted into binders at the end (Lean's kernel builds them the same way).

usage: recref.py EXPORT.ndjson [NAME-SUBSTRING]
"""
import json, os, sys, itertools

# ---- terms: tuples ----------------------------------------------------------
# ('bv',i) ('sort',lvl) ('c',name,lvls) ('app',f,a) ('lam',ty,b) ('pi',ty,b)
# ('let',ty,v,b) ('lit',n) ('str',s) ('proj',tn,i,s) ('fv',k)
class Ex:
    def __init__(s, path):
        s.N, s.L, s.E, s.decls = {}, {}, {}, []
        for line in open(path):
            r = json.loads(line)
            if 'in' in r: s.N[r['in']] = r
            elif 'il' in r: s.L[r['il']] = r
            elif 'ie' in r: s.E[r['ie']] = r
            else: s.decls.append(r)
        s.memo = {}
    def nm(s, i):
        if i == 0: return ''
        r = s.N[i]
        for k in ('str', 'num'):
            if k in r:
                p = s.nm(r[k]['pre']); x = r[k].get('str', r[k].get('i'))
                return (p + '.' if p else '') + str(x)
    def lvl(s, i):
        if i not in s.L: return ('z',)
        r = s.L[i]
        if 'zero' in r or r.get('il') == 0 and len(r) == 1: return ('z',)
        for k, v in r.items():
            if k == 'il': continue
            if k == 'succ': return ('s', s.lvl(v))
            if k == 'max': return ('max', s.lvl(v[0]), s.lvl(v[1]))
            if k == 'imax': return ('imax', s.lvl(v[0]), s.lvl(v[1]))
            if k == 'param': return ('p', s.nm(v))
        return ('z',)
    def ex(s, i):
        if i in s.memo: return s.memo[i]
        r = s.E[i]; t = None
        if 'bvar' in r: t = ('bv', r['bvar'])
        elif 'sort' in r: t = ('sort', s.lvl(r['sort']))
        elif 'const' in r: t = ('c', s.nm(r['const']['name']), tuple(s.lvl(u) for u in r['const']['us']))
        elif 'app' in r: t = ('app', s.ex(r['app']['fn']), s.ex(r['app']['arg']))
        elif 'lam' in r: t = ('lam', s.ex(r['lam']['type']), s.ex(r['lam']['body']))
        elif 'forallE' in r: t = ('pi', s.ex(r['forallE']['type']), s.ex(r['forallE']['body']))
        elif 'letE' in r: t = ('let', s.ex(r['letE']['type']), s.ex(r['letE']['value']), s.ex(r['letE']['body']))
        elif 'natVal' in r: t = ('lit', r['natVal'])
        elif 'strVal' in r: t = ('str', r['strVal'])
        elif 'proj' in r: t = ('proj', s.nm(r['proj']['typeName']), r['proj']['idx'], s.ex(r['proj']['struct']))
        else: raise Exception(r)
        s.memo[i] = t; return t

# ---- de Bruijn ops ----------------------------------------------------------
def inst(t, v, d=0):            # replace bv d by v (v closed: fvars), decrement above
    k = t[0]
    if k == 'bv': return v if t[1] == d else (('bv', t[1]-1) if t[1] > d else t)
    if k == 'app': return ('app', inst(t[1], v, d), inst(t[2], v, d))
    if k in ('lam', 'pi'): return (k, inst(t[1], v, d), inst(t[2], v, d+1))
    if k == 'let': return ('let', inst(t[1], v, d), inst(t[2], v, d), inst(t[3], v, d+1))
    if k == 'proj': return ('proj', t[1], t[2], inst(t[3], v, d))
    return t
def abst(t, fv, d=0):           # replace ('fv',fv) by bv d
    k = t[0]
    if k == 'fv': return ('bv', d) if t[1] == fv else t
    if k == 'app': return ('app', abst(t[1], fv, d), abst(t[2], fv, d))
    if k in ('lam', 'pi'): return (k, abst(t[1], fv, d), abst(t[2], fv, d+1))
    if k == 'let': return ('let', abst(t[1], fv, d), abst(t[2], fv, d), abst(t[3], fv, d+1))
    if k == 'proj': return ('proj', t[1], t[2], abst(t[3], fv, d))
    return t
def _expl(l):                   # explicit level (succ^n zero): n, else None
    n = 0
    while l[0] == 's': l = l[1]; n += 1
    return n if l[0] == 'z' else None
def _notzero(l):
    if l[0] == 's': return True
    if l[0] == 'max': return _notzero(l[1]) or _notzero(l[2])
    if l[0] == 'imax': return _notzero(l[2])
    return False
def mk_max(a, b):               # Lean's level smart constructor
    ea, eb = _expl(a), _expl(b)
    if ea is not None and eb is not None: return a if ea >= eb else b
    if a == b: return a
    if a == ('z',): return b
    if b == ('z',): return a
    if b[0] == 'max' and (b[1] == a or b[2] == a): return b
    return ('max', a, b)
def mk_imax(a, b):
    if _notzero(b): return mk_max(a, b)
    if b == ('z',): return b
    if a == ('z',): return b
    if a == b: return a
    return ('imax', a, b)
def lsub(t, sub):               # level param substitution
    def L(l):
        if l[0] == 'p': return sub.get(l[1], l)
        if l[0] == 's': return ('s', L(l[1]))
        if l[0] == 'max': return mk_max(L(l[1]), L(l[2]))
        if l[0] == 'imax': return mk_imax(L(l[1]), L(l[2]))
        return l
    k = t[0]
    if k == 'sort': return ('sort', L(t[1]))
    if k == 'c': return ('c', t[1], tuple(L(u) for u in t[2]))
    if k == 'app': return ('app', lsub(t[1], sub), lsub(t[2], sub))
    if k in ('lam', 'pi'): return (k, lsub(t[1], sub), lsub(t[2], sub))
    if k == 'let': return ('let', lsub(t[1], sub), lsub(t[2], sub), lsub(t[3], sub))
    if k == 'proj': return ('proj', t[1], t[2], lsub(t[3], sub))
    return t
def app(f, *xs):
    for x in xs: f = ('app', f, x)
    return f
def spine(t):
    xs = []
    while t[0] == 'app': xs.append(t[2]); t = t[1]
    return t, xs[::-1]
def mkpi(fvs, body):            # fvs: [(k, ty)] outermost first
    for k, ty in reversed(fvs): body = ('pi', ty, abst(body, k))
    return body
def mklam(fvs, body):
    for k, ty in reversed(fvs): body = ('lam', ty, abst(body, k))
    return body
def occurs(t, names):
    k = t[0]
    if k == 'c': return t[1] in names
    if k == 'app': return occurs(t[1], names) or occurs(t[2], names)
    if k in ('lam', 'pi'): return occurs(t[1], names) or occurs(t[2], names)
    if k == 'let': return any(occurs(x, names) for x in t[1:])
    if k == 'proj': return occurs(t[3], names)
    return False

DEFS = {}                       # name -> (level param names, value)
def whnf(t):                    # head beta + delta of definitions (enough here)
    while True:
        h, xs = spine(t)
        if h[0] == 'lam' and xs:
            b = inst(h[2], xs[0]); t = app(b, *xs[1:]); continue
        if h[0] == 'c' and h[1] in DEFS:
            lp, v = DEFS[h[1]]
            t = app(lsub(v, dict(zip(lp, h[2]))), *xs); continue
        return t

def tele_whnf(ty):              # Lean's is_rec_argument: whnf at each Pi
    out = []
    ty = whnf(ty)
    while ty[0] == 'pi':
        x = fv(); out.append((x[1], ty[1])); ty = whnf(inst(ty[2], x))
    return out, ty

def strip_ann(t):
    while True:
        h, xs = spine(t)
        if h[0] == 'c' and h[1] in ('optParam', 'autoParam') and len(xs) == 2:
            t = xs[0]; continue
        if h[0] == 'c' and h[1] in ('outParam', 'semiOutParam') and len(xs) == 1:
            t = xs[0]; continue
        return t

FRESH = itertools.count(1)
def fv(): return ('fv', next(FRESH))

def tele(ty, n=None):           # instantiate a Pi telescope with fresh fvars
    out = []
    while ty[0] == 'pi' and (n is None or len(out) < n):
        x = fv(); out.append((x[1], ty[1])); ty = inst(ty[2], x)
    return out, ty

# ---- the block --------------------------------------------------------------
def derive(X, blk, inds):
    """blk: the export's inductive record; inds: name -> inductive record
    for earlier blocks (nested occurrences' inductives)"""
    types = blk['types']; ctors = {X.nm(c['name']): c for c in blk['ctors']}
    tnames = [X.nm(t['name']) for t in types]
    np = types[0]['numParams']
    lps = [X.nm(l) for l in types[0]['levelParams']]
    us0 = tuple(('p', l) for l in lps)
    # params: from the first type's telescope
    params, _ = tele(X.ex(types[0]['type']), np)
    # Lean's mk_local_decl_for: every binder the kernel opens -- params,
    # indices, fields -- has its type's annotations consumed
    params = [(k, strip_ann(t)) for k, t in params]
    pv = [('fv', k) for k, _ in params]
    # specs: (head name, level args, param args (in terms of param fvars))
    specs = [(n, us0, tuple(pv)) for n in tnames]
    def ind_rec(n):               # inductive record for a type name
        return inds[n] if n not in tnames else blk
    def ind_type(n):
        b = ind_rec(n)
        for t in b['types']:
            if X.nm(t['name']) == n: return t
    def ctor_list(n):
        b = ind_rec(n); t = ind_type(n)
        cs = {X.nm(c['name']): c for c in b['ctors']}
        return [(X.nm(c), cs[X.nm(c)]) for c in t['ctors']]
    def spec_of(t):               # (spec index, index args) if t is a spec app
        h, xs = spine(t)
        if h[0] != 'c': return None
        for j, (n, us, ps) in enumerate(specs):
            if h[1] == n and h[2] == us and tuple(xs[:len(ps)]) == ps:
                return j, xs[len(ps):]
        return None
    def ctor_inst(j, cname, c):    # the ctor's type with spec j's levels/params
        n, us, ps = specs[j]
        cty = X.ex(c['type'])
        sub = dict(zip([X.nm(l) for l in c['levelParams']], us))
        cty = lsub(cty, sub)
        for p in ps:
            assert cty[0] == 'pi'; cty = inst(cty[2], p)
        return cty
    # discover nested occurrences (BFS over specs' ctor fields)
    j = 0
    allnames = set(tnames)
    while j < len(specs):
        n, us, ps = specs[j]
        for cname, c in ctor_list(n):
            cty = ctor_inst(j, cname, c)
            fields, res = tele(cty)
            for _, fty in fields:
                zs, fres = tele(fty)
                h, xs = spine(fres)
                if h[0] == 'c' and h[1] not in tnames and h[1] in inds:
                    jt = ind_type(h[1]); jnp = jt['numParams']
                    pa = tuple(xs[:jnp])
                    if any(occurs(a, allnames) for a in pa) and spec_of(fres) is None:
                        specs.append((h[1], h[2], pa))
        j += 1
    nmot = len(specs)
    # elimination universe: assume large (motive level param = first rec lp)
    return specs, params, ctor_list, ctor_inst, spec_of, np, lps, tnames

def build(X, blk, inds):
    specs, params, ctor_list, ctor_inst, spec_of, np, lps, tnames = derive(X, blk, inds)
    rec0 = blk['recs'][0]
    rlps = [X.nm(l) for l in rec0['levelParams']]
    large = len(rlps) > len(lps)
    v = ('p', rlps[0]) if large else ('z',)
    rus = tuple(('p', l) for l in rlps)
    pv = [('fv', k) for k, _ in params]
    def ind_type_of(j):
        n, us, ps = specs[j]
        for b in [blk] + list(INDS.values()):
            for t in b['types']:
                if X.nm(t['name']) == n:
                    ty = lsub(X.ex(t['type']), dict(zip([X.nm(l) for l in t['levelParams']], us)))
                    for p in ps: ty = inst(ty[2], p)
                    return ty
    # motives
    motives = []
    for j, (n, us, ps) in enumerate(specs):
        idx, _ = tele(ind_type_of(j))
        idx = [(k, strip_ann(t)) for k, t in idx]
        t = fv()
        mty = mkpi(idx + [(t[1], app(('c', n, us), *ps, *[('fv', k) for k, _ in idx]))], ('sort', v))
        motives.append((next(FRESH), mty))
    mv = [('fv', k) for k, _ in motives]
    # minors
    minors = []; minfo = []
    for j, (n, us, ps) in enumerate(specs):
        for cname, c in ctor_list(n):
            cty = ctor_inst(j, cname, c)
            fields, res = tele(cty)
            # Lean's consume_type_annotations: optParam/autoParam/outParam
            # wrappers on a field's type are dropped in the minor premise
            fields = [(k, strip_ann(t)) for k, t in fields]
            ihs = []
            for fk, fty in fields:
                zs, fres = tele_whnf(fty)
                sp = spec_of(fres)
                if sp is not None:
                    k, ix = sp
                    ihs.append((next(FRESH), mkpi(zs, app(mv[k], *ix, app(('fv', fk), *[('fv', z) for z, _ in zs]))), fk, k, zs, ix))
            _, rxs = spine(res)
            body = app(mv[j], *rxs[len(ps):], app(('c', cname, us), *ps, *[('fv', k) for k, _ in fields]))
            mk = next(FRESH)
            minors.append((mk, mkpi(fields + [(h[0], h[1]) for h in ihs], body)))
            minfo.append((j, cname, fields, ihs))
    nv = [('fv', k) for k, _ in minors]
    # recursor names: block types' own, then aux rec_1..
    def rec_name(j):
        return specs[j][0] + '.rec' if j < len(tnames) else tnames[0] + '.rec_%d' % (j - len(tnames) + 1)
    out = {}
    for j, (n, us, ps) in enumerate(specs):
        idx, _ = tele(ind_type_of(j))
        idx = [(k, strip_ann(t)) for k, t in idx]
        t = fv()
        tail = mkpi(idx + [(t[1], app(('c', n, us), *ps, *[('fv', k) for k, _ in idx]))],
                    app(mv[j], *[('fv', k) for k, _ in idx], t))
        rty = mkpi(params + motives + minors, tail)
        rules = []
        for mi, (jj, cname, fields, ihs) in enumerate(minfo):
            if jj != j: continue
            ihv = []
            for (hk, hty, fk, k, zs, ix) in ihs:
                ihv.append(mklam(zs, app(('c', rec_name(k), rus), *pv, *mv, *nv, *ix, app(('fv', fk), *[('fv', z) for z, _ in zs]))))
            rhs = mklam(params + motives + minors + fields, app(nv[mi], *[('fv', k) for k, _ in fields], *ihv))
            rules.append((cname, len(fields), rhs))
        out[rec_name(j)] = (rty, rules)
    return out

INDS = {}
def main():
    X = Ex(sys.argv[1]); filt = sys.argv[2] if len(sys.argv) > 2 else None
    ok = bad = 0
    for d in X.decls:
        if 'def' in d:
            DEFS[X.nm(d['def']['name'])] = ([X.nm(l) for l in d['def']['levelParams']], X.ex(d['def']['value']))
        if 'inductive' not in d: continue
        blk = d['inductive']
        names = [X.nm(t['name']) for t in blk['types']]
        nested = any(t.get('numNested', 0) for t in blk['types'])
        mutual = len(names) > 1
        # single blocks too when a name filter selects them
        if (nested or mutual or filt is not None or os.environ.get('ALL')) and (filt is None or any(filt in n for n in names)):
            try:
                out = build(X, blk, INDS)
            except Exception as e:
                print('FAIL build', names, repr(e)); bad += 1
                for t in blk['types']: INDS[X.nm(t['name'])] = blk
                continue
            for r in blk['recs']:
                rn = X.nm(r['name'])
                if rn not in out: print('MISSING rec', rn, list(out)); bad += 1; continue
                rty, rules = out[rn]
                ety = X.ex(r['type'])
                tyok = (rty == ety)
                rok = len(rules) == len(r['rules']) and all(
                    X.nm(er['ctor']) == c and er['nfields'] == nf and X.ex(er['rhs']) == rhs
                    for (c, nf, rhs), er in zip(rules, r['rules']))
                if tyok and rok: ok += 1
                else:
                    bad += 1; print('MISMATCH', rn, 'type' if not tyok else '', 'rules' if not rok else '')
        for t in blk['types']: INDS[X.nm(t['name'])] = blk
    print('recursors matched', ok, 'mismatched', bad)

if __name__ == '__main__':
    main()
