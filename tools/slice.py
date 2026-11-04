#!/usr/bin/env python3
"""Dependency-closed, RENUMBERED slice of a large arena .ndjson (mathlib-size).

    python3 tools/slice.py IN.ndjson OUT.ndjson NAME [NAME ...]

tools/extract.py loads every record (impossible at 6 GB) and keeps the
original ids, so km's store, sized by the largest expression id, stays
corpus-sized.  Here: one forward pass indexes every record's byte offset
(cached in IN.ndjson.sidx/, reused by later slices), a DFS from the named
declarations follows types, values, ctor/rec types, rule rhs, `all` lists,
const and proj names; the first PRE (4000) declarations -- the Init prelude,
whose builtins (Nat.le, UInt8, ...) Lean's kernel looks up itself -- are kept
whole.  Kept records are written in file order with names, levels and
expressions renumbered densely.  Declaration count of OUT = N for `BIN OUT K N`.
NOT a backward pass: an expression a later declaration shares can precede the
record of a constant it mentions (mathlib's ChainClosure).
"""
import json, re, sys, os, pickle
from array import array

src, dst, *want = sys.argv[1:]
PRE = int(os.environ.get("PRE", "4000"))
RID = re.compile(rb'"(in|il|ie)":(\d+)')
DK = (b'{"thm"', b'{"def"', b'{"opaque"', b'{"axiom"', b'{"quot"', b'{"inductive"')
cache = src + ".sidx"

def decl_names(k, d):
    if k != "inductive": return [d["name"]]
    return ([t["name"] for t in d["types"]] + [c["name"] for c in d["ctors"]]
            + [q["name"] for q in d["recs"]])

if os.path.isdir(cache):
    off = {}
    for k in ("in", "il", "ie"):
        a = array("q"); n = os.path.getsize(f"{cache}/{k}") // 8
        with open(f"{cache}/{k}", "rb") as f: a.fromfile(f, n)
        off[k] = a
    with open(f"{cache}/decls.pkl", "rb") as f: dpos, dorder, pre_end = pickle.load(f)
else:
    off = {"in": array("q", [-1]), "il": array("q", [-1]), "ie": array("q")}
    dpos, dorder, pre_end, at = {}, [], 0, 0
    with open(src, "rb") as f:
        for ln in f:
            if ln.startswith(DK):
                r = json.loads(ln); k = next(iter(r))
                for n in decl_names(k, r[k]): dpos[n] = at
                dorder.append(at)
                if len(dorder) == PRE: pre_end = at + len(ln)
            else:
                m = RID.match(ln, 1) if ln[2:4] in (b"in", b"il") else RID.search(ln)
                if m:
                    a = off[m.group(1).decode()]; i = int(m.group(2))
                    if i != len(a): sys.exit(f"non-dense id {m.group(0)} at {at}")
                    a.append(at)
            at += len(ln)
    os.makedirs(cache, exist_ok=True)
    for k, a in off.items():
        with open(f"{cache}/{k}", "wb") as f: a.tofile(f)
    with open(f"{cache}/decls.pkl", "wb") as f: pickle.dump((dpos, dorder, pre_end), f)

fh = open(src, "rb")
def rec(o):
    fh.seek(o); return json.loads(fh.readline())

# names: wanted ones by string (walk all name records once, cheap via index)
nm_s = {0: ""}
def nstr(i):
    if i in nm_s: return nm_s[i]
    r = rec(off["in"][i]); k = "str" if "str" in r else "num"; d = r[k]
    s = d["str"] if k == "str" else str(d["i"]); p = nstr(d["pre"])
    nm_s[i] = (p + "." + s) if p else s
    return nm_s[i]
wid = {}
for n in dpos:
    s = nstr(n)
    if s in want or s in ("Nat", "String"): wid[s] = n
missing = set(want) - set(wid)
if missing: sys.exit(f"not found: {missing}")

need_n, need_l, need_e, done_o = set(), set(), set(), set()
dq = [dpos[wid[w]] for w in want] + [o for o in dorder if o < pre_end]  # offsets
eq = []

def nm(x):
    while x and x not in need_n:
        need_n.add(x); r = rec(off["in"][x]); x = r["str" if "str" in r else "num"]["pre"]
def lv(x):
    st = [x]
    while st:
        x = st.pop()
        if x == 0 or x in need_l: continue
        need_l.add(x); r = rec(off["il"][x])
        if "succ" in r: st.append(r["succ"])
        elif "max" in r: st += r["max"]
        elif "imax" in r: st += r["imax"]
        elif "param" in r: nm(r["param"])
def needc(n):
    nm(n)
    if n in dpos: dq.append(dpos[n])

while dq or eq:
    while eq:
        x = eq.pop()
        if x in need_e: continue
        need_e.add(x); r = rec(off["ie"][x])
        for k, v in r.items():
            if k == "ie": continue
            if k == "sort": lv(v)
            elif k == "const": needc(v["name"]); [lv(u) for u in v["us"]]
            elif k == "app": eq += [v["fn"], v["arg"]]
            elif k in ("lam", "forallE"): eq += [v["type"], v["body"]]; nm(v["name"])
            elif k == "letE": eq += [v["type"], v["value"], v["body"]]; nm(v["name"])
            elif k == "proj": eq.append(v["struct"]); needc(v["typeName"])
            elif k == "mdata": eq.append(v["expr"])
            elif k == "natVal" and "Nat" in wid: needc(wid["Nat"])
            elif k == "strVal" and "String" in wid: needc(wid["String"])
    if dq:
        o = dq.pop()
        if o in done_o: continue
        done_o.add(o)
        r = rec(o); k = next(iter(r)); d = r[k]
        for n in decl_names(k, d): nm(n)
        if k == "inductive":
            for t in d["types"]:
                eq.append(t["type"]); [nm(x) for x in t["levelParams"]]
                for a in t.get("all", []): needc(a)
            for c in d["ctors"]:
                eq.append(c["type"]); nm(c["induct"]); [nm(x) for x in c["levelParams"]]
            for q in d["recs"]:
                eq.append(q["type"]); [nm(x) for x in q["levelParams"]]
                for a in q.get("all", []): needc(a)
                for ru in q["rules"]: eq.append(ru["rhs"]); nm(ru["ctor"])
        else:
            eq.append(d["type"])
            if "value" in d: eq.append(d["value"])
            for x in d["levelParams"]: nm(x)
            for a in d.get("all", []): needc(a)

# forward: renumber densely in file order
keep = sorted([0] + [off["in"][i] for i in need_n] + [off["il"][i] for i in need_l]
              + [off["ie"][i] for i in need_e] + list(done_o))
N, L, E = {0: 0}, {0: 0}, {}
def n_(x): return N[x]
def l_(x): return L[x]
def e_(x): return E[x]
nd = 0
with open(dst, "w") as out:
    for o in keep:
        r = rec(o)
        if "meta" in r: pass
        elif "in" in r:
            N[r["in"]] = r["in"] = len(N)
            k = "str" if "str" in r else "num"; r[k]["pre"] = n_(r[k]["pre"])
        elif "il" in r:
            L[r["il"]] = r["il"] = len(L)
            for k in ("succ", "param"):
                if k in r: r[k] = (l_ if k == "succ" else n_)(r[k])
            for k in ("max", "imax"):
                if k in r: r[k] = [l_(x) for x in r[k]]
        elif "ie" in r:
            for k, v in r.items():
                if k == "ie": continue
                if k == "sort": r[k] = l_(v)
                elif k == "const": v["name"] = n_(v["name"]); v["us"] = [l_(u) for u in v["us"]]
                elif k == "app": v["fn"] = e_(v["fn"]); v["arg"] = e_(v["arg"])
                elif k in ("lam", "forallE"): v["type"] = e_(v["type"]); v["body"] = e_(v["body"]); v["name"] = n_(v["name"])
                elif k == "letE":
                    for f in ("type", "value", "body"): v[f] = e_(v[f])
                    v["name"] = n_(v["name"])
                elif k == "proj": v["struct"] = e_(v["struct"]); v["typeName"] = n_(v["typeName"])
                elif k == "mdata": v["expr"] = e_(v["expr"])
            E[r["ie"]] = r["ie"] = len(E)
        else:
            nd += 1; k = next(iter(r)); d = r[k]
            def com(d):
                d["name"] = n_(d["name"]); d["type"] = e_(d["type"])
                d["levelParams"] = [n_(x) for x in d["levelParams"]]
                if "all" in d: d["all"] = [n_(x) for x in d["all"]]
            if k == "inductive":
                for t in d["types"]: com(t); t["ctors"] = [n_(x) for x in t["ctors"]]
                for c in d["ctors"]: com(c); c["induct"] = n_(c["induct"])
                for q in d["recs"]:
                    com(q)
                    for ru in q["rules"]: ru["rhs"] = e_(ru["rhs"]); ru["ctor"] = n_(ru["ctor"])
            else:
                com(d)
                if "value" in d: d["value"] = e_(d["value"])
        out.write(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n")
print(f"{nd} declarations, {len(E)} expressions, {len(N)} names -> {dst}")
