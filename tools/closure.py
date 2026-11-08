#!/usr/bin/env python3
"""closure.py EXPORT.ndjson: how much of an export the structural checks can
reach -- every subterm of the inductive blocks' types, constructor and
recursor types and rule right-hand sides and of the quotient declarations,
closed over constants (each reached constant's declared type, and value when
it has one). Prints the closure's node count against the export's."""
import json, sys
from array import array

kids = {}          # expression index -> tuple of child indices
cname = {}         # expression index -> constant name (const nodes)
decl = {}          # name -> (type, value or -1)
roots = []
nx = 0
with open(sys.argv[1]) as f:
    for line in f:
        if line.startswith('{"in"') or line.startswith('{"il"'):
            continue
        r = json.loads(line)
        if 'ie' in r:
            i = r['ie']; nx = max(nx, i + 1)
            for k, v in r.items():
                if k == 'ie':
                    continue
                if k == 'app': kids[i] = (v['fn'], v['arg'])
                elif k in ('lam', 'forallE'): kids[i] = (v['type'], v['body'])
                elif k == 'letE': kids[i] = (v['type'], v['value'], v['body'])
                elif k == 'proj': kids[i] = (v['struct'],)
                elif k == 'const': cname[i] = v['name']
            continue
        for k in ('def', 'thm', 'opaque', 'axiom', 'quot'):
            if k in r:
                d = r[k]; decl[d['name']] = (d['type'], d.get('value', -1))
                if k == 'quot':
                    roots.append(d['type'])
        if 'inductive' in r:
            b = r['inductive']
            for t in b['types']:
                roots.append(t['type']); decl[t['name']] = (t['type'], -1)
            for c in b['ctors']:
                roots.append(c['type']); decl[c['name']] = (c['type'], -1)
            for rc in b['recs']:
                roots.append(rc['type']); decl[rc['name']] = (rc['type'], -1)
                for ru in rc['rules']:
                    roots.append(ru['rhs'])
seen = bytearray(nx)
seenc = set()
st = list(roots)
while st:
    i = st.pop()
    if i < 0 or i >= nx or seen[i]:
        continue
    seen[i] = 1
    st.extend(kids.get(i, ()))
    n = cname.get(i)
    if n is not None and n not in seenc:
        seenc.add(n)
        t, v = decl.get(n, (-1, -1))
        st.append(t); st.append(v)
c = sum(seen)
print(f"{sys.argv[1].split('/')[-1]}: closure {c} of {nx} expressions ({100.0 * c / max(nx, 1):.1f}%), {len(seenc)} constants")
