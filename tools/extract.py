#!/usr/bin/env python3
"""Cut a DEPENDENCY-CLOSED sub-export out of an arena .ndjson.

    python3 tools/extract.py IN.ndjson OUT.ndjson NAME [NAME ...]

Keeps the named declarations, every declaration they transitively reference
(through types, values, constructor types and recursor rules), and only the
expressions those reach. All name/level records are kept (they are inert).
Truncating a file naively is NOT equivalent: leftover expressions that
reference now-undeclared constants make fjudge's whole-file scan reject.
"""
import json, sys

src, dst, *want = sys.argv[1:]
recs = [json.loads(l) for l in open(src)]
E = {r["ie"]: r for r in recs if "ie" in r}
N = {r["in"]: r for r in recs if "in" in r}

def nm(i):
    r = N.get(i)
    if not r: return ""
    for k in ("str", "num"):
        if k in r and isinstance(r[k], dict):
            p = nm(r[k].get("pre", 0)); s = r[k].get("str", r[k].get("i"))
            return (p + "." if p else "") + str(s)
    return ""

# declaration record -> (names it declares, expression roots)
def decl_info(r):
    for k in ("axiom", "def", "thm", "opaque", "quot"):
        if k in r:
            d = r[k]; roots = [d["type"]] + ([d["value"]] if "value" in d else [])
            return [d["name"]], roots
    if "inductive" in r:
        d = r["inductive"]; names, roots = [], []
        for t in d.get("types", []): names.append(t["name"]); roots.append(t["type"])
        for c in d.get("ctors", []): names.append(c["name"]); roots.append(c["type"])
        for q in d.get("recs", []):
            names.append(q["name"]); roots.append(q["type"])
            roots += [ru["rhs"] for ru in q.get("rules", [])]
        return names, roots
    return None

decls = []  # (record index, names, roots)
byname = {}
for i, r in enumerate(recs):
    info = decl_info(r)
    if info:
        decls.append((i, *info))
        for n in info[0]: byname[n] = len(decls) - 1

CHILD = {"app": ("fn", "arg"), "lam": ("type", "body"), "forallE": ("type", "body"),
         "letE": ("type", "value", "body"), "proj": ("struct",), "mdata": ("expr",)}
def walk(root, seen_e, consts):
    st = [root]
    while st:
        e = st.pop()
        if e in seen_e or e not in E: continue
        seen_e.add(e); r = E[e]
        if "const" in r: consts.add(r["const"]["name"])
        for k, fields in CHILD.items():
            if k in r:
                for f in fields:
                    if f in r[k]: st.append(r[k][f])
        if "proj" in r and "typeName" in r["proj"]: consts.add(r["proj"]["typeName"])

wanted = {n for n, r in N.items() if nm(n) in set(want)}
missing = set(want) - {nm(n) for n in wanted}
if missing: sys.exit(f"not found: {missing}")
keep_decl, seen_e, todo = set(), set(), [byname[n] for n in wanted if n in byname]
while todo:
    di = todo.pop()
    if di in keep_decl: continue
    keep_decl.add(di)
    consts = set()
    for root in decls[di][2]: walk(root, seen_e, consts)
    for c in consts:
        if c in byname and byname[c] not in keep_decl: todo.append(byname[c])
keep_rec = {decls[di][0] for di in keep_decl}
with open(dst, "w") as out:
    for i, r in enumerate(recs):
        if ("ie" in r and r["ie"] not in seen_e): continue
        if decl_info(r) and i not in keep_rec: continue
        out.write(json.dumps(r, separators=(",", ":")) + "\n")
print(f"{len(keep_decl)} declarations, {len(seen_e)} expressions -> {dst}")
