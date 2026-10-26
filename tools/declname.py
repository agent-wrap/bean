#!/usr/bin/env python3
"""declname.py EXPORT.ndjson IDX [IDX...] -- the name of the declaration an
ftick/frange log index denotes: declaration records (axiom, def, thm,
opaque, quot, inductive) counted in file order from 0, the meta record
excluded (see memory: VERD index off by one)."""
import sys, json
KINDS = ("axiom", "def", "thm", "opaque", "quot", "inductive")
path = sys.argv[1]; want = {int(x) for x in sys.argv[2:]}
names = {0: ""}
def name(i):
    if i in names: return names[i]
    r = raw[i]; pre = name(r["pre"])
    s = r["str"] if "str" in r else str(r["i"])
    names[i] = (pre + "." + s) if pre else s
    return names[i]
raw = {}; ix = 0; hi = max(want)
with open(path) as f:
    for line in f:
        if line.startswith('{"in"'):
            r = json.loads(line); raw[r["in"]] = r["str"] if "str" in r else r["num"]
            continue
        k = line[2:line.index('"', 2)]
        if k in KINDS:
            if ix in want:
                r = json.loads(line)[k]
                if k == "inductive":
                    n = ", ".join(name(t["name"]) for t in r.get("types", r.get("ctors", []))[:3])
                else:
                    n = name(r["name"])
                print(ix, k, n)
            ix += 1
            if ix > hi: break
