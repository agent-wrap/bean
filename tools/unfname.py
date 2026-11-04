#!/usr/bin/env python3
"""unfname.py SLICE.ndjson ERR [DIAG.txt DECL] -- name tools/funf.sh's
`UNFC vi att real` lines (vi = a definition's value node) and print the top
constants by attempts; with kdiag's DIAG file and a declaration name, Lean's
unfold counts (its top 6) alongside."""
import json, sys, re
src, err = sys.argv[1:3]
raw = {}; val2name = {}; ndecl = 0; last = None
KINDS = ("axiom", "def", "thm", "opaque", "quot", "inductive")
recs = []
for line in open(src):
    r = json.loads(line)
    if 'in' in r and ('str' in r or 'num' in r):
        k = 'str' if 'str' in r else 'num'; raw[r['in']] = r[k]; continue
    for k in KINDS:
        if k in r: recs.append((k, r[k])); break
names = {0: ''}
def nm(i):
    if i in names: return names[i]
    r = raw[i]; pre = nm(r['pre']); s = r['str'] if 'str' in r else str(r['i'])
    names[i] = (pre + '.' + s) if pre else s; return names[i]
for k, r in recs:
    if k in ('def', 'thm', 'opaque') and isinstance(r, dict) and 'value' in r:
        val2name[r['value']] = nm(r['name'])
rows = []
for l in open(err):
    p = l.split()
    if len(p) == 4 and p[0] == 'UNFC': rows.append((int(p[2]), int(p[3]), int(p[1])))
ta = sum(r[0] for r in rows); tr = sum(r[1] for r in rows)
lt = {}
if len(sys.argv) > 4:
    for l in open(sys.argv[3]):
        if l.startswith('DIAG %s ' % sys.argv[4]):
            m = re.search(r'us=(\d+) unfolds=(\d+) top=(.*)', l)
            print('lean: %.1f ms, %s unfolds' % (int(m.group(1)) / 1000, m.group(2)))
            lt = dict((kv.rsplit(':', 1)[0], kv.rsplit(':', 1)[1]) for kv in m.group(3).split(',') if ':' in kv)
print('ours: attempts %d, real %d, distinct %d' % (ta, tr, len(rows)))
print('%-60s %10s %10s %8s' % ('constant', 'att', 'real', 'lean'))
for a, r, vi in sorted(rows, reverse=True)[:40]:
    n = val2name.get(vi, 'vi%d' % vi)
    print('%-60s %10d %10d %8s' % (n[-60:], a, r, lt.get(n, '')))
