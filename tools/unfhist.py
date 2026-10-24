#!/usr/bin/env python3
"""Per-declaration unfold histogram from a probe trace.

    tools/unfhist.py SLICE.ndjson TRC.txt [TOP]

TRC.txt holds `TRC x y` lines where x is a VALUE node index (the vi of
km's WDelGo arm, i.e. the export expression id of the constant's value).
Prints the constants whose values were unfolded (or attempted) most,
with counts -- the km side of a differential unfold profile against
kdiag's DIAG lines (tools/unfdiff.py joins the two).
"""
import json, sys, collections
src, trc = sys.argv[1:3]; top = int(sys.argv[3]) if len(sys.argv) > 3 else 25
names = {}; val2name = {}
def nm(i):
    r = names.get(i)
    if r is None: return ''
    pre, s = r; return (nm(pre) + '.' if pre else '') + str(s)
for line in open(src):
    if line.startswith('{"in":'):
        r = json.loads(line); k = 'str' if 'str' in r else 'num'
        names[r['in']] = (r[k]['pre'], r[k].get('str', r[k].get('i'))); continue
    for k in ('def', 'thm', 'opaque'):
        if line.startswith('{"%s":' % k):
            r = json.loads(line)[k]; val2name[r['value']] = nm(r['name']); break
cnt = collections.Counter()
for line in open(trc):
    p = line.split()
    if len(p) >= 2 and p[0] == 'TRC': cnt[int(p[1])] += 1
tot = sum(cnt.values()); print('total', tot, 'distinct', len(cnt))
for v, c in cnt.most_common(top):
    print('%9d  %s' % (c, val2name.get(v, 'node %d' % v)))
