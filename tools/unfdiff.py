#!/usr/bin/env python3
"""Join km's per-constant unfold counts with Lean's for one declaration.

    tools/unfdiff.py HIST.txt DIAG.txt DECLNAME

HIST.txt is tools/unfhist.py's output (counts by constant, km side) and
DIAG.txt the kdiag kernel's DIAG lines; DECLNAME selects Lean's row.
Prints Lean's time and totals, then the constants side by side.
"""
import sys, re
hist, diag, decl = sys.argv[1:4]
ours = {}
for l in open(hist):
    m = re.match(r'\s*(\d+)\s+(\S+)', l)
    if m and not l.startswith('total'): ours[m.group(2)] = int(m.group(1))
lean = None
for l in open(diag):
    if l.startswith('DIAG %s ' % decl):
        m = re.search(r'us=(\d+) unfolds=(\d+) top=(.*)', l); lean = m
if not lean: print('no DIAG row for', decl); sys.exit(1)
print('lean: %.1f ms, %s unfolds; ours: %d (top constants listed)' % (int(lean.group(1)) / 1000, lean.group(2), sum(ours.values())))
lt = dict((kv.rsplit(':', 1)[0], int(kv.rsplit(':', 1)[1])) for kv in lean.group(3).split(',') if ':' in kv)
print('%-70s %9s %9s' % ('constant', 'ours', 'lean(top6)'))
for k, v in sorted(ours.items(), key=lambda kv: -kv[1])[:30]:
    print('%-70s %9d %9s' % (k[-70:], v, lt.get(k, '')))
for k, v in lt.items():
    if k not in ours: print('%-70s %9s %9d' % (k[-70:], '', v))
