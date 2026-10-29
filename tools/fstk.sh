#!/usr/bin/env bash
# km continuation-stack sampler:
#     SRC=DIR RUNCAP=S [EVERY=16384] [DEPTH=10] tools/fstk.sh SLICE.ndjson > stacks.txt
# Builds fdbg from SRC (default src; a mkprobe copy restricts checking to one
# declaration), patches the generated C so that every EVERY-th km dispatch
# prints `STK f1 f2 ..`: the frames of the continuation stack, innermost
# first, skipping whnf/kernel-helper frames (W*, K*) after the first, DEPTH
# of them. Aggregate with `sort | uniq -c | sort -rn`. The stack is what a
# trail (fprobe TRAIL) cannot show: which comparison is WAITING on the work.
set -euo pipefail
SLICE="$1"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TMP="$(mktemp -d)"
"$ROOT/tools/bend.sh" "${SRC:-$ROOT/src}/fdbg.bend" -o "$TMP/gen.c"
python3 - "$TMP/gen.c" "${EVERY:-16384}" "${DEPTH:-10}" <<'PY'
import sys, re
p, every, depth = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
s = open(p).read()
cids = re.findall(r"#define (CID_[A-Z0-9_]+) (\d+)", s)
mx = max(int(v) for _, v in cids) + 1
names = ["?"] * mx
for nm_, v in cids: names[int(v)] = nm_[7:] if nm_.startswith("CID_KM_") else nm_[4:]
hdr = "static const char* stk_nm[%d] = {%s};\nstatic unsigned long long stk_n = 0;\n" % (mx, ",".join('"%s"' % x for x in names))
i = s.index("static void err_fail"); s = s[:i] + hdr + s[i:]
a = "  WL_CASE(FID_KM_KM)\n  {\n"
assert s.count(a) == 1
walk = r'''    if ((++stk_n %% %d) == 0) { Term _k = r1; int _d = 0, _first = 1; fprintf(stderr, "STK");
      while (_d < %d && term_aux(_k) == CID_KM_KCON) { u64 _l = term_peek(e.mem, _k); Term _f = e.mem[_l]; unsigned _c = (unsigned)term_aux(_f);
        const char* _n = _c < %d ? stk_nm[_c] : "?";
        if (_first || !(_n[0] == 'W' || _n[0] == 'K')) { fprintf(stderr, " %%s", _n); _d++; }
        _first = 0; _k = e.mem[_l + 1]; }
      fprintf(stderr, "\n"); }
''' % (every, depth, mx)
s = s.replace(a, a + walk)
open(p, "w").write(s)
PY
/nix/store/fy71z4s85kl6114vz7ksp3m5z4fz275k-clang-wrapper-21.1.8/bin/clang -O2 -o "$TMP/fdbg" "$TMP/gen.c" -lpthread 2>&1 | grep -i error | head -5 || true
timeout "${RUNCAP:-120}" "$TMP/fdbg" "$SLICE" 2>&1 >/dev/null | grep '^STK' || true
