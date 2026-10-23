#!/usr/bin/env bash
# Breadcrumb probe for the flat machine: record the FIRST (X, Y) pair of term
# indices seen when a given km arm runs, and print both terms.
#
#     tools/fprobe.sh SLICE.ndjson "    case 1n+p KCon{DSub{True{}, same, xi, yi, ctx, fu}, k}" xi yi [COND]
#
# COND (a Bend Bool over the arm's variables, default True{}) restricts the
# recording to the first time it holds, e.g. at IAp7 (an argument-type check's
# answer t): "Bool.not(L.tri_is_yes(t))" -- with X = ra, Y = I.all_dom(node).
#
# The arm is named by its first line, exactly as in src/km.bend; X and Y are
# U32 variables in scope there (bound before the arm's body). A copy of src
# gets `+px9 = X; +py9 = Y` after the arm header and threads them into the
# memo (keys 4294967288/7) the first time; fdbg dumps them and tools/fdump.py
# prints them. STORE=4 enlarges the store 4x (sdepth +2) so an overflowing
# declaration still dumps intact terms. Useful arms: DSub{True..} (depth
# budget exhausted), DCgS4{True..} (congruence bailed to the lazy probe),
# LZU{False{}, False{}..} (lazy probe stuck), IAp7 (an argument-type check).
# KEEP=1 stops rollbacks reusing the store (see below); with STORE=4 it keeps
# recorded terms intact. AFTER=TEXT inserts the probe below the arm's first line containing TEXT, so
# X/Y/COND can use the arm's rebound (+x2 = x) copies of its binders.
# Make slices with tools/extract.py.
set -euo pipefail
SLICE="$1"; ARM="$2"; X="$3"; Y="$4"; COND="${5:-}"
[[ -z "$COND" ]] && COND='True{}'
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TMP="$(mktemp -d)"
/bin/cp -Rf "${SRC:-$ROOT/src}" "$TMP/src"   # SRC=DIR probes a modified copy
if [[ "${STORE:-}" == "4" ]]; then
  sed -i '' "s/Nat.add(U32.log2((base + 2097152 : U32)), 2n)/Nat.add(U32.log2((base + 2097152 : U32)), 4n)/" "$TMP/src/km.bend"
fi
python3 - "$TMP/src/km.bend" "$ARM" "$X" "$Y" "$COND" <<'PY'
import sys
p, arm, x, y, cond = sys.argv[1:]; s = open(p).read()
s = s.replace("def krigid(", """def kpair_if(+c: Bool, +w: R.Tr<U32>, +x: U32, +y: U32) -> R.Tr<U32>:
  +w2 : R.Tr<U32> = w
  +had : Bool = Bool.not(U32.is_eq(R.get(U32, 64n, w2, 4294967288, 4294967295),
                                   4294967295))
  +keep : Bool = had || Bool.not(c)
  +ox : U32 = R.get(U32, 64n, w2, 4294967288, 4294967295)
  +oy : U32 = R.get(U32, 64n, w2, 4294967287, 4294967295)
  R.set(U32, 64n, R.set(U32, 64n, w2, 4294967288, S.pick(keep, ox, x),
                        4294967295),
        4294967287, S.pick(keep, oy, y), 4294967295)

def krigid(""", 1)
i = s.index(arm); j = s.index("\n", i) + 1
while not s[i:j].rstrip().endswith(":"):
    j2 = s.index("\n", j) + 1; i = j; j = j2
import os
after = os.environ.get("AFTER", "")
if after:                        # AFTER=TEXT: insert below the arm's first line containing TEXT
    j = s.index("\n", s.index(after, j)) + 1
s = s[:j] + "      +px9 : U32 = %s\n      +py9 : U32 = %s\n      +pc9 : Bool = %s\n" % (x, y, cond) + s[j:]
k = s.index("natn, wm, nt", j)
s = s[:k] + "natn, kpair_if(pc9, wm, px9, py9), nt" + s[k + len("natn, wm, nt"):]
# keep the probe's keys across KRb rollbacks (a recorded term allocated
# inside a rolled-back region may since have been overwritten)
old = "+s1 : R.Tr<U32> = snap"
assert old in s, "kflags_into changed: update fprobe.sh"
s = s.replace(old, "+s1 : R.Tr<U32> = kflag1(c2, 4294967288, kflag1(c2, 4294967287, snap))", 1)
# LAST=1 records the last pair the condition holds for, not the first
if os.environ.get("LAST") == "1":
    s = s.replace("+keep : Bool = had || Bool.not(c)", "+keep : Bool = Bool.not(c) && (had || True{})", 1)
# KEEP=1: rollbacks restore the memo but keep their allocations (no reuse,
# no compaction), so a pair recorded inside a rolled-back region stays intact
if os.environ.get("KEEP") == "1":
    old = "S.pick(roll, m2, n2)), msg), r2))"
    assert old in s, "KRb changed: update fprobe.sh"
    s = s.replace(old, "n2), msg), r2))", 1)
    s = s.replace("+comp : Bool = Bool.not(roll) && Bool.not(ovf)", "+comp : Bool = False{} && Bool.not(roll) && Bool.not(ovf)", 1)
open(p, "w").write(s)
PY
# DMP=N dumps terms N levels deep (default 400)
sed -i '' "s/dmp(400n/dmp(${DMP:-400}n/g" "$TMP/src/fdbg.bend"
if [[ "${TRACE:-}" == "1" ]]; then
  # TRACE=1: every recording (COND true) also prints "TRC x y" to stderr as
  # it happens -- all hits in order, rollbacks or not (with KEEP=1 the
  # indices stay valid for a later targeted probe of one pair)
  "$ROOT/tools/bend.sh" "$TMP/src/fdbg.bend" -o "$TMP/gen.c"
  python3 - "$TMP/gen.c" <<'PY2'
import sys, re
p = sys.argv[1]; s = open(p).read()
m = re.search(r"  WL_CASE\(FID_KM_KPAIR_IF\)\n  \{\n((?:    [^\n]*_0 = r\d+;\n)+)", s)
assert m, "kpair_if case not found"
regs = dict((v, r) for v, r in re.findall(r"(_\w+?_0) = (r\d+);", m.group(1)))
c = [v for v in regs if v.startswith("_c_")][0]; x = [v for v in regs if v.startswith("_x_")][0]; y = [v for v in regs if v.startswith("_y_")][0]
line = '    if (%s) fprintf(stderr, "TRC %%u %%u\\n", (unsigned)%s, (unsigned)%s);\n' % (
    "term_aux(%s) == CID_TRUE" % c if "Term %s" % c in m.group(1) else "%s" % c, x, y)
s = s[:m.end()] + line + s[m.end():]
open(p, "w").write(s)
PY2
  /nix/store/fy71z4s85kl6114vz7ksp3m5z4fz275k-clang-wrapper-21.1.8/bin/clang -O2 -o "$TMP/fdbg" "$TMP/gen.c" -lpthread 2>&1 | grep -i error | head -5 || true
else
"$ROOT/tools/fbuild.sh" "$TMP/src/fdbg.bend" "$TMP/fdbg" 2>&1 | grep -v '^$' | head -5 || true
fi
"$TMP/fdbg" "$SLICE" > "$TMP/dump.dbg"
python3 "$ROOT/tools/fdump.py" "$SLICE" "$TMP/dump.dbg" ""
