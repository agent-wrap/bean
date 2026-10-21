#!/usr/bin/env bash
# Breadcrumb probe for the flat machine: record the FIRST (X, Y) pair of term
# indices seen when a given km arm runs, and print both terms.
#
#     tools/fprobe.sh SLICE.ndjson "    case 1n+p KCon{DSub{True{}, same, xi, yi, ctx, fu}, k}" xi yi
#
# The arm is named by its first line, exactly as in src/km.bend; X and Y are
# U32 variables in scope there (bound before the arm's body). A copy of src
# gets `+px9 = X; +py9 = Y` after the arm header and threads them into the
# memo (keys 4294967288/7) the first time; fdbg dumps them and tools/fdump.py
# prints them. STORE=4 enlarges the store 4x (sdepth +2) so an overflowing
# declaration still dumps intact terms. Useful arms: DSub{True..} (depth
# budget exhausted), DCgS4{True..} (congruence bailed to the lazy probe),
# LZU{False{}, False{}..} (lazy probe stuck), IAp7 (an argument-type check).
# Make slices with tools/extract.py.
set -euo pipefail
SLICE="$1"; ARM="$2"; X="$3"; Y="$4"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TMP="$(mktemp -d)"
/bin/cp -Rf "$ROOT/src" "$TMP/src"
if [[ "${STORE:-}" == "4" ]]; then
  sed -i '' "s/Nat.add(U32.log2((base + 2097152 : U32)), 2n)/Nat.add(U32.log2((base + 2097152 : U32)), 4n)/" "$TMP/src/km.bend"
fi
python3 - "$TMP/src/km.bend" "$ARM" "$X" "$Y" <<'PY'
import sys
p, arm, x, y = sys.argv[1:]; s = open(p).read()
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
s = s[:j] + "      +px9 : U32 = %s\n      +py9 : U32 = %s\n" % (x, y) + s[j:]
k = s.index("natn, wm, nt", j)
s = s[:k] + "natn, kpair_if(True{}, wm, px9, py9), nt" + s[k + len("natn, wm, nt"):]
open(p, "w").write(s)
PY
"$ROOT/tools/fbuild.sh" "$TMP/src/fdbg.bend" "$TMP/fdbg" 2>&1 | grep -v '^$' | head -5 || true
"$TMP/fdbg" "$SLICE" > "$TMP/dump.dbg"
python3 "$ROOT/tools/fdump.py" "$SLICE" "$TMP/dump.dbg" ""
