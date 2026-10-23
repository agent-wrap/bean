#!/usr/bin/env bash
# Check one SLICE of a large export, in parallel with others:
#     tools/frange.sh OUT LO HI
# builds the ftick variant (SLOW/VERD/PROG log, see ftick.sh) whose fcheck
# checks only declarations with index in [LO, HI); the rest are trusted --
# still entering every table, as the checked ones see them. A full init
# VERD log as 14 slices runs in the time of the slowest slice.
set -euo pipefail
OUT="$1"; LO="$2"; HI="$3"
DIR="$(cd "$(dirname "$0")" && pwd)"
TMP="$(mktemp -d)"
/bin/cp -Rf "$DIR/../src" "$TMP/src"
python3 - "$TMP/src/fcheck.bend" "$LO" "$HI" <<'PY'
import sys
p, lo, hi = sys.argv[1:]; s = open(p).read()
a = "def krange_lo() -> U32:\n  0\n"; b = "def krange_hi() -> U32:\n  4294967295\n"
assert a in s and b in s, "krange_lo/hi moved"
s = s.replace(a, "def krange_lo() -> U32:\n  %d\n" % int(lo)).replace(b, "def krange_hi() -> U32:\n  %d\n" % int(hi))
open(p, "w").write(s)
PY
SRC="$TMP/src" exec "$DIR/ftick.sh" "$OUT"
