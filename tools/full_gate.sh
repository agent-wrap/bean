#!/bin/bash
# tools/full_gate.sh BIN TAG [OUTDIR]: the commit gate for a candidate binary.
# Arena score directly and through the wrapper (4 workers), tools/regress.sh,
# then std/init/cedar through the wrapper, each capped at 2400 s so a hang is
# a reported timeout, not a stalled gate. Writes OUTDIR/fg_TAG.txt (default
# OUTDIR: $TMPDIR) and the two score.json copies next to it. Time only on an
# idle machine.
B="$1"; TAG="$2"; D="${3:-${TMPDIR:-/tmp}}"
cd "$(dirname "$0")/.."
T=~/.cache/lean-kernel-arena/arena/_build/tests
O=$D/fg_$TAG.txt; : >| "$O"
python3 tools/score.py --checker "$B" --max-size 20 2>&1 | tail -4 >> "$O"
/bin/cp -f _results/score.json "$D/score_${TAG}_d.json"
FBEAN_BIN=$B FBEAN_WORKERS=4 python3 tools/score.py --checker build/fbean --max-size 20 2>&1 | tail -4 >> "$O"
/bin/cp -f _results/score.json "$D/score_${TAG}_w.json"
tools/regress.sh "$B" 2>&1 | grep -vc "^ok" | sed 's/^/regress-not-ok: /' >> "$O"
for t in std init cedar; do
  r=$( { /usr/bin/time -p timeout 2400 env FBEAN_BIN="$B" build/fbean "$T/$t.ndjson" >/dev/null; echo "rc=$?"; } 2>&1 | tr '\n' ' ')
  echo "$t: $r" >> "$O"
done
echo fg-done >> "$O"
