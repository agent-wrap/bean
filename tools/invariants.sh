#!/usr/bin/env bash
# The project invariant: no @unsafe definitions anywhere, and the whole thing
# accepted by BendTT's Lean-proven kernel. Losing either forfeits the only
# reason to write this checker in Bend. Comments are excluded so that a note
# naming the invariant does not trip it.
set -uo pipefail
cd "$(dirname "$0")/.."
fail=0
n=$(grep -v '^\s*#' src/*.bend | grep -c '@unsafe' || true)
if [[ "$n" -ne 0 ]]; then echo "FAIL: $n @unsafe definitions"; fail=1
else echo "ok: no @unsafe definitions"; fi
for f in src/*.bend; do
  if ! ./tools/bend.sh "$f" --verdict 2>&1 | grep -q 'ALL PROOFS CHECK'; then
    echo "FAIL: --verdict rejected $f"; fail=1
  fi
done
[[ "$fail" -eq 0 ]] && echo "ok: bend --verdict accepts every module"
exit "$fail"
