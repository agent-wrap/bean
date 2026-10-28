#!/usr/bin/env bash
# Run the repo's own regression exports (tests/soundness must reject,
# tests/accept must accept) against a checker binary:
#     tools/regress.sh BIN
set -uo pipefail
BIN="$1"; ROOT="$(cd "$(dirname "$0")/.." && pwd)"; bad=0
for f in "$ROOT"/tests/soundness/*.ndjson; do
  out=$("$BIN" "$f" 2>&1 | tail -1)
  case "$out" in reject*) echo "ok      reject  $(basename "$f")";; *) echo "WRONG   $out  $(basename "$f")"; bad=1;; esac
done
for f in "$ROOT"/tests/accept/*.ndjson; do
  out=$("$BIN" "$f" 2>&1 | tail -1)
  case "$out" in accept*) echo "ok      accept  $(basename "$f")";; *) echo "FAIL    $out  $(basename "$f")"; bad=1;; esac
done
exit $bad
