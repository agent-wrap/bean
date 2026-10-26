#!/usr/bin/env bash
# Check an export with N worker processes: worker K checks the declarations
# whose index is K mod N and trusts the rest (fmain's argv[2], argv[3]);
# every declaration is checked by exactly one worker, so the join is the
# sequential verdict -- any reject -> reject (exit 1), else any decline or
# crash -> decline (exit 2), else accept (exit 0) -- in the wall time of the
# slowest share. N: $FBEAN_WORKERS, else 1 for a small export and the core
# count less two (at most 12) for a large one; each worker holds the whole
# store. FBEAN_KEEP=DIR keeps every worker's stderr (the logging build's
# SLOW/VERD lines) as DIR/err.K.
#     tools/fbean-par.sh EXPORT.ndjson
set -uo pipefail
IN="$1"
BIN="${FBEAN_BIN:-$(cd "$(dirname "$0")" && pwd)/../build/fbean-bin}"
CORES=$(sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 4)
SIZE=$(wc -c < "$IN" | tr -d " ")
if [[ -n "${FBEAN_WORKERS:-}" ]]; then N=$FBEAN_WORKERS
elif (( SIZE < 4000000 )); then N=1
else N=$(( CORES - 2 )); (( N > 12 )) && N=12; (( N < 1 )) && N=1
fi
# the workers' files: in FBEAN_KEEP when set (kept), else a temp dir
if [[ -n "${FBEAN_KEEP:-}" ]]; then TMP="$FBEAN_KEEP"; mkdir -p "$TMP"; /bin/rm -f "$TMP"/err.* "$TMP"/rc.* "$TMP"/out.*; CLEAN=0
else TMP=$(mktemp -d); CLEAN=1; fi
PIDS=()
trap 'kill "${PIDS[@]}" 2>/dev/null; (( CLEAN )) && /bin/rm -rf "$TMP"' EXIT
echo "workers=$N bin=$BIN" >"$TMP/run.txt"
for (( k=0; k<N; k++ )); do
  ( "$BIN" "$IN" "$k" "$N" >"$TMP/out.$k" 2>"$TMP/err.$k"; echo $? >"$TMP/rc.$k" ) &
  PIDS+=($!)
done
wait "${PIDS[@]}"
REJ=0; DEC=0; MSG=""
for (( k=0; k<N; k++ )); do
  rc=$(cat "$TMP/rc.$k" 2>/dev/null || echo 2)
  if (( rc == 1 )); then REJ=1; MSG=$(cat "$TMP/err.$k")
  elif (( rc != 0 )); then DEC=1; [[ -z "$MSG" ]] && MSG=$(cat "$TMP/err.$k"); fi
done
if (( REJ )); then echo "${MSG:-reject}" >&2; exit 1; fi
if (( DEC )); then echo "${MSG:-decline: not yet checkable by this kernel}" >&2; exit 2; fi
echo accept
exit 0
