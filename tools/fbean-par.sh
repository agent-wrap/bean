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
else
  # memory-sized: a worker's RSS is ~1.9-2.1x its store (2.2 used), the store 2^(d+1)
  # slots of 64 B with d = floor(log2(nx + 2^22 + 2^21)) + 2 (km's sdepth,
  # nx the largest record index) -- init 6.7 GB,
  # std 8.1 GB, cedar 14, navier-stokes 28 measured; 12 std workers would
  # exceed the 96 GB machine. Budget 88 GB.
  # the store's size follows the largest record index (ids increase in
  # file order: read them from the tail), km's sdepth = log2(nx + 2^22 +
  # 2^21) + 2
  NX=$(tail -c 4000000 "$IN" | grep -o '"i[enl]":[0-9]*' | sed 's/.*://' | sort -n | tail -1); [[ -z "$NX" ]] && NX=$(( SIZE / 58 ))
  M=$(( NX + 1 + 4194304 + 2097152 )); D=0; while (( (1 << (D + 1)) <= M )); do D=$(( D + 1 )); done
  # km's sdepth: one doubling of room, two when that leaves under 2^24 free
  SD=$(( D + 2 )); (( (1 << (D + 1)) - M >= 16777216 )) && SD=$(( D + 1 ))
  # measured peak RSS / store: con-leche 1.82 (2^26 slots), navier-stokes
  # 2.1 (2^27): 2.0 up to 2^26 slots, 2.2 above. con-leche's wall time is
  # set by the worker count (8: 808 s, 9: 725-759, 10: 644, 11: 647; limit 720)
  # compact expression records (decode.bend RecK, 2026-10-29): a worker's
  # peak is its load's -- std 6.77 GB (1.58x, the whole run), navier-stokes
  # 14.5 GB (1.69x) -- so 1.7x up to 2^26 slots, 1.8x above
  RF=18; (( SD <= 25 )) && RF=17
  RSS=$(( (1 << (SD + 1)) * 64 * RF / 10 )); NM=$(( 88000000000 / RSS )); (( NM < 1 )) && NM=1
  N=$(( CORES - 2 )); (( N > 12 )) && N=12; (( N > NM )) && N=$NM; (( N < 1 )) && N=1
fi
# the workers' files: in FBEAN_KEEP when set (kept), else a temp dir
if [[ -n "${FBEAN_KEEP:-}" ]]; then TMP="$FBEAN_KEEP"; mkdir -p "$TMP"; /bin/rm -f "$TMP"/err.* "$TMP"/rc.* "$TMP"/out.*; CLEAN=0
else TMP=$(mktemp -d); CLEAN=1; fi
PIDS=()
trap 'kill "${PIDS[@]}" 2>/dev/null; (( CLEAN )) && /bin/rm -rf "$TMP"' EXIT
echo "workers=$N bin=$BIN" >"$TMP/run.txt"
# dynamic sharing (FBEAN_DYN=0 turns it off): the workers claim chunks of
# 256 declarations through files in CL -- each still walks every
# declaration, and checks the chunks it claimed first (fcheck FC.FL)
CL=()
if (( N >= 2 )) && [[ "${FBEAN_DYN:-1}" != "0" ]]; then
  /bin/rm -rf "$TMP/claims"; mkdir -p "$TMP/claims"; CL=("$TMP/claims")
fi
for (( k=0; k<N; k++ )); do
  ( "$BIN" "$IN" "$k" "$N" ${CL[@]+"${CL[@]}"} >"$TMP/out.$k" 2>"$TMP/err.$k"; echo $? >"$TMP/rc.$k" ) &
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
