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
CORES=${FBEAN_CORES:-$(sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 4)}
SIZE=$(wc -c < "$IN" | tr -d " ")
# NX1: the largest record index + 1, read from the file's tail (ids grow in
# file order); fmain's 5th argument -- the store is allocated before decoding
# and the expressions go straight into it (0: the old path). FBEAN_STREAM=0
# turns it off.
NX1=0
if [[ "${FBEAN_STREAM:-1}" != "0" ]]; then
  NXT=$(tail -c 4000000 "$IN" | grep -o '"i[enl]":[0-9]*' | sed 's/.*://' | sort -n | tail -1)
  [[ -n "$NXT" ]] && NX1=$(( NXT + 1 ))
fi
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
  # km's sdepth: one doubling of room, two when that leaves under 2^21 free
  SD=$(( D + 2 )); (( (1 << (D + 1)) - M >= 2097152 )) && SD=$(( D + 1 ))
  # con-leche's wall time is set by the worker count (8: 808 s, 9: 725-759,
  # 10: 644, 11: 647; limit 720)
  # the budget: FBEAN_MEM bytes, else 85% of the machine's RAM (the arena's
  # runner has 16 GB; this machine 96 GB, of which 88 GB was the old fixed
  # budget)
  MEMB=$(sysctl -n hw.memsize 2>/dev/null || awk '/MemTotal/ {print $2 * 1024}' /proc/meminfo 2>/dev/null || echo 16000000000)
  BUDGET=${FBEAN_MEM:-$(( MEMB * 85 / 100 ))}
  # all-U32 expression nodes (2026-11-07): a store slot is 32 B; the rest
  # of a worker's peak (kept records, the structural checks' closure trie,
  # decode) ~1 GB + 45 B a record -- single-worker peaks std 3.51 GB (store
  # 2.15), cslib 6.89 (store 4.29); the per-record term capped at cslib's
  # 40M records (mathlib's 105M: a measured 10.25 GB, store 8.59); 10% margin
  NXC=$NX; (( NXC > 40000000 )) && NXC=40000000
  RSS=$(( ((1 << (SD + 1)) * 32 + 1000000000 + NXC * 45) * 11 / 10 )); NM=$(( BUDGET / RSS )); (( NM < 1 )) && NM=1
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
  ( "$BIN" "$IN" "$k" "$N" "${CL[0]:-}" "$NX1" >"$TMP/out.$k" 2>"$TMP/err.$k"; echo $? >"$TMP/rc.$k" ) &
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
