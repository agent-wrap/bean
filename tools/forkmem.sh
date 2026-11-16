#!/usr/bin/env bash
# Fork-mode memory: run tools/fbean-par.sh with FBEAN_FORK=1 and, every
# STEP seconds, print the parent's resident and each worker's written
# (private) memory from vmmap -summary (macOS) or smaps_rollup (Linux); the
# machine's real use is about the parent's resident plus the workers' sum.
#     STEP=30 tools/forkmem.sh EXPORT.ndjson
set -uo pipefail
IN="$1"; STEP=${STEP:-30}
BINN=$(basename "${FBEAN_BIN:-fbean-bin}")
t0=$(date +%s)
FBEAN_FORK=1 "$(dirname "$0")/fbean-par.sh" "$IN" >/dev/null 2>&1 & W=$!
mem() {
  if [[ -r /proc/$1/smaps_rollup ]]; then
    awk '/^Rss/ {r=$2} /^Private_Dirty/ {p=$2} END {printf "res=%.2fG priv=%.2fG", r/1048576, p/1048576}' /proc/$1/smaps_rollup
  else
    vmmap -summary "$1" 2>/dev/null | awk '/^Writable regions/ {for (i=1;i<=NF;i++) {if ($i ~ /^written=/) w=$i; if ($i ~ /^resident=/) r=$i}} END {gsub(/\(.*/,"",w); gsub(/\(.*/,"",r); print r, w}'
  fi
}
while kill -0 $W 2>/dev/null; do
  sleep "$STEP"
  ps -axo pid,ppid,command | awk -v b="$BINN" '{n=split($3,a,"/"); if (a[n]==b) print $1, $2}' > /tmp/forkmem.$$ 2>/dev/null || true
  P=$(awk 'NR==1 {print $1}' /tmp/forkmem.$$ 2>/dev/null)
  [[ -z "$P" ]] && continue
  line="t=$(( $(date +%s) - t0 )) parent[$(mem "$P")]"
  for c in $(awk -v p="$P" '$2==p {print $1}' /tmp/forkmem.$$); do line="$line w[$(mem "$c")]"; done
  echo "$line"
done
wait $W; echo "rc=$? wall=$(( $(date +%s) - t0 ))s"
rm -f /tmp/forkmem.$$
