#!/usr/bin/env bash
# Sample the machine's used memory (GB: active + wired + compressor-held
# pages on macOS; MemTotal - MemAvailable on Linux) every second while a
# command runs; print the baseline, the peak and the peak over the baseline.
#     tools/memwatch.sh CMD ARGS...
set -uo pipefail
used() {
  if [[ -r /proc/meminfo ]]; then
    awk '/MemTotal/ {t=$2} /MemAvailable/ {a=$2} END {printf "%.2f", (t-a)/1048576}' /proc/meminfo
  else
    vm_stat | awk -v ps="$(pagesize)" '/Pages active/ {a=$3} /Pages wired/ {w=$4} /occupied by compressor/ {c=$5}
      END {gsub(/\./,"",a); gsub(/\./,"",w); gsub(/\./,"",c); printf "%.2f", (a+w+c)*ps/1e9}'
  fi
}
BASE=$(used); PEAK=$BASE
"$@" & PID=$!
while kill -0 "$PID" 2>/dev/null; do
  u=$(used); awk -v u="$u" -v p="$PEAK" 'BEGIN {exit !(u > p)}' && PEAK=$u
  sleep 1
done
wait "$PID"; RC=$?
echo "mem base=${BASE} peak=${PEAK} delta=$(awk -v a="$PEAK" -v b="$BASE" 'BEGIN {printf "%.2f", a-b}') GB rc=$RC" >&2
exit $RC
