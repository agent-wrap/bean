#!/bin/bash
# tools/sim16.sh OUT TEST...: run tests through the wrapper under the arena
# runner's budget (8 vCPU / 16 GB: FBEAN_MEM=13.6 GB, FBEAN_CORES=8) with the
# arena's timeouts, recording verdict, wall, workers and peak RSS per test.
# Time only on an idle machine.
T=$HOME/.cache/lean-kernel-arena/arena/_build/tests
OUT=$1; shift
lim() { case "$1" in init) echo 500;; std) echo 590;; cedar) echo 940;; con-leche) echo 720;;
  cslib) echo 1800;; navier-stokes-euler) echo 2400;; mathlib) echo 5680;; *) echo 600;; esac; }
for t in "$@"; do
  K="$OUT.$t.keep"; rm -rf "$K"
  s=$(date +%s)
  r=$(FBEAN_MEM=13600000000 FBEAN_CORES=8 FBEAN_KEEP="$K" timeout "$(lim "$t")" \
      "$(dirname "$0")/../build/fbean" "$T/$t.ndjson" 2>/dev/null | tail -1)
  echo "$t verdict=${r:-TIMEOUT} wall=$(( $(date +%s) - s ))s limit=$(lim "$t") $(head -1 "$K/run.txt" 2>/dev/null)" >> "$OUT"
done
