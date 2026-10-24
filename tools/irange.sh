#!/bin/bash
# irange.sh TAG [OUTDIR] -- build 14 range binaries from the current src and
# check init in parallel slices (one launcher tree only; ~6.5 GB RSS each).
# Writes OUTDIR/TAG/{bin_i,out_i,err_i} and OUTDIR/TAG/done at the end.
cd "$(dirname "$0")/.."
TAG=$1; OUT=${2:-build/irange}; D=$OUT/$TAG; mkdir -p $D; /bin/rm -f $D/done
INIT=$HOME/.cache/lean-kernel-arena/arena/_build/tests/init.ndjson
B="0 2000 3500 4000 4500 5500 6500 7500 8500 10000 13000 18000 28000 40000 60000"
set -- $B; prev=$1; shift; i=0
for hi in "$@"; do
  lo=$prev; prev=$hi; i=$((i+1))
  ( tools/frange.sh $D/bin_$i $lo $hi >/dev/null 2>&1 && timeout ${CAP:-14400} /usr/bin/time -l $D/bin_$i $INIT > $D/out_$i 2> $D/err_$i ) &
done
wait
echo ALLDONE > $D/done
