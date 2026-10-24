#!/bin/bash
# run1.sh BIN FILE [CAP] -- one verdict line with wall seconds (sequential use)
b=$1; f=$2; cap=${3:-600}
t0=$(perl -MTime::HiRes=time -e 'print time'); r=$(timeout $cap $b $f 2>&1 | tail -1); t1=$(perl -MTime::HiRes=time -e 'print time')
printf "%-40s %-8s %7.1f\n" "$(basename $f .ndjson)" "${r:-TIMEOUT}" $(echo "$t1 - $t0" | bc)
