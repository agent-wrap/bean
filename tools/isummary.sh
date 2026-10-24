#!/bin/bash
# isummary.sh DIR -- verdicts, walls, RSS, VERD lines and the SLOW sum of an irange run
D=$1
for i in $(seq 1 14); do echo "slice $i: $(tail -1 $D/out_$i 2>/dev/null | cut -c1-50) | real $(grep real $D/err_$i | awk '{print $1}') | rss $(grep 'maximum resident' $D/err_$i | awk '{printf "%.1f", $1/1e9}') GB"; done
echo "VERD lines: $(grep -h '^VERD' $D/err_* | wc -l)"; grep -h '^VERD' $D/err_* | head -5
echo "SLOW sum: $(grep -h '^SLOW' $D/err_* | awk '{for(i=1;i<=NF;i++) if ($i ~ /^dt=/) {sub("dt=","",$i); s+=$i}} END{printf "%.0f", s}') s"
