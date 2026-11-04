#!/usr/bin/env bash
# Build the DIAG kernel: the arena's official checker with Main.lean replaced
# by a replay that prints, per declaration Lean's kernel checks,
#     DIAG name us=<microseconds> unfolds=<n> top=c1:n1,...   (Kernel.Diagnostics)
#     tools/kdiag/build.sh OUTDIR   ->  OUTDIR/.lake/build/bin/kernel FILE.ndjson
# Ground truth for differential profiles (tools/funf.sh + tools/unfname.py).
set -euo pipefail
OUT="$1"
SRC="$HOME/.cache/lean-kernel-arena/arena/checkers/official"
rm -rf "${OUT:?}"; /bin/cp -Rf "$SRC" "$OUT"
/bin/cp -f "$(dirname "$0")/Main.lean" "$OUT/Main.lean"
cd "$OUT" && PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin:$PATH" lake build
