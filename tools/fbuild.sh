#!/usr/bin/env bash
# Build a Bend file to a native binary, bypassing Apple clang 21.0.0, whose
# ARM64 backend crashes ("live register clobbered by inserted prologue
# instructions") on the kernel machine's generated C. Emits C with the pinned
# bend, compiles with the nix clang 21.1.8, where the bug is fixed.
set -euo pipefail
SRC="$1"; OUT="$2"
NIXCLANG=/nix/store/fy71z4s85kl6114vz7ksp3m5z4fz275k-clang-wrapper-21.1.8/bin/clang
TMP="$(mktemp -d)/gen.c"
"$(dirname "$0")/bend.sh" "$SRC" -o "$TMP"
exec "$NIXCLANG" -O2 -o "$OUT" "$TMP" -lpthread
