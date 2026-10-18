#!/usr/bin/env bash
# Wrapper for the pinned Bend toolchain. Strips the upgrade nag, which Bend
# prints to stderr on every run and which otherwise pollutes checker stderr.
set -euo pipefail
BEND="${BEND:-$HOME/.cache/bend2/result/bin/bend}"
if [[ ! -x "$BEND" ]]; then
  echo "bend not found at $BEND" >&2
  exit 127
fi
exec "$BEND" "$@" 2> >(grep -v 'is available: run bend update' >&2)
