#!/usr/bin/env python3
"""Make the arena's own grader see all 223 tests locally.

The arena clone has 27 tests built under `arena/_build/tests/`; the other 196
ship separately in the test tarball (unpacked at `small/{good,bad}/`). lka.py
discovers tests by globbing `_build/tests/**/*.stats.json`, so it only sees the
27 and `lka.py run` cannot reach the rest.

A test's `.stats.json` turns out to be byte-identical to its entry in
`results.json`, so the missing 196 can be reconstructed exactly and their
.ndjson symlinked into place. Each file's sha256 is checked against the
recorded digest, which also proves the local corpus is the same bytes the
official results were computed on -- without that, comparing a local score to
results.json would be meaningless.

Idempotent, additive, and it never overwrites a file the arena built itself.
"""
from __future__ import annotations

import hashlib, json, os, sys
from pathlib import Path

ARENA = Path(os.environ.get("ARENA", Path.home() / ".cache/lean-kernel-arena"))
BUILT = ARENA / "arena/_build/tests"


def sha256(p: Path) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()


def main() -> int:
    verify_all = "--verify-all" in sys.argv
    meta = json.loads((ARENA / "results.json").read_text())
    added = verified = bad = skipped = 0

    for t in meta["tests"]:
        name = t["name"]
        stats = BUILT / f"{name}.stats.json"
        nd = BUILT / f"{name}.ndjson"
        if stats.exists() and nd.exists():
            skipped += 1
            if verify_all and sha256(nd) != t["sha256"]:
                print(f"  DIGEST MISMATCH (arena-built) {name}")
                bad += 1
            continue

        src = next((p for p in (ARENA / "small/good" / f"{name}.ndjson",
                                ARENA / "small/bad" / f"{name}.ndjson") if p.exists()), None)
        if src is None:
            print(f"  no source for {name}")
            bad += 1
            continue

        got = sha256(src)
        if got != t["sha256"]:
            print(f"  DIGEST MISMATCH {name}\n    want {t['sha256']}\n    got  {got}")
            bad += 1
            continue
        verified += 1

        nd.parent.mkdir(parents=True, exist_ok=True)
        if not nd.exists():
            nd.symlink_to(src)
        if not stats.exists():
            stats.write_text(json.dumps(t, indent=2))
        added += 1

    print(f"\nlinked {added}, already built {skipped}, digests verified {verified}, problems {bad}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
