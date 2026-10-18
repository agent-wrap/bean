#!/usr/bin/env python3
"""Check the Bend scanner's record-kind census against a Python one.

The Bend scanner (src/scan.bend) identifies a record's kind by a packed
signature of its first non-index top-level key. This recomputes the same thing
with a real JSON parser and diffs, line by line, so any disagreement names the
exact line it happens on.
"""
from __future__ import annotations

import json, subprocess, sys
from pathlib import Path

INDEX = {"in", "ie", "il"}


def pack(k: str) -> int:
    """Polynomial key hash, matching src/scan.bend.

    An earlier scheme packed the first two bytes and the length; it collided
    on numParams/numNested/numFields/numMinors, which an inductive
    declaration cannot be read without telling apart.
    """
    v = 0
    for c in k.encode():
        v = (v * 31 + c) & 0xFFFFFFFF
    return v


def expected(path: Path) -> list[int]:
    out = []
    for line in path.read_text().splitlines():
        if not line.strip():
            out.append(0)
            continue
        o = json.loads(line)
        kinds = [k for k in o if k not in INDEX]
        # The scanner takes the FIRST non-index key in serialised order.
        first = next((k for k in o.keys() if k not in INDEX), None)
        out.append(pack(first) if first else 0)
    return out


def main() -> int:
    binary, files = sys.argv[1], [Path(a) for a in sys.argv[2:]]
    bad = 0
    for f in files:
        want = expected(f)
        p = subprocess.run([binary, str(f)], capture_output=True)
        got = [int(x) for x in p.stdout.decode().split()]
        if got == want:
            print(f"  ok    {len(want):6} records  {f.name}")
            continue
        bad += 1
        print(f"  DIFF  {f}")
        print(f"        bend {len(got)} codes, python {len(want)}")
        for i, (g, w) in enumerate(zip(got, want)):
            if g != w:
                src = f.read_text().splitlines()[i]
                print(f"        line {i+1}: bend {g} python {w}\n          {src[:120]}")
                break
    print(f"\n{len(files) - bad}/{len(files)} files match")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
