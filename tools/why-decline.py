#!/usr/bin/env python3
"""Group the declarations BEAN declines, across a corpus.

`build/icheck` prints one line per declaration -- verdict, name index, kind.
This resolves each name index to its dotted Lean name using the export's own
`in` records, then reports which declarations decline and how often.

A whole file declines if any one declaration does, so the arena's "declined"
tells you nothing about what is missing. This does.

    ./tools/bend.sh src/icheck.bend -o build/icheck
    python3 tools/why-decline.py ~/.cache/lean-kernel-arena/small/good/**/*.ndjson
"""
from __future__ import annotations

import collections
import json
import subprocess
import sys
from pathlib import Path

ICHECK = Path("build/icheck")


def names_of(path: Path) -> dict[int, str]:
    """index -> dotted name, from the export's `str`/`num` name records."""
    parts: dict[int, tuple[int, str]] = {}
    with path.open() as fh:
        for line in fh:
            line = line.strip()
            if not line or '"in"' not in line:
                continue
            try:
                rec = json.loads(line)
            except json.JSONDecodeError:
                continue
            ix = rec.get("in")
            if ix is None:
                continue
            if "str" in rec:
                parts[ix] = (rec["str"]["pre"], str(rec["str"]["str"]))
            elif "num" in rec:
                parts[ix] = (rec["num"]["pre"], str(rec["num"]["i"]))

    def resolve(ix: int, depth: int = 0) -> str:
        if ix == 0 or depth > 64:
            return ""
        if ix not in parts:
            return f"?{ix}"
        pre, comp = parts[ix]
        head = resolve(pre, depth + 1)
        return f"{head}.{comp}" if head else comp

    return {ix: resolve(ix) for ix in parts}


def main() -> int:
    if not ICHECK.exists():
        print(f"no {ICHECK}; build src/icheck.bend first", file=sys.stderr)
        return 2
    files = [Path(a) for a in sys.argv[1:]]
    if not files:
        print(__doc__)
        return 2

    per_name: collections.Counter[str] = collections.Counter()
    per_kind: collections.Counter[str] = collections.Counter()
    per_file: dict[str, list[str]] = {}
    totals = collections.Counter()

    for f in files:
        try:
            out = subprocess.run([str(ICHECK), str(f)], capture_output=True,
                                 text=True, timeout=120).stdout
        except subprocess.TimeoutExpired:
            totals["timeout"] += 1
            continue
        nm = names_of(f)
        bad = []
        for line in out.splitlines():
            bits = line.split()
            if len(bits) < 3:
                continue
            verdict, ix, kind = bits[0], int(bits[1]), bits[2]
            totals[verdict] += 1
            if verdict == "D":
                name = nm.get(ix, f"?{ix}")
                per_name[f"{kind} {name}"] += 1
                per_kind[kind] += 1
                bad.append(f"{kind} {name}")
        if bad:
            per_file[f.name] = bad

    print(f"declarations: {dict(totals)}")
    print(f"\ndeclining declarations by kind: {dict(per_kind)}")
    print(f"\ntop declining declarations ({len(per_name)} distinct):")
    for name, n in per_name.most_common(45):
        print(f"  {n:>4}  {name}")
    print(f"\nfiles with at least one declining declaration: {len(per_file)}")
    for fname, bad in sorted(per_file.items())[:25]:
        print(f"  {fname}: {', '.join(bad[:4])}" + (" ..." if len(bad) > 4 else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
