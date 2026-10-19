#!/usr/bin/env python3
"""Delta-debug an export file against a predicate on icheck's output.

Repeatedly removes chunks of declaration lines (never name/level/expression
lines, which later records reference by index) while the predicate holds,
then prints the minimised file. The predicate here: the debug icheck still
reports `R <ix> thm` for the named declaration index -- i.e. the wrong
rejection still happens.

Built to localise the magma-list-pair wrong reject: 600 KB is unreadable,
and gate-and-rebuild bisection dead-ended because at least two deep denials
only misfire in combination. A file small enough to read settles it.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ICHECK = Path("build/icheck_dbg")


def holds(lines: list[str], marker: str, tmp: Path) -> bool:
    tmp.write_text("\n".join(lines) + "\n")
    try:
        out = subprocess.run([str(ICHECK), str(tmp)], capture_output=True,
                             text=True, timeout=240).stdout
    except subprocess.TimeoutExpired:
        return False
    return marker in out


def main() -> int:
    src, marker, out_path = sys.argv[1], sys.argv[2], Path(sys.argv[3])
    lines = [l for l in Path(src).read_text().splitlines() if l.strip()]
    tmp = out_path.with_suffix(".try.ndjson")

    # only declaration lines are candidates for removal
    def is_decl(l: str) -> bool:
        return any(k in l[:14] for k in ('"def"', '"thm"', '"axiom"',
                                         '"inductive"', '"opaque"', '"quot"'))

    assert holds(lines, marker, tmp), "predicate does not hold on the input"
    chunk = max(1, len(lines) // 4)
    while chunk >= 1:
        i = 0
        removed_any = False
        while i < len(lines):
            cand_idx = [j for j in range(i, min(i + chunk, len(lines)))
                        if is_decl(lines[j])]
            if cand_idx:
                trial = [l for j, l in enumerate(lines) if j not in set(cand_idx)]
                if holds(trial, marker, tmp):
                    lines = trial
                    removed_any = True
                    continue  # same i: indices shifted
            i += chunk
        print(f"chunk {chunk}: {len(lines)} lines", flush=True)
        if chunk == 1 and not removed_any:
            break
        chunk = max(1, chunk // 2) if chunk > 1 else (1 if removed_any else 0)
        if chunk == 0:
            break
    out_path.write_text("\n".join(lines) + "\n")
    print(f"minimised to {len(lines)} lines -> {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
