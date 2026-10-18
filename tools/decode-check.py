#!/usr/bin/env python3
"""Check the Bend decoder's extracted fields against a real JSON parser.

For each record the Bend decoder emits
    <kind> <index> <bi1> <bi2> |<payload>| <int fields...>
where the int fields are every integer and every boolean (as 1/0) in
serialisation order except the one belonging to the index key, the payload is the value of `str`/`natVal`/
`strVal`, and bi1/bi2 are the first two bytes of `binderInfo`.

This recomputes all of it from the parsed JSON and diffs record by record, so
a disagreement names the exact line.
"""
from __future__ import annotations

import json, subprocess, sys
from pathlib import Path

INDEX = {"in", "ie", "il"}
STRKEYS = {"str", "natVal", "strVal"}


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


def walk(o, key, ints, payload, bi, ctr, ob):
    """Collect (key hash, integer, object ordinal) in serialisation order.

    Attributed by key, not by position: 26 records in the small corpus
    serialise a binder as name, type, body, binderInfo rather than in
    alphabetical order, so position is not a reliable field identifier.

    The object ordinal is assigned in document order, one per `{`, which is
    what src/scan.bend does while scanning the bytes. It is needed because an
    `inductive` record nests arrays of objects that all repeat the same keys.
    """
    if isinstance(o, bool):
        # Booleans are recorded as 1/0 under their own key, in serialisation
        # order, exactly as the Bend decoder does. `k` on a recursor is one
        # of them and the kernel has to check that claim, so it is no longer
        # dropped.
        ints.append((pack(key), 1 if o else 0, ob))
        return
    if False:
        return
    if isinstance(o, int):
        if key not in INDEX:
            ints.append((pack(key), o, ob))
        return
    if isinstance(o, str):
        if key in STRKEYS:
            payload.append(o)
        if key == "binderInfo":
            bi.append(o)
        return
    if isinstance(o, list):
        for v in o:
            walk(v, key, ints, payload, bi, ctr, ob)
        return
    if isinstance(o, dict):
        mine = ctr[0]
        ctr[0] += 1
        for k, v in o.items():
            walk(v, k, ints, payload, bi, ctr, mine)


def expected(path: Path) -> list[str]:
    out = []
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        o = json.loads(line)
        first = next((k for k in o if k not in INDEX), None)
        kind = pack(first) if first else 0
        ix = next((o[k] for k in o if k in INDEX), 0)
        ints: list[int] = []
        payload: list[str] = []
        bi: list[str] = []
        walk(o, None, ints, payload, bi, [0], 0)
        b = bi[0] if bi else ""
        b1 = ord(b[0]) if len(b) > 0 else 0
        b2 = ord(b[1]) if len(b) > 1 else 0
        # Bend prints the payload as byte values, so compare UTF-8 bytes.
        pay = "".join(f" {b}" for b in "".join(payload).encode("utf-8"))
        out.append(f"{kind} {ix} {b1} {b2} |{pay} |"
                   + "".join(f" {g}:{v}@{ob}" for g, v, ob in ints))
    return out


def main() -> int:
    binary, files = sys.argv[1], [Path(a) for a in sys.argv[2:]]
    bad = 0
    for f in files:
        want = expected(f)
        p = subprocess.run([binary, str(f)], capture_output=True)
        got = [l for l in p.stdout.decode().split("\n") if l.strip()]
        if got == want:
            print(f"  ok    {len(want):6} records  {f.name}")
            continue
        bad += 1
        print(f"  DIFF  {f}   bend {len(got)} / python {len(want)}")
        for i, (g, w) in enumerate(zip(got, want)):
            if g != w:
                src = [l for l in f.read_text().splitlines() if l.strip()][i]
                print(f"        record {i+1}\n          bend   {g}\n"
                      f"          python {w}\n          src    {src[:160]}")
                break
    print(f"\n{len(files) - bad}/{len(files)} files match")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
