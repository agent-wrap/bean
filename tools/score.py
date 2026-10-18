#!/usr/bin/env python3
"""Score bean against the local Lean Kernel Arena corpus.

Mirrors lka.py's semantics exactly (lka.py:1498-1525):
  exit 0 -> accepted, 1 -> rejected, 2 -> declined, else -> error;
  timeout -> error. Expected outcome 'either' is excluded from scoring.

Runs one test at a time: the arena's own perf numbers drift badly when heavy
tests overlap, which is how a prior run misread a 131 s test as a timeout.
"""
from __future__ import annotations

import argparse, json, os, subprocess, sys, time
from pathlib import Path

ARENA = Path(os.environ.get("ARENA", Path.home() / ".cache/lean-kernel-arena"))
RESULTS = ARENA / "results.json"


def locate(name: str) -> Path | None:
    for c in (ARENA / "arena/_build/tests" / f"{name}.ndjson",
              ARENA / "small/good" / f"{name}.ndjson",
              ARENA / "small/bad" / f"{name}.ndjson"):
        if c.exists():
            return c
    return None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--checker", default="build/bean")
    ap.add_argument("--filter", default="", help="substring match on test name")
    ap.add_argument("--max-size", type=float, default=0.0, help="skip inputs larger than N MB")
    ap.add_argument("--default-timeout", type=int, default=300,
                    help="limit for the 196 tests the arena gives none")
    ap.add_argument("--out", default="_results/score.json")
    args = ap.parse_args()

    meta = json.loads(RESULTS.read_text())
    tests = [t for t in meta["tests"] if args.filter in t["name"]]
    if args.max_size:
        tests = [t for t in tests if t["size"] <= args.max_size * 1e6]
    tests.sort(key=lambda t: t["size"])

    checker = Path(args.checker).resolve()
    if not checker.exists():
        print(f"no checker at {checker}", file=sys.stderr)
        return 127

    rows, missing = [], []
    for t in tests:
        path = locate(t["name"])
        if path is None:
            missing.append(t["name"])
            continue
        limit = t.get("timeout") or args.default_timeout
        t0 = time.monotonic()
        try:
            p = subprocess.run([str(checker), str(path)], capture_output=True, timeout=limit)
            code, timed_out = p.returncode, False
            err = p.stderr.decode(errors="replace")[-400:]
        except subprocess.TimeoutExpired:
            code, timed_out, err = None, True, ""
        wall = time.monotonic() - t0

        status = ("timeout" if timed_out else
                  {0: "accepted", 1: "rejected", 2: "declined"}.get(code, "error"))
        want = t["outcome"]
        if status == "declined":
            correctness = "declined"
        elif status in ("error", "timeout"):
            correctness = "error"
        elif want == "either":
            correctness = "either"
        elif (want == "accept") == (status == "accepted"):
            correctness = "correct"
        else:
            correctness = "incorrect"

        rows.append(dict(test=t["name"], size=t["size"], expected=want, status=status,
                         correctness=correctness, exit_code=code, wall=round(wall, 3),
                         limit=limit, stderr=err))
        mark = {"correct": "ok", "incorrect": "WRONG", "declined": "--",
                "error": "ERR", "either": "~"}[correctness]
        print(f"{mark:>5}  {wall:7.2f}s  {t['name']}"
              + (f"   [{status}, wanted {want}]" if correctness == "incorrect" else ""))

    tally: dict[str, int] = {}
    for r in rows:
        tally[r["correctness"]] = tally.get(r["correctness"], 0) + 1
    scorable = sum(1 for r in rows if r["expected"] != "either")
    rejects = [r for r in rows if r["expected"] == "reject"]

    print("\n" + "=" * 62)
    print(f"ran {len(rows)} of {len(tests)} tests" + (f", {len(missing)} missing" if missing else ""))
    print("  " + "  ".join(f"{k}={v}" for k, v in sorted(tally.items())))
    print(f"  score {tally.get('correct', 0)}/{scorable} scorable")
    print(f"  soundness: {sum(1 for r in rejects if r['correctness'] == 'correct')}"
          f"/{len(rejects)} reject-tests rejected")
    print(f"  WRONG: {tally.get('incorrect', 0)}  (a no-op scores 140/205; "
          f"only the reject column is real signal)")

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(dict(checker=str(checker), tally=tally, rows=rows), indent=1))
    print(f"  wrote {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
