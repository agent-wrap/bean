# bean

A Lean 4 kernel type checker written in [Bend 2](https://bend-lang.org). It
reads a `lean4export` 3.1.0 file (Lean 4.34.1) and answers accept, reject or
decline, under the [Lean Kernel Arena](https://arena.lean-lang.org)'s
exit-code contract. Toolchain: Bend 2.0.36.

## Why Bend

Bend is a total functional language whose own kernel, BendTT, is proven in Lean
(`bend2/bendtt.lean`, shipped with the toolchain). `bend --verdict` rechecks a
program with that proven kernel. A checker written in Bend with no `@unsafe`
definitions inherits a machine-checked guarantee for free, where
[con-leche](https://github.com/leanprover/con-leche) earned a far stronger one
by hand.

The invariant, enforced by `tools/invariants.sh`: **zero `@unsafe` defs, and
`bend --verdict` accepts every module.** Where it stands today:

- Every checking module (`km`, `fcheck`, `fstore`, `level`, `check`,
  `nested`, `recursor`, ...) has no `@unsafe` and passes `--verdict`.
- `src/fmain.bend` does not, since fork mode. Bend cannot fork a process, so
  `Fork.workers` is a foreign effect: `src/fork.c` (about 100 lines: fork N
  children, reset the runtime's thread pool in each, wait for them, join
  their exit codes) and `src/fork.js` (a one-line stub for the JS target,
  which never forks). `bend --verdict` proves only code with no foreign
  implementation in it, so it flags `Fork.workers` and the nine definitions
  on the path from `main` to it. The checking logic is unaffected; the C
  decides which worker checks which declaration and ANDs the answers, and
  cannot make a wrong declaration accepted. The pre-fork entry (commit
  `675ed7c`) passed.

  Why we took that trade: the arena's runner has 16 GB. Without fork, each
  worker loads its own copy of the export, which on 16 GB leaves room for
  one worker, and cslib and navier-stokes then exceed their time limits.
  Forked workers share the loaded export copy-on-write (cslib: six workers
  in ~8.7 GB against ~41 GB separate). `FBEAN_FORK=0` runs the same binary without
  ever calling the fork; a binary that passes `--verdict` is the one built
  from the pre-fork entry.
- `src/dcheck.bend`, a debug printer, fails `--verdict` on a stale `match`.

## Status

**Zero wrong answers is the rule every commit is gated on.** An undecided
comparison is a decline, never a guess. Every WRONG during development was
the same mistake: answering on insufficient evidence.

On the arena's corpus up to 20 MB, scored by `tools/score.py`, which mirrors
`lka.py`'s semantics (`tools/full_gate.sh`):

    198/198 scorable tests correct        (197 when the machine is loaded: see n36 below)
    soundness 71/71 reject-tests rejected
    WRONG 0

Eighteen tests are marked `either` by the arena (Lean's own developers have
not settled the answer) and are excluded from the score. bean answers 16 and
declines 2: `corner-cases/eta-rule-k` (function eta through a recursor with
rule K, [lean4#12520](https://github.com/leanprover/lean4/issues/12520)) and
`corner-cases/proj-maybe-prop` (projection out of a structure whose sort is a
bare universe parameter,
[lean4#7637](https://github.com/leanprover/lean4/issues/7637)).

The seven large exports all accept on the development machine (96 GB, Apple
M-series), through the worker wrapper `tools/fbean-par.sh`:

| export | arena limit | last measured here |
|---|---|---|
| init | 500 s | 64-70 s |
| std | 590 s | 112-143 s |
| cedar | 940 s | 166-181 s |
| con-leche | 720 s | accepts |
| cslib | 1800 s | 994 s, 6 forked workers, loaded machine |
| navier-stokes | 2400 s | 1899 s (2026-11-03) |
| mathlib | 5680 s | 3936 s, 6 workers, ~10 GB a worker |

What has **not** been shown: a run on the arena's own runner (8 vCPU, 16 GB,
Linux). `tools/sim16.sh` simulates its budget locally; under it every export
but mathlib fits (cslib peaks near 8.7 GB with six forked workers), mathlib
does not (one process loading it holds ~10 GB), and `perf/magma-list-deep-n36`
runs at 359-391 s against a 390 s limit, so it fails whenever the machine is
busy. The arena entry `arena/bend-kernel.yaml` builds on Linux with the
runner's `cc`; that build has been dry-run on macOS only.

## Design

Bend forbids mutual recursion, requires every recursion to terminate, has no
mutable state, and will not let `match` scrutinise a computed value. The usual
mutually recursive `whnf`/`infer`/`isDefEq` cluster is therefore one
fuel-indexed abstract machine (`src/km.bend`) running over a **flat store**: a
hash-consed node array threaded linearly through the machine, so updates are
in place (Bend stores `Array<T.Ex>` unboxed, 64 B a slot). Regions of the
store are rolled back when a sub-computation's result is no longer needed, and
the whnf, inference and defeq memos live in the store beside the nodes.

The definitional-equality loop follows the reference kernel
(`docs/spec/type_checker.cpp`): lazy delta reduction by definition height, the
failure cache, proof irrelevance, eta and structure eta, `Nat`/`String`
literal extensions, quotients, and iota reduction for nested and mutual
inductives. Inductive declarations are validated, and recursor data is
**derived** and compared with the export's claim rather than trusted; the
format spec says it is redundant, and `bugs/rec-k-lie` is an export that lies
about a recursor to prove `False`. Two things the port learned the hard way,
both of them Lean's behaviour: memo keys must cover only the context a term
actually refers to (free-variable masks; keying on the whole context made
mathlib declarations enter millions of defeq pairs), and the hash-cons scan
must survive the tombstones that rollbacks leave behind.

**Workers.** A large export is checked by N processes, worker K taking the
declarations with index K mod N and trusting the rest; the join is the
sequential verdict (any reject, else any decline or crash, else accept).
In fork mode one process loads the export and builds the shared tables, then
forks the workers, which share all of it copy-on-write: a worker writes
0.3-0.6 GB of its own. `tools/fbean-par.sh` sizes N from the cores and the
memory budget.

## Layout

    src/fmain.bend         entry point; arena exit-code contract; fork mode
    src/fork.c, fork.js    the Fork.workers effect (C; the JS stub never forks)
    src/fcheck.bend        declaration checking on the flat store
    src/km.bend            the kernel machine: whnf, infer, defeq
    src/fstore.bend        the flat store
    src/level.bend         universe levels in normal form
    src/check.bend         inductive declarations, recursors, projections
    src/nested.bend        recursors of mutual and nested blocks, derived
    src/scan.bend, decode.bend   the NDJSON scanner and record decoder
    src/main.bend ...      the earlier trie-based checker, kept as an oracle
    src/fdbg, fdiff, fsdiff, fckdiff, tdbg, dcheck, icheck, census
                           debug entries and differential checks, not the checker
    tests/                 regression exports beyond the arena's suite (tests/README.md)
    bench/                 micro-benchmarks behind the design decisions
    docs/                  design notes, measurements, dead ends (see below)
    arena/bend-kernel.yaml the arena checker definition

## Build and score

    ./tools/invariants.sh                        # the project invariant (see above)
    ./tools/bend.sh src/fmain.bend --check-only  # types and termination
    ./tools/fbuild.sh src/fmain.bend build/fbean-bin
    cp tools/fbean-par.sh build/fbean            # the arena runs this wrapper

On Linux, `bend src/fmain.bend -o fbean.c && cc -O2 -o fbean-bin fbean.c
-lpthread` is enough (that is what `arena/bend-kernel.yaml` does). On macOS
`tools/fbuild.sh` compiles with a nix clang 21.1.8 because Apple clang 21.0.0's
ARM64 backend crashes on the generated C; edit the path at the top of the
script.

    python3 tools/arena-link.py                  # once: expose the arena tests to lka.py
    python3 tools/score.py --checker build/fbean --max-size 20
    tools/regress.sh build/fbean-bin
    tools/full_gate.sh build/fbean-bin TAG       # the commit gate: score, wrapper, regress, init/std/cedar

    cd ~/.cache/lean-kernel-arena/arena          # the authoritative grader
    uv run lka.py run --checker bend-kernel --test 'bugs/*'

Never time two runs at once: the Bend runtime's workers spin, and a background
run produces phantom timeouts.

## Tools

Everything that found a bug or a slowdown is in `tools/`, each with a usage
comment at the top.

- **Scoring and gating:** `score.py`, `full_gate.sh`, `regress.sh`,
  `fbean-par.sh`, `sim16.sh` (the 16 GB runner's budget), `forkmem.sh` and
  `memwatch.sh` (memory), `run1.sh`.
- **Build variants of the checker** that count or sample instead of just
  answering: `ftick.sh` (per-declaration time), `funf.sh` (delta unfolds per
  constant), `fkey.sh` (memo-key counts), `fcount.sh`, `farms.sh`,
  `fprof.sh`, `fstk.sh` (continuation-stack sampler), `fprobe.sh` /
  `fterm.sh` (dump the two terms at a chosen defeq).
- **Against the real kernel:** `tools/kdiag` is a small Lean program that
  prints the official kernel's unfold counts and defeq traces for one
  declaration; `unfdiff.py`, `unfhist.py` and `unfname.py` join them with
  bean's. Comparing counts, not seconds, is how algorithmic divergence was
  told apart from Bend's constant factor.
- **Cutting exports down:** `extract.py` and `slice.py` (dependency-closed
  slices, the latter renumbered for mathlib-size files), `shrink.py`
  (delta-debugging), `decl_show.py`, `declname.py`, `why-decline.py`.
- **Checking the checker's pieces:** `recref.py` (a reference recursor
  derivation), `decode-check.py`, `census-check.py`, `closure.py`.

## Dead ends

Kept so nobody repeats them; the measurements are in `docs/measurements.md`
and `docs/defeq-port.md`.

- **Closed locals** (opening binders eagerly as free variables): one
  declaration went 480 s to 19 s, but `perf/app-lam` and `perf/fueled-chain`
  timed out and the caches lost cross-depth sharing. Not merged
  (`docs/defeq-port.md`, "Closed locals").
- **A compact store** (4 field words plus packed tags, 16.5 B a slot instead
  of 64) halved memory and made `magma-list-deep-n36` 1.8x slower (686-696 s
  against 376-390). mathlib on 16 GB needs a smaller store, but not at the
  price of the hot path. Not in the docs; the patch was not kept.
- **Args-first comparison for projection functions** everywhere: a 25x
  blowup on mathlib; it survives only for projection-function abbrevs.
- **Cheap-first ordering** of the comparison hangs std; Lean's order stays.
- **Rebuilding the hash-cons table** after rollbacks instead of scanning
  past tombstones: slower or still declining.
- **A radix-4 trie** and **cross-declaration whnf-memo threading**, from the
  trie-based era: measured, no help, reverted.
- The trie-based checker itself (`src/main.bend`): correct, but its store
  could not be updated in place; it remains as a differential oracle.

## Limitations

- mathlib does not fit the arena's 16 GB; `magma-list-deep-n36` has almost
  no margin under its 390 s limit; neither has run on the arena's Linux
  runner.
- Fork mode is foreign code, so the entry module no longer passes
  `bend --verdict`: the proven-kernel guarantee covers the checker, not the
  process plumbing (see Why Bend). `FBEAN_FORK=0` runs separate processes
  with the same binary; only the pre-fork entry builds a binary that
  passes, and either way far fewer workers fit in 16 GB.
- Fuel: the machine is fuel-indexed to satisfy Bend's termination checker. A
  declaration that exhausts fuel declines, never rejects, but it is a
  decline Lean would not give.
- Two `either` corner cases decline rather than pick a side.
- The arena's exit-code contract is unforgiving: a runtime abort exits 1,
  which it reads as *reject*. `fmain` maps I/O failure to 3; nothing else
  may exit 1 without having proven the export wrong.

## Next steps, and where help is welcome

1. **A real run on a 16 GB Linux box**, with `tools/sim16.sh`'s settings.
   This is the single largest unknown.
2. **mathlib in 16 GB.** The store is 64 B a slot because Bend sizes an
   unboxed array element for the largest constructor. A narrower `T.Ex`, or
   a two-array layout that keeps the hot hash-cons probe unboxed, is the
   lever; the compact-store attempt above shows the constraint.
3. **Fork mode inside the invariant.** Either a Bend-level way to express
   it, or a build that proves the fork-free entry and ships the forking one.
4. **`eta-rule-k` and `proj-maybe-prop`**: a decision, once Lean settles.
5. **Speed.** The arena's limits sit at roughly 15x the official kernel.
   On init bean takes 64 s with eight workers where the official kernel takes
   33 s on one core; on single declarations the gap has been 100x before a
   fix and the differential tooling in `tools/` is set up for finding the
   next one.

Issues and pull requests are welcome; a reproducible export (see
`tools/extract.py`) is the most useful thing to attach.

## How this is judged

1. **The arena's own harness.** `lka.py run --checker bend-kernel`, diffed
   against the checkers in `results.json` that score 205/205.
2. **The reference kernel as a differential oracle.** Unfold counts and
   pair-by-pair traces against the official Lean kernel.
3. **`bend --verdict`** and zero `@unsafe` definitions.
4. **Soundness first.** The 71 `reject` tests and the `bugs/` regressions
   are reported separately from the accept score, and a commit that loses
   one is not made.
