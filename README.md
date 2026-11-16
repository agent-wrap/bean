# bean

A Lean 4 kernel type checker written in [Bend 2](https://bend-lang.org), graded
by the [Lean Kernel Arena](https://arena.lean-lang.org).

## Why Bend

Bend is a total functional language whose own kernel, BendTT, is proven in Lean
(`bend2/bendtt.lean`, shipped with the toolchain). `bend --verdict` rechecks a
program with that proven kernel. A checker written in Bend with no `@unsafe`
definitions therefore inherits a machine-checked guarantee for free, where
[con-leche](https://github.com/leanprover/con-leche) earned a far stronger one
by hand.

Keeping that guarantee is the point of the project, so it is an invariant, not
a goal: **zero `@unsafe` defs, and `bend --verdict` must pass.**

## Status

Work in progress. On the arena's corpus up to 20 MB
(`tools/score.py --max-size 20`):

    198/198 scorable tests correct
    soundness 71/71 reject-tests rejected
    WRONG 0

The large exports are the open front, and they are bounded by time, not by
correctness: `init`, `std` and `cedar` are accepted; `navier-stokes`, `cslib`
and `mathlib` still decline or exceed the time limit.

**Zero wrong answers is the rule every commit is gated on.** Every violation
during development has been the same mistake -- answering on insufficient
evidence -- so an undecided comparison is a decline, never a guess.

## Design

Bend forbids mutual recursion, requires every recursion to terminate, has no
mutable state, and will not let `match` scrutinise a computed value. The usual
mutually recursive `whnf`/`infer`/`isDefEq` cluster is therefore one
fuel-indexed abstract machine (`src/km.bend`) running over a **flat store**: a
hash-consed node array threaded linearly through the machine, so updates are
in place. Regions of the store are rolled back or compacted when a
sub-computation's result is no longer needed, and whnf, inference and
unfolding memos live in the store beside the nodes.

The definitional-equality loop follows the reference kernel
(`type_checker.cpp`): lazy delta reduction by definition height, the
failure cache, proof irrelevance, eta and structure eta, `Nat`/`String`
literal extensions, quotients, and iota reduction for nested and mutual
inductives. Inductive declarations are validated, and recursor data is
**derived** and compared with the export's claim rather than trusted -- the
format spec says it is redundant, and `bugs/rec-k-lie` is an export that lies
about a recursor to prove `False`.

## Layout

    src/fmain.bend         entry point; arena exit-code contract
    src/fcheck.bend        declaration checking on the flat store
    src/km.bend            the kernel machine: whnf, infer, defeq
    src/fstore.bend        the flat store
    src/level.bend         universe levels in normal form
    src/check.bend         inductive declarations, recursors, projections
    src/main.bend ...      the earlier trie-based checker, kept as an oracle
    tests/                 regression exports beyond the arena's suite
    bench/                 micro-benchmarks behind the design decisions
    tools/bend.sh          pinned toolchain wrapper
    tools/fbuild.sh        native build (see below)
    tools/score.py         local scorer, mirrors lka.py's semantics exactly
    tools/arena-link.py    makes lka.py see all tests, verifies every digest
    tools/invariants.sh    enforces zero @unsafe and bend --verdict
    tools/regress.sh       runs tests/ against a binary
    tools/fprobe.sh ...    tracing and profiling probes
    arena/bend-kernel.yaml arena checker definition

## Build and score

    ./tools/invariants.sh                        # the project invariant
    ./tools/bend.sh src/fmain.bend --check-only  # types and termination
    ./tools/fbuild.sh src/fmain.bend build/fbean

`tools/fbuild.sh` emits C with the pinned `bend` and compiles it with a nix
clang 21.1.8: Apple clang 21.0.0's ARM64 backend crashes on the machine's
generated C. Edit the clang path at the top of the script for your system.

    python3 tools/arena-link.py                  # once: expose the arena tests
    python3 tools/score.py --checker build/fbean --max-size 20
    tools/regress.sh build/fbean

    cd ~/.cache/lean-kernel-arena/arena          # the authoritative grader
    uv run lka.py run --checker bend-kernel --test 'bugs/*'

## How this is judged

Not by a single number.

1. **The arena's own harness.** `lka.py run --checker bend-kernel`, diffed
   against the checkers in `results.json` that score 205/205.
2. **The reference kernel as a differential oracle.** Unfold counts and
   pair-by-pair traces against the official Lean kernel locate algorithmic
   divergence that Bend's constant factor would otherwise hide.
3. **`bend --verdict`** and zero `@unsafe` definitions.
4. **Soundness first.** The 71 `reject` tests and the `bugs/` regressions
   are reported separately from the accept score, and a commit that loses
   one is not made.
