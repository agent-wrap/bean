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

`v0.13.1`. 5,040 lines of Bend. Graded by `lka.py` itself and by
`tools/score.py`, which agree:

    ran 223 of 223 tests
      correct=94   declined=118   error=7   incorrect=0
      score 170/205 scorable
      soundness 42/71 reject-tests rejected
      WRONG 0

**Zero wrong answers at every released step.** It was violated eleven times
during development; every one was the same mistake -- answering on
insufficient evidence -- and docs/measurements.md records all of them with
their causes, because they have been more informative than the score.

52 accepts, 42 rejects including eight of the arena's real soundness
regressions. Six inductive-containing files are now accepted, three of them
(`062_emptyRec`, `063_boolRec`, `068_punitRec`) with proofs that **apply a
recursor** -- which typecheck against the derived type, not the export's -- and it is accepted because its recursor's type was **derived** and
matched the export's claim: the format spec says recursor data is redundant
and should be validated rather than trusted, and `bugs/rec-k-lie` is an export
that lies about one to prove `False`.

What is done, with the evidence:

* **Arena contract**, graded by `lka.py`, not a local imitation.
* **Streaming ingestion**: 6.2 GB in 17.8 s at 38 MB constant RSS, exact
  against `wc`. Reading mathlib costs 0.34% of its time limit.
* **Scanner and decoder**: 196/196 small-corpus files agree record-for-record
  with a real JSON parser, including the object ordinals that group an
  inductive block's items.
* **Term tables as reusable `Data` tries** -- the central design decision,
  and what lets the kernel be ordinary recursive functions rather than an
  explicit stack machine. See docs/bend-notes.md.
* **Universe levels** in normal form with substitution, resolved
  order-independently, with a three-valued zero test.
* **Lifting, instantiation, universe substitution inside terms, weak-head
  normalisation** (beta, zeta, delta), **inference** including application,
  and **definitional equality** -- each one self-recursive function.
* **Bidirectional checking** and an **incremental environment**.
* **Inductive declarations**: telescope shape and universe, parameter counts,
  constructor result head and parameter positions, indices free of the
  datatype, strict positivity with a memoised three-valued occurrence check,
  the recursor's universe-parameter count with the large-elimination
  restriction, and a **derived recursor type** for the base case.
* **Projection validity** and the usual structural checks.
* `bend --verdict` green and zero `@unsafe`, enforced by
  `./tools/invariants.sh`.

What is not done: recursor derivation beyond the base case (parameters,
indices, constructor fields and their inductive hypotheses), iota reduction,
quotients, proof irrelevance, eta, the `Nat`/`String` literal extensions,
nested and mutual inductives, memoising `infer` and `defeq`, and folding the
decoder into the streaming reader. Fuel is bounded at 24 to keep
`perf/app-lam` fast, which costs completeness.

## Layout

    src/main.bend          entry point; arena exit-code contract, chunked reader
    bench/probe.bend       the ingestion measurement in docs/measurements.md
    tools/bend.sh          pinned toolchain wrapper
    tools/score.py         local scorer, mirrors lka.py:1498-1525 exactly
    tools/arena-link.py    makes lka.py see all 223 tests, verifies every digest
    tools/invariants.sh    enforces zero @unsafe and bend --verdict on every module
    tools/census-check.py  diffs the scanner against a real JSON parser
    tools/decode-check.py  diffs every decoded field against a real JSON parser
    arena/bend-kernel.yaml arena checker definition
    docs/measurements.md   every number, with the command that produced it
    docs/bend-notes.md     the Bend constraints that decide the architecture

## Build and score

    ./tools/invariants.sh                        # the project invariant
    ./tools/bend.sh src/main.bend --check-only   # types and termination
    ./tools/bend.sh src/main.bend --verdict      # recheck with the proven kernel
    ./tools/bend.sh src/main.bend -o build/bean

    python3 tools/arena-link.py                  # once: expose all 223 tests
    python3 tools/score.py                       # score locally
    python3 tools/score.py --max-size 2          # fast inner loop

    cd ~/.cache/lean-kernel-arena/arena          # the authoritative grader
    uv run lka.py run --checker bend-kernel --test 'bugs/*'

## How this is judged

Not by me, and not by a single number.

1. **The arena's own harness.** `lka.py run --checker bend-kernel`, diffed
   against the nine checkers in `results.json` that score 205/205.
2. **Reduction-step counts**, not seconds. `lazylean` with `LL_WORK_REPORT=1`
   reports per-declaration steps and cache hits. Reporting steps beside its
   steps keeps an algorithmic error from hiding behind Bend's constant factor.
3. **`sokonanodazo`**, an independent Rust checker, as a verdict oracle on any
   input (`--stdin --nat-extension --string-extension --axiom-allow-all`).
4. **`bend --verdict`** and `grep -c '@unsafe' src/*.bend` == 0.
5. **Mutation testing.** Perturbed accepted exports must be rejected; an
   accepted mutant is a soundness hole the arena does not yet cover.

Three numbers get reported, never one: the 71 `reject` tests, the 18 `bugs/`
regressions, and the 134 `accept` tests. `declines:` stays empty until
measurement forces an entry, and any entry cites the measurement.
