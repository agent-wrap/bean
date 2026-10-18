# bean -- a Lean 4 kernel checker in Bend 2.
#
# Arena contract (lean-kernel-arena/schemas/checker.json, lka.py:1498):
#   argv[1] is the export file; exit 0 = accept, 1 = reject, 2 = decline,
#   anything else = error. Every path here lands on one of those.
#
# Two traps that the arena's three-code contract makes dangerous, both found
# the hard way:
#   * `IO.try` exits with the effect's errno, and ENOENT is 2, which the
#     arena reads as "declined". I/O failure is caught here and mapped to 3.
#   * A Bend runtime abort exits 1, which the arena reads as *reject*. The
#     table abort that caused that is gone -- the term tables are tries now,
#     and tries have no size to overflow.
#
# Current limit: the input is read in a single call, so this version handles
# files up to the chunk size and answers 3, an error, on anything larger.
# bench/probe.bend streams 6.2 GB in constant memory; folding the decoder
# into it is the next step.

import Base
import ./scan.bend as S
import ./decode.bend as D
import ./term.bend as T
import ./level.bend as L
import ./store.bend as K
import ./check.bend as C

def unwrap_arg(m: Maybe<&1, String>) -> String:
  match m:
    case None{}:
      ""
    case Some{value}:
      value

def open_or_fail(r: Result<&1, &1, U32 & String, File>) -> IO(File):
  match r:
    case Fail{error}:
      match error:
        case Tuple{code, msg}:
          IO.die(File, 3, "cannot read input (errno " ++ U32.show(code) ++ "): " ++ msg)
    case Done{value}:
      IO.pure(File, value)

# Exit codes are the whole interface, so this is the only place that ends the
# process. `IO.die` writes the reason to stderr, which lka.py records.
def finish(v: C.V) -> IO(Unit):
  match v:
    case C.VAccept{}:
      IO.print("accept")
    case C.VReject{}:
      IO.die(Unit, 1, "reject")
    case C.VDecline{}:
      IO.die(Unit, 2, "decline: not yet checkable by this kernel")

# Silent truncation is the one way this version could accept a file whose
# later declarations are bad, so it is checked exactly rather than guessed at:
# a second read that returns any byte means the input did not fit.
def not_empty(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{head, tail}:
      True{}

def guard_eof(+more: Bool, v: C.V) -> IO(C.V):
  match more:
    case True{}:
      IO.die(C.V, 3, "input exceeds this version's single-read limit")
    case False{}:
      IO.pure(C.V, v)

def judge(+bs: List<&2, U32>) -> C.V:
  +recs = D.decode(bs, S.Sc.start(), D.Acc.start(), Nil{})
  +nex = U32.to_nat((K.max_ex_ix(recs, 0) + 1 : U32))
  +nlv = U32.to_nat((K.max_lvl_ix(recs, 0) + 1 : U32))
  C.judge(recs, K.decls_of(recs, Nil{}), nex, nlv, 32n,
          (K.max_any_ix(recs, 0) + 1 : U32))

# The read's (File, Result) pair is matched here rather than in `main`,
# because a `do` block admits no destructuring let and the pair is affine, so
# `Pair.fst`/`Pair.snd` cannot both be taken from it.
def read_and_judge(pr: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(C.V):
  match pr:
    case Tuple{f, r}:
      do IO<C.V>:
        bs : List<&2, U32> <- IO.pass(List<&2, U32>, r)
        pr2 : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 1)
        more : List<&2, U32> <- IO.pass(List<&2, U32>,
          Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, pr2))
        guard_eof(not_empty(more), judge(bs))

def main() -> IO(Unit):
  do IO<Unit>:
    av : List<&1, String> <- IO.args()
    path : String = unwrap_arg(List.get(&1, String, av, 1n))
    oh : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    f : File <- open_or_fail(oh)
    pr : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 33554432)
    v : C.V <- read_and_judge(pr)
    finish(v)
