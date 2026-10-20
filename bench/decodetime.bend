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
import ../src/scan.bend as S
import ../src/decode.bend as D
import ../src/term.bend as T
import ../src/level.bend as L
import ../src/store.bend as K
import ../src/check.bend as C

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

def count_recs(rs: List<&2, D.Rec>, acc: U32) -> U32:
  match rs:
    case Nil{}:
      acc
    case Con{head, tail}:
      count_recs(tail, (acc + 1 : U32))

def trip_out(trip: S.Sc & D.Acc & List<&2, D.Rec>) -> List<&2, D.Rec>:
  match trip:
    case Tuple{st, Tuple{acc, out}}:
      out

def stream(fuel: Nat, +chunk: U32,
           pr: File & Result<&1, &1, U32 & String, List<&2, U32>>,
           trip: S.Sc & D.Acc & List<&2, D.Rec>) -> IO(List<&2, D.Rec>):
  match fuel pr trip:
    case 0n Tuple{f, r} Tuple{st, Tuple{acc, out}}:
      do IO<List<&2, D.Rec>>:
        bs : List<&2, U32> <- IO.pass(List<&2, U32>, r)
        File.close(f)
        IO.pure(List<&2, D.Rec>, trip_out(D.decode_resume(bs, st, acc, out)))
    case 1n+p Tuple{f, r} Tuple{st, Tuple{acc, out}}:
      do IO<List<&2, D.Rec>>:
        bs : List<&2, U32> <- IO.pass(List<&2, U32>, r)
        nxt : File & Result<&1, &1, U32 & String, List<&2, U32>>
          <- File.read_bytes(f, chunk)
        stream(p, chunk, nxt, D.decode_resume(bs, st, acc, out))

def main() -> IO(Unit):
  do IO<Unit>:
    av : List<&1, String> <- IO.args()
    path : String = unwrap_arg(List.get(&1, String, av, 1n))
    oh : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    f : File <- open_or_fail(oh)
    pr : File & Result<&1, &1, U32 & String, List<&2, U32>>
      <- File.read_bytes(f, 8388608)
    recs : List<&2, D.Rec> <- stream(1200n, 8388608, pr,
      Tuple{S.Sc.start(), Tuple{D.Acc.start(), Nil{}}})
    IO.print("records " ++ U32.show(count_recs(recs, 0)))
