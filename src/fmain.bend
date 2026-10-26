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
import ./fcheck.bend as FC

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

# argv[2], argv[3] (optional): this process is worker WK of WN -- it checks
# the declarations whose index is WK mod WN and trusts the others (they
# still enter every table). tools/fbean-par.sh runs WN such processes on
# one export and joins their verdicts: every declaration is checked by
# exactly one of them, so the join (any reject -> reject, else any
# decline -> decline, else accept) is the sequential verdict, in the wall
# time of the slowest share -- the arena's limits are wall-clock, and the
# kernel checks one declaration at a time.
def judge_recs(+recs: List<&2, D.Rec>, +wk: U32, +wn: U32) -> C.V:
  +nex = U32.to_nat((K.max_ex_ix(recs, 0) + 1 : U32))
  +nlv = U32.to_nat((K.max_lvl_ix(recs, 0) + 1 : U32))
  FC.fjudge(recs, K.decls_of(recs, Nil{}), nex, nlv, 32n,
          (K.max_any_ix(recs, 0) + 1 : U32), wk, wn)

# a worker index past the count reads as a single worker checking all
def judge_wk(+recs: List<&2, D.Rec>, +wk: U32, +wn: U32) -> C.V:
  +k2 : U32 = wk
  +n2 : U32 = wn
  +ok : Bool = U32.is_lt(k2, n2) && U32.is_gt(n2, 0)
  judge_recs(recs, S.pick(ok, k2, 0), S.pick(ok, n2, 1))

# a decimal argument (digits only, non-empty); anything else reads as the
# default
def arg_u32_go(s: String, +acc: U32, +ok: Bool, +any: Bool) -> U32 & Bool:
  match s:
    case SNil{}:
      (acc, ok && any)
    case SCon{head, tail}:
      +c : U32 = Char.to_u32(head)
      +dg : Bool = U32.is_ge(c, 48) && U32.is_le(c, 57)
      arg_u32_go(tail, (acc * 10 + (c - 48 : U32) : U32), ok && dg, True{})

def arg_u32_fin(pr: U32 & Bool, +dflt: U32) -> U32:
  match pr:
    case Tuple{v, ok}:
      S.pick(ok, v, dflt)

def arg_u32(m: Maybe<&1, String>, +dflt: U32) -> U32:
  match m:
    case None{}:
      dflt
    case Some{value}:
      arg_u32_fin(arg_u32_go(value, 0, True{}, False{}), dflt)

# argv[1] the export, argv[2] the worker index, argv[3] the worker count
def args_of(av: List<&1, String>) -> String & (U32 & U32):
  match av:
    case Nil{}:
      ("", (0, 1))
    case Con{a0, r1}:
      match r1:
        case Nil{}:
          ("", (0, 1))
        case Con{a1, r2}:
          match r2:
            case Nil{}:
              (a1, (0, 1))
            case Con{a2, r3}:
              match r3:
                case Nil{}:
                  (a1, (arg_u32(Some{a2}, 0), 1))
                case Con{a3, r4}:
                  (a1, (arg_u32(Some{a2}, 0), arg_u32(Some{a3}, 1)))

# Pure: pull the record list out of a threaded decode triple.
def trip_out(trip: S.Sc & D.Acc & List<&2, D.Rec>) -> List<&2, D.Rec>:
  match trip:
    case Tuple{st, Tuple{acc, out}}:
      out

# Single self-recursive streaming reader, after bench/probe.bend's `drain`:
# the read-pair `pr` and the carried decode triple are PARAMETERS, so every
# match is on a field scrutinee and nothing is mutually recursive. Each step
# pulls one chunk, folds its bytes into the triple with `decode_resume` (an
# empty chunk folds to a no-op, so reads past EOF are harmless), drops the
# bytes, and reads the next chunk. `fuel` (1200 * 8 MB = 9.4 GB) bounds the
# step count; the file is consumed well before it, and the remaining steps are
# cheap empty reads. One chunk of bytes lives at a time -- no read-size cap,
# nothing to truncate, so no truncation guard.
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

def main_go(pw: String & (U32 & U32)) -> IO(Unit):
  match pw:
    case Tuple{path, Tuple{wk, wn}}:
      do IO<Unit>:
        oh : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
        f : File <- open_or_fail(oh)
        pr : File & Result<&1, &1, U32 & String, List<&2, U32>>
          <- File.read_bytes(f, 8388608)
        recs : List<&2, D.Rec> <- stream(1200n, 8388608, pr,
          Tuple{S.Sc.start(), Tuple{D.Acc.start(), Nil{}}})
        finish(judge_wk(recs, wk, wn))

def main() -> IO(Unit):
  do IO<Unit>:
    av : List<&1, String> <- IO.args()
    main_go(args_of(av))
