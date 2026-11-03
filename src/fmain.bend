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
# the four whole-list scans as a parallel pair of parallel pairs
def jr_ab(+recs: List<&2, D.Rec>) -> U32 & U32:
  a b = K.max_ex_ix(recs, 0) K.max_lvl_ix(recs, 0)
  (a, b)

def jr_cd(+recs: List<&2, D.Rec>) -> List<&2, K.Dcl> & U32:
  c d = K.decls_of(recs, Nil{}) K.max_any_ix(recs, 0)
  (c, d)

def jr_go(+recs: List<&2, D.Rec>, ab: U32 & U32, cd: List<&2, K.Dcl> & U32,
          +wk: U32, +wn: U32) -> C.V:
  match ab cd:
    case Tuple{mex, mlv} Tuple{ds, many}:
      FC.fjudge(recs, ds, (mex + 1 : U32), U32.to_nat((mlv + 1 : U32)), 32n,
                (many + 1 : U32), wk, wn)

def judge_recs(+recs: List<&2, D.Rec>, +wk: U32, +wn: U32) -> C.V:
  ab cd = jr_ab(recs) jr_cd(recs)
  jr_go(recs, ab, cd, wk, wn)

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
# Pure: pull the record list out of a threaded decode triple.
def trip_out(trip: S.Sc & D.Acc & List<&2, D.Rec>) -> List<&2, D.Rec>:
  match trip:
    case Tuple{st, Tuple{acc, out}}:
      out

# ---- parallel decoding --------------------------------------------------
# The decoder's state resets at every newline (Sc.start, Acc.start) and a
# record is emitted there, so a run of COMPLETE lines decodes the same alone
# as inside the stream. Each chunk read is cut at its last newline (the
# remainder carries into the next chunk); every 16 chunks are decoded as a
# balanced tree of parallel calls and their records joined in stream order
# (newest first, as the sequential reader built them). A last line with no
# newline emits no record, as before.

def rev_onto(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      rev_onto(tail, Con{head, acc})

# rb is a chunk reversed: pop bytes until a newline (they are the remainder,
# collected back in file order); what is left, from that newline on, is the
# complete part, still reversed
def nl_drop2(+isnl: Bool, +h: U32, t: List<&2, U32>,
             tail: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match isnl:
    case True{}:
      (Con{h, t}, tail)
    case False{}:
      (t, Con{h, tail})

def nl_drop(fuel: Nat, +done: Bool,
            st: List<&2, U32> & List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match fuel done st:
    case 0n _ _:
      st
    case 1n+p True{} _:
      st
    case 1n+p False{} Tuple{Nil{}, tail}:
      (Nil{}, tail)
    case 1n+p False{} Tuple{Con{h, t}, tail}:
      +h2 : U32 = h
      +nl : Bool = U32.is_eq(h2, 10)
      nl_drop(p, nl, nl_drop2(nl, h2, t, tail))

def split_fin(pr: List<&2, U32> & List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match pr:
    case Tuple{revcomp, tail}:
      (rev_onto(revcomp, Nil{}), tail)

# (complete lines, remainder) of carry ++ bs
def split_nl(carry: List<&2, U32>, bs: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  split_fin(nl_drop(16777216n, False{}, (rev_onto(bs, rev_onto(carry, Nil{})), Nil{})))

def dec_chunk(bs: List<&2, U32>) -> List<&2, D.Rec>:
  trip_out(D.decode_resume(bs, S.Sc.start(), D.Acc.start(), Nil{}))

def app_recs(xs: List<&2, D.Rec>, ys: List<&2, D.Rec>) -> List<&2, D.Rec>:
  List.append(&2, D.Rec, xs, ys)

# chunks newest first -> their records newest first
def dec_seq(cs: List<&2, List<&2, U32>>) -> List<&2, D.Rec>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      app_recs(dec_chunk(c), dec_seq(t))

def take_cs(n: Nat, +cs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match n cs:
    case 0n _:
      Nil{}
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{c, t}:
      Con{c, take_cs(p, t)}

def drop_cs(n: Nat, +cs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match n cs:
    case 0n _:
      cs
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{c, t}:
      drop_cs(p, t)

# depth-d balanced parallel decode of n chunks (newest first)
def pdec(d: Nat, +cs: List<&2, List<&2, U32>>, +n: U32) -> List<&2, D.Rec>:
  match d:
    case 0n:
      dec_seq(cs)
    case 1n+p:
      +q = p
      +h : U32 = (n / 2 : U32)
      a b = pdec(q, take_cs(U32.to_nat(h), cs), h) pdec(q, drop_cs(U32.to_nat(h), cs), (n - h : U32))
      app_recs(a, b)

# the stream state: (remainder, (chunks newest first, (count, records)))
def ingest2(+full: Bool, pr: List<&2, U32> & List<&2, U32>,
            parts: List<&2, List<&2, U32>>, +np: U32,
            out: List<&2, D.Rec>) -> List<&2, U32> & (List<&2, List<&2, U32>> & (U32 & List<&2, D.Rec>)):
  match full pr:
    case True{} Tuple{comp, tail}:
      (tail, (Nil{}, (0, app_recs(pdec(4n, Con{comp, parts}, (np + 1 : U32)), out))))
    case False{} Tuple{comp, tail}:
      (tail, (Con{comp, parts}, ((np + 1 : U32), out)))

def ingest(bs: List<&2, U32>,
           st: List<&2, U32> & (List<&2, List<&2, U32>> & (U32 & List<&2, D.Rec>))) -> List<&2, U32> & (List<&2, List<&2, U32>> & (U32 & List<&2, D.Rec>)):
  match st:
    case Tuple{carry, Tuple{parts, Tuple{np, out}}}:
      +n2 : U32 = np
      ingest2(U32.is_ge((n2 + 1 : U32), 16), split_nl(carry, bs), parts, n2,
              out)

def flush_st(st: List<&2, U32> & (List<&2, List<&2, U32>> & (U32 & List<&2, D.Rec>))) -> List<&2, D.Rec>:
  match st:
    case Tuple{carry, Tuple{parts, Tuple{np, out}}}:
      +n2 : U32 = np
      app_recs(pdec(4n, parts, n2), out)

def stream(fuel: Nat, +chunk: U32,
           pr: File & Result<&1, &1, U32 & String, List<&2, U32>>,
           st: List<&2, U32> & (List<&2, List<&2, U32>> & (U32 & List<&2, D.Rec>))) -> IO(List<&2, D.Rec>):
  match fuel pr:
    case 0n Tuple{f, r}:
      do IO<List<&2, D.Rec>>:
        bs : List<&2, U32> <- IO.pass(List<&2, U32>, r)
        File.close(f)
        IO.pure(List<&2, D.Rec>, flush_st(ingest(bs, st)))
    case 1n+p Tuple{f, r}:
      do IO<List<&2, D.Rec>>:
        bs : List<&2, U32> <- IO.pass(List<&2, U32>, r)
        nxt : File & Result<&1, &1, U32 & String, List<&2, U32>>
          <- File.read_bytes(f, chunk)
        stream(p, chunk, nxt, ingest(bs, st))

def main_go(pw: String & (U32 & U32)) -> IO(Unit):
  match pw:
    case Tuple{path, Tuple{wk, wn}}:
      do IO<Unit>:
        oh : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
        f : File <- open_or_fail(oh)
        pr : File & Result<&1, &1, U32 & String, List<&2, U32>>
          <- File.read_bytes(f, 4194304)
        recs : List<&2, D.Rec> <- stream(2400n, 4194304, pr,
          Tuple{Nil{}, Tuple{Nil{}, Tuple{0, Nil{}}}})
        finish(judge_wk(recs, wk, wn))

def main() -> IO(Unit):
  do IO<Unit>:
    av : List<&1, String> <- IO.args()
    main_go(args_of(av))
