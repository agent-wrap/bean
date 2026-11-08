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
import ./fstore.bend as F

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

def jr_go2(+recs: List<&2, D.Rec>, ab: U32 & U32, cd: List<&2, K.Dcl> & U32,
           +wk: U32, +wn: U32) -> FC.FL:
  match ab cd:
    case Tuple{mex, mlv} Tuple{ds, many}:
      FC.fjudge2(recs, ds, (mex + 1 : U32), U32.to_nat((mlv + 1 : U32)), 32n,
                 (many + 1 : U32), wk, wn)

def judge_recs2(+recs: List<&2, D.Rec>, +wk: U32, +wn: U32) -> FC.FL:
  ab cd = jr_ab(recs) jr_cd(recs)
  jr_go2(recs, ab, cd, wk, wn)

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

# argv[1] the export, argv[2] the worker index, argv[3] the worker count,
# argv[4] (optional) a claim directory: dynamic sharing (FC.FL)
def args_of(av: List<&1, String>) -> String & ((U32 & U32) & String):
  match av:
    case Nil{}:
      ("", ((0, 1), ""))
    case Con{a0, r1}:
      match r1:
        case Nil{}:
          ("", ((0, 1), ""))
        case Con{a1, r2}:
          match r2:
            case Nil{}:
              (a1, ((0, 1), ""))
            case Con{a2, r3}:
              match r3:
                case Nil{}:
                  (a1, ((arg_u32(Some{a2}, 0), 1), ""))
                case Con{a3, r4}:
                  match r4:
                    case Nil{}:
                      (a1, ((arg_u32(Some{a2}, 0), arg_u32(Some{a3}, 1)), ""))
                    case Con{a4, r5}:
                      (a1, ((arg_u32(Some{a2}, 0), arg_u32(Some{a3}, 1)), a4))

# argv[5] (optional, from tools/fbean-par.sh): the export's largest record
# index + 1. With it the store is allocated before decoding and every
# expression record goes straight into it (F.fb_route), so the decoded
# record list never holds the expressions; without it, the path above
def nx_of(av: List<&1, String>) -> U32:
  match av:
    case Con{a0, r1}:
      match r1:
        case Con{a1, r2}:
          match r2:
            case Con{a2, r3}:
              match r3:
                case Con{a3, r4}:
                  match r4:
                    case Con{a4, r5}:
                      match r5:
                        case Con{a5, r6}:
                          arg_u32(Some{a5}, 0)
                        case Nil{}:
                          0
                    case Nil{}:
                      0
                case Nil{}:
                  0
            case Nil{}:
              0
        case Nil{}:
          0
    case Nil{}:
      0

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

# ---- the nx path: expressions decoded straight into the store ----------
def route_fin(r: (Array<T.Ex> & U32) & List<&2, D.Rec>,
              out: List<&2, D.Rec>) -> (Array<T.Ex> & U32) & List<&2, D.Rec>:
  match r:
    case Tuple{ab, kept}:
      (ab, app_recs(F.rev_recs(kept, Nil{}), out))

def route_into(batch: List<&2, D.Rec>, so: (Array<T.Ex> & U32) & List<&2, D.Rec>,
               +cap: U32) -> (Array<T.Ex> & U32) & List<&2, D.Rec>:
  match so:
    case Tuple{ab, out}:
      route_fin(F.fb_route(batch, (ab, Nil{}), cap), out)

def ingest2A(+full: Bool, pr: List<&2, U32> & List<&2, U32>,
             parts: List<&2, List<&2, U32>>, +np: U32,
             so: (Array<T.Ex> & U32) & List<&2, D.Rec>, +cap: U32)
    -> List<&2, U32> & (List<&2, List<&2, U32>> & (U32 & ((Array<T.Ex> & U32) & List<&2, D.Rec>))):
  match full pr:
    case True{} Tuple{comp, tail}:
      (tail, (Nil{}, (0, route_into(pdec(3n, Con{comp, parts}, (np + 1 : U32)), so, cap))))
    case False{} Tuple{comp, tail}:
      (tail, (Con{comp, parts}, ((np + 1 : U32), so)))

def ingestA(bs: List<&2, U32>,
            st: List<&2, U32> & (List<&2, List<&2, U32>> & (U32 & ((Array<T.Ex> & U32) & List<&2, D.Rec>))),
            +cap: U32)
    -> List<&2, U32> & (List<&2, List<&2, U32>> & (U32 & ((Array<T.Ex> & U32) & List<&2, D.Rec>))):
  match st:
    case Tuple{carry, Tuple{parts, Tuple{np, so}}}:
      +n2 : U32 = np
      ingest2A(U32.is_ge((n2 + 1 : U32), 8), split_nl(carry, bs), parts, n2,
               so, cap)

def flushA(st: List<&2, U32> & (List<&2, List<&2, U32>> & (U32 & ((Array<T.Ex> & U32) & List<&2, D.Rec>))),
           +cap: U32) -> (Array<T.Ex> & U32) & List<&2, D.Rec>:
  match st:
    case Tuple{carry, Tuple{parts, Tuple{np, so}}}:
      +n2 : U32 = np
      route_into(pdec(3n, parts, n2), so, cap)

def streamA(fuel: Nat, +chunk: U32, +cap: U32,
            pr: File & Result<&1, &1, U32 & String, List<&2, U32>>,
            st: List<&2, U32> & (List<&2, List<&2, U32>> & (U32 & ((Array<T.Ex> & U32) & List<&2, D.Rec>))))
    -> IO((Array<T.Ex> & U32) & List<&2, D.Rec>):
  match fuel pr:
    case 0n Tuple{f, r}:
      do IO<(Array<T.Ex> & U32) & List<&2, D.Rec>>:
        bs : List<&2, U32> <- IO.pass(List<&2, U32>, r)
        File.close(f)
        IO.pure((Array<T.Ex> & U32) & List<&2, D.Rec>, flushA(ingestA(bs, st, cap), cap))
    case 1n+p Tuple{f, r}:
      do IO<(Array<T.Ex> & U32) & List<&2, D.Rec>>:
        bs : List<&2, U32> <- IO.pass(List<&2, U32>, r)
        nxt : File & Result<&1, &1, U32 & String, List<&2, U32>>
          <- File.read_bytes(f, chunk)
        streamA(p, chunk, cap, nxt, ingestA(bs, st, cap))

# ---- dynamic sharing: claim files, one per chunk of 256 declarations ----
# (File.open has no exclusive mode: a chunk is claimed when its file does
# not exist yet; two workers racing both check it -- see FC.FL)
def opened(r: Result<&1, &1, U32 & String, File>) -> IO(U32):
  match r:
    case Fail{error}:
      IO.pure(U32, 0)
    case Done{value}:
      do IO<U32>:
        u : Unit <- File.close(value)
        IO.pure(U32, 1)

def try_open(path: String, mode: String) -> IO(U32):
  do IO<U32>:
    oh : Result<&1, &1, U32 & String, File> <- File.open(path, mode)
    opened(oh)

# 1 when this worker created the claim (the file did not exist)
def claim_go(+have: U32, path: String) -> IO(U32):
  match have:
    case 0:
      try_open(path, "w")
    case _:
      IO.pure(U32, 0)

def cpath(+dir: String, +c: U32) -> String:
  dir ++ "/" ++ U32.show(c)

def dyn_step(fuel: Nat, +dir: String, +c: U32, +wk: U32, +wn: U32,
             pr: FC.FL & Bool) -> IO(C.V):
  match fuel pr:
    case 0n Tuple{s2, m}:
      IO.pure(C.V, C.VDecline{})
    case 1n+p Tuple{s2, False{}}:
      IO.pure(C.V, FC.fl_fin(s2))
    case 1n+p Tuple{s2, True{}}:
      do IO<C.V>:
        h : U32 <- try_open(cpath(dir, c), "r")
        w : U32 <- claim_go(h, cpath(dir, c))
        dyn_step(p, dir, (c + 1 : U32), wk, wn,
                 FC.fl_more(FC.fck_chunk(256n, U32.is_eq(w, 1), wk, wn, s2)))

def run_dyn(+recs: List<&2, D.Rec>, +wk: U32, +wn: U32,
            +dir: String) -> IO(Unit):
  do IO<Unit>:
    v : C.V <- dyn_step(4194304n, dir, 0, wk, wn,
                        FC.fl_more(judge_recs2(recs, wk, wn)))
    finish(v)

def run_pick(+recs: List<&2, D.Rec>, +wk: U32, +wn: U32,
             dir: String) -> IO(Unit):
  match dir:
    case SNil{}:
      finish(judge_wk(recs, wk, wn))
    case SCon{head, tail}:
      run_dyn(recs, wk, wn, SCon{head, tail})

def judge_recsA(+recs: List<&2, D.Rec>, arr: Array<T.Ex>, +wk: U32, +wn: U32,
                +nx: U32) -> C.V:
  +r2 = recs
  FC.fjudgeA(r2, arr, K.decls_of(r2, Nil{}),
             U32.to_nat((K.max_lvl_ix(r2, 0) + 1 : U32)), 32n, nx, wk, wn)

def judge_recs2A(+recs: List<&2, D.Rec>, arr: Array<T.Ex>, +wk: U32,
                 +wn: U32, +nx: U32) -> FC.FL:
  +r2 = recs
  FC.fjudge2A(r2, arr, K.decls_of(r2, Nil{}),
              U32.to_nat((K.max_lvl_ix(r2, 0) + 1 : U32)), 32n, nx, wk, wn)

def judge_wkA(+recs: List<&2, D.Rec>, arr: Array<T.Ex>, +wk: U32, +wn: U32,
              +nx: U32) -> C.V:
  +k2 : U32 = wk
  +n2 : U32 = wn
  +ok : Bool = U32.is_lt(k2, n2) && U32.is_gt(n2, 0)
  judge_recsA(recs, arr, S.pick(ok, k2, 0), S.pick(ok, n2, 1), nx)

def run_dynA(+recs: List<&2, D.Rec>, arr: Array<T.Ex>, +wk: U32, +wn: U32,
             +dir: String, +nx: U32) -> IO(Unit):
  do IO<Unit>:
    v : C.V <- dyn_step(4194304n, dir, 0, wk, wn,
                        FC.fl_more(judge_recs2A(recs, arr, wk, wn, nx)))
    finish(v)

def run_pickA(+recs: List<&2, D.Rec>, arr: Array<T.Ex>, +wk: U32, +wn: U32,
              dir: String, +nx: U32) -> IO(Unit):
  match dir:
    case SNil{}:
      finish(judge_wkA(recs, arr, wk, wn, nx))
    case SCon{head, tail}:
      run_dynA(recs, arr, wk, wn, SCon{head, tail}, nx)

def run_a2(+ok: Bool, +recs: List<&2, D.Rec>, arr: Array<T.Ex>, +wk: U32,
           +wn: U32, dir: String, +nx: U32) -> IO(Unit):
  match ok:
    case True{}:
      run_pickA(recs, arr, wk, wn, dir, nx)
    case False{}:
      finish(C.VDecline{})

# an expression index at or past the store's capacity: decline (no read)
def run_a(res: (Array<T.Ex> & U32) & List<&2, D.Rec>, +wk: U32, +wn: U32,
          dir: String, +nx: U32) -> IO(Unit):
  match res:
    case Tuple{Tuple{arr, bad}, recs}:
      run_a2(U32.is_eq(bad, 0), recs, arr, wk, wn, dir, nx)

def main_a(path: String, +wk: U32, +wn: U32, dir: String, +nx: U32) -> IO(Unit):
  do IO<Unit>:
    oh : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    f : File <- open_or_fail(oh)
    pr : File & Result<&1, &1, U32 & String, List<&2, U32>>
      <- File.read_bytes(f, 4194304)
    res : (Array<T.Ex> & U32) & List<&2, D.Rec> <- streamA(2400n, 4194304, nx, pr,
      Tuple{Nil{}, Tuple{Nil{}, Tuple{0, Tuple{Tuple{FC.new_store(nx), 0}, Nil{}}}}})
    run_a(res, wk, wn, dir, nx)

def main_go(pw: String & ((U32 & U32) & String)) -> IO(Unit):
  match pw:
    case Tuple{path, Tuple{Tuple{wk, wn}, dir}}:
      do IO<Unit>:
        oh : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
        f : File <- open_or_fail(oh)
        pr : File & Result<&1, &1, U32 & String, List<&2, U32>>
          <- File.read_bytes(f, 4194304)
        recs : List<&2, D.Rec> <- stream(2400n, 4194304, pr,
          Tuple{Nil{}, Tuple{Nil{}, Tuple{0, Nil{}}}})
        run_pick(recs, wk, wn, dir)

def main_sel2(+go: Bool, +nx: U32, path: String, +wk: U32, +wn: U32,
              dir: String) -> IO(Unit):
  match go:
    case True{}:
      main_a(path, wk, wn, dir, nx)
    case False{}:
      main_go((path, ((wk, wn), dir)))

def main_sel(+nx: U32, pw: String & ((U32 & U32) & String)) -> IO(Unit):
  match pw:
    case Tuple{path, Tuple{Tuple{wk, wn}, dir}}:
      main_sel2(U32.is_gt(nx, 0), nx, path, wk, wn, dir)

def main() -> IO(Unit):
  do IO<Unit>:
    av : List<&1, String> <- IO.args()
    bv : List<&1, String> <- IO.args()
    main_sel(nx_of(bv), args_of(av))
