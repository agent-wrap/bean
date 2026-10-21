# DEBUG PROBE (trie engine): for every declaration whose type fails to
# infer, report each Pi-binder domain under its context, then the
# codomain and its application spine -- to localise where inference fails.
import Base
import ./scan.bend as S
import ./decode.bend as D
import ./term.bend as T
import ./level.bend as L
import ./store.bend as K
import ./trie.bend as R
import ./subst.bend as U
import ./infer.bend as I
import ./tables.bend as B
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


def tagof(+x: T.Ex) -> String:
  match x:
    case T.ESort{l}:
      "Sort"
    case T.EAll{n, t, b, bi}:
      "Pi"
    case T.ELam{n, t, b, bi}:
      "Lam"
    case T.EApp{f, a}:
      "App"
    case T.EConst{n, us}:
      "Const(" ++ U32.show(n) ++ ")"
    case T.EBVar{i}:
      "BVar(" ++ U32.show(i) ++ ")"
    case _:
      "other"

def okstr(+b: Bool) -> String:
  match b:
    case True{}:
      "ok"
    case False{}:
      "FAIL"

def pline(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
          +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +e: U32,
          +ctx: List<&2, U32>, +ind: String) -> String:
  +x : T.Ex = U.ex_at(I.is_ex(st), e)
  +r = I.infer(8192n, st, mt, nt, lp, vt, x, e, ctx)
  ind ++ "#" ++ U32.show(e) ++ " " ++ tagof(x) ++ " infer="
    ++ okstr(I.ir_ok(r)) ++ " ty="
    ++ tagof(U.ex_at(I.is_ex(I.ir_st(r)), I.ir_ty(r))) ++ "\n"

# the application spine, down the function side: one line per node, plus
# each argument
def papp(fuel: Nat, +st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
         +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +x: T.Ex, +e: U32,
         +ctx: List<&2, U32>, +ind: String) -> String:
  match fuel x:
    case 0n _:
      pline(st, mt, nt, lp, vt, e, ctx, ind)
    case 1n+p T.EApp{f, a}:
      +f2 : U32 = f
      +a2 : U32 = a
      pline(st, mt, nt, lp, vt, e, ctx, ind)
        ++ pline(st, mt, nt, lp, vt, a2, ctx, ind ++ "  arg ")
        ++ papp(p, st, mt, nt, lp, vt, U.ex_at(I.is_ex(st), f2), f2, ctx, ind)
    case 1n+p _:
      pline(st, mt, nt, lp, vt, e, ctx, ind)

# walk a Pi spine: infer each domain under the context so far, then the body
def ppi(fuel: Nat, +st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
        +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +x: T.Ex, +e: U32,
        +ctx: List<&2, U32>, +d: U32) -> String:
  match fuel x:
    case 0n _:
      "fuel\n"
    case 1n+p T.EAll{n, t, b, bi}:
      +t2 : U32 = t
      +b2 : U32 = b
      "binder " ++ U32.show(d) ++ ":\n"
        ++ papp(12n, st, mt, nt, lp, vt, U.ex_at(I.is_ex(st), t2), t2, ctx,
                "  ")
        ++ ppi(p, st, mt, nt, lp, vt, U.ex_at(I.is_ex(st), b2), b2,
               Con{t2, ctx}, (d + 1 : U32))
    case 1n+p _:
      "codomain:\n" ++ papp(12n, st, mt, nt, lp, vt, x, e, ctx, "  ")

def whole(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
          +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +e: U32) -> String:
  +r = I.infer(8192n, st, mt, nt, lp, vt, U.ex_at(I.is_ex(st), e), e, Nil{})
  "whole type infer=" ++ okstr(I.ir_ok(r)) ++ " ty="
    ++ tagof(U.ex_at(I.is_ex(I.ir_st(r)), I.ir_ty(r))) ++ "\n"

def report(+ok: Bool, +st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
           +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +d: K.Dcl) -> String:
  match ok:
    case True{}:
      ""
    case False{}:
      "== decl name " ++ U32.show(K.dcl_name(d)) ++ "\n"
        ++ ppi(32n, st, mt, nt, lp, vt, U.ex_at(I.is_ex(st), K.dcl_type(d)),
               K.dcl_type(d), Nil{}, 0)

# every declaration (other than inductive blocks) whose TYPE fails to infer,
# against the environment of the declarations before it
def scan(ds: List<&2, K.Dcl>, +st: I.IS, +mt: R.Tr<I.Meta>,
         +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>) -> String:
  match ds:
    case Nil{}:
      "done"
    case Con{head, tail}:
      +h = head
      +r = I.infer(8192n, st, mt, nt, lp, vt,
                   U.ex_at(I.is_ex(st), K.dcl_type(h)), K.dcl_type(h), Nil{})
      +skip : Bool = U32.is_eq(K.dcl_name(h), 0)
      report(skip || I.ir_ok(r), st, mt, nt, lp, vt, h)
        ++ scan(tail, st, mt, B.add_nt(h, nt), B.add_lp(h, lp),
                B.add_vt(h, vt))

def go(+recs: List<&2, D.Rec>) -> String:
  +ds = K.decls_of(recs, Nil{})
  +nex = U32.to_nat((K.max_ex_ix(recs, 0) + 1 : U32))
  +nlv = U32.to_nat((K.max_lvl_ix(recs, 0) + 1 : U32))
  +nx : U32 = (K.max_any_ix(recs, 0) + 1 : U32)
  +ex = B.build_ex(recs, R.TNil{})
  +ln = B.lv_resolve(32n, nlv, B.build_lv(recs, R.TNil{}), R.TNil{})
  +st : I.IS = I.IS{ex, nx, ln, nx, R.TNil{}, K.build_ht(recs, R.TNil{}),
                    K.find_name(recs, [78, 97, 116], 4294967295),
                    K.find_name(recs,
                                [83, 116, 114, 105, 110, 103], 4294967295),
                    K.build_wk2(recs, R.TNil{})}
  scan(ds, st, C.build_meta(ds, ex, ln, R.TNil{}), R.TNil{}, R.TNil{},
       R.TNil{})

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
    IO.print(go(recs))
