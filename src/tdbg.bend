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

def tristr(+t: L.Tri) -> String:
  match t:
    case L.TYes{}:
      "YES"
    case L.TNo{}:
      "NO"
    case L.TUnk{}:
      "UNK"

def digits(ds: List<&2, U32>) -> String:
  match ds:
    case Nil{}:
      ""
    case Con{head, tail}:
      U32.show(head) ++ digits(tail)

def pat(xs: List<&2, L.Atom>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{head, tail}:
      match head:
        case L.At{b, o}:
          " b" ++ U32.show(b) ++ "+" ++ U32.show(o) ++ pat(tail)

def pln(fuel: Nat, +a: L.LN) -> String:
  match fuel a:
    case 0n _:
      "~"
    case 1n+p L.LNun{}:
      "UN"
    case 1n+p L.LNsym{}:
      "SYM"
    case 1n+p L.LNmax{xs}:
      "max[" ++ pat(xs) ++ " ]"
    case 1n+p L.LNimax{x, y, o}:
      +pf = p
      "imax(" ++ pln(pf, x) ++ ", " ++ pln(pf, y) ++ ")+" ++ U32.show(o)
    case 1n+p L.LNmx{xs, y, r}:
      +pf = p
      "max[" ++ pat(xs) ++ " " ++ pln(pf, y) ++ " | " ++ pln(pf, r) ++ " ]"

def sortlv(+st: I.IS, +x: T.Ex) -> String:
  match x:
    case T.ESort{l}:
      " {" ++ pln(8n, R.get(L.LN, 64n, I.is_lnt(st), l, L.LNun{})) ++ "}"
    case _:
      ""

def lvls(+ln: R.Tr<L.LN>, us: List<&2, U32>) -> String:
  match us:
    case Nil{}:
      ""
    case Con{head, tail}:
      ".{" ++ pln(8n, R.get(L.LN, 64n, ln, head, L.LNun{})) ++ "}" ++ lvls(ln, tail)

def ppn(fuel: Nat, +ex: R.Tr<T.Ex>, +ln: R.Tr<L.LN>, +x: T.Ex) -> String:
  match fuel x:
    case 0n _:
      "~"
    case 1n+p T.EBVar{i}:
      "#" ++ U32.show(i)
    case 1n+p T.ESort{l}:
      "Sort"
    case 1n+p T.EConst{n, us}:
      "@" ++ U32.show(n) ++ lvls(ln, us)
    case 1n+p T.EApp{f, a}:
      +pf = p
      "(" ++ ppn(pf, ex, ln, U.ex_at(ex, f)) ++ " " ++ ppn(pf, ex, ln, U.ex_at(ex, a)) ++ ")"
    case 1n+p T.ELam{n, t, b, bi}:
      +pf = p
      "(fun:" ++ ppn(pf, ex, ln, U.ex_at(ex, t)) ++ ". " ++ ppn(pf, ex, ln, U.ex_at(ex, b)) ++ ")"
    case 1n+p T.EAll{n, t, b, bi}:
      +pf = p
      "(Pi:" ++ ppn(pf, ex, ln, U.ex_at(ex, t)) ++ ". " ++ ppn(pf, ex, ln, U.ex_at(ex, b)) ++ ")"
    case 1n+p T.ELet{n, t, v, b}:
      +pf = p
      "(let " ++ ppn(pf, ex, ln, U.ex_at(ex, v)) ++ "; " ++ ppn(pf, ex, ln, U.ex_at(ex, b)) ++ ")"
    case 1n+p T.EProj{tn, i, s}:
      ppn(p, ex, ln, U.ex_at(ex, s)) ++ ".pi" ++ U32.show(i)
    case 1n+p T.ENat{d}:
      digits(d)
    case 1n+p _:
      "?"

# term printer over the trie store; names as @index (decoded by python)
def ppx(fuel: Nat, +ex: R.Tr<T.Ex>, +ln: R.Tr<L.LN>, +i: U32) -> String:
  match fuel:
    case 0n:
      "~"
    case 1n+p:
      ppn(p, ex, ln, U.ex_at(ex, i))

# one line for a comparison of two (already whnf-able) indices
def dline(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
          +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +a: U32, +b: U32,
          +ctx: List<&2, U32>, +ind: String) -> String:
  +d = I.defeq(64n, U32.is_eq(a, b), st, mt, nt, lp, vt, ctx,
               U.ex_at(I.is_ex(st), a), U.ex_at(I.is_ex(st), b))
  ind ++ tristr(I.dr_r(d)) ++ "  " ++ ppx(30n, I.is_ex(st), I.is_lnt(st), a)
    ++ sortlv(st, U.ex_at(I.is_ex(st), a))
    ++ "\n" ++ ind ++ "  =?= " ++ ppx(30n, I.is_ex(st), I.is_lnt(st), b)
    ++ sortlv(st, U.ex_at(I.is_ex(st), b)) ++ "\n"

# descend: a pair of whnf'd NODES (with their indices) under ctx
def dtr(fuel: Nat, +st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
        +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +x: T.Ex, +y: T.Ex,
        +xi: U32, +yi: U32, +ctx: List<&2, U32>, +ind: String) -> String:
  match fuel x y:
    case 0n _ _:
      ""
    case 1n+p T.EAll{n1, t1, b1, i1} T.EAll{n2, t2, b2, i2}:
      +pf = p
      +ta : U32 = t1
      +bb1 : U32 = b1
      +bb2 : U32 = b2
      +tt2 : U32 = t2
      +wa = I.whd(st, mt, lp, vt, bb1)
      +wb = I.whd(I.ir_st(wa), mt, lp, vt, bb2)
      +s3 = I.ir_st(wb)
      dline(st, mt, nt, lp, vt, ta, tt2, ctx, ind ++ "dom ")
        ++ dline(s3, mt, nt, lp, vt, I.ir_ty(wa), I.ir_ty(wb), Con{ta, ctx},
                 ind ++ "body ")
        ++ dtr(pf, s3, mt, nt, lp, vt, U.ex_at(I.is_ex(s3), I.ir_ty(wa)),
               U.ex_at(I.is_ex(s3), I.ir_ty(wb)), I.ir_ty(wa), I.ir_ty(wb),
               Con{ta, ctx}, ind ++ "  ")
    case 1n+p T.EApp{f1, a1} T.EApp{f2, a2}:
      +pf = p
      +ff1 : U32 = f1
      +ff2 : U32 = f2
      +aa1 : U32 = a1
      +aa2 : U32 = a2
      +wa = I.whd(st, mt, lp, vt, aa1)
      +wb = I.whd(I.ir_st(wa), mt, lp, vt, aa2)
      +s3 = I.ir_st(wb)
      dline(s3, mt, nt, lp, vt, I.ir_ty(wa), I.ir_ty(wb), ctx, ind ++ "arg ")
        ++ dtr(pf, s3, mt, nt, lp, vt, U.ex_at(I.is_ex(s3), I.ir_ty(wa)),
               U.ex_at(I.is_ex(s3), I.ir_ty(wb)), I.ir_ty(wa), I.ir_ty(wb),
               ctx, ind ++ "  a ")
        ++ dtr(pf, s3, mt, nt, lp, vt, U.ex_at(I.is_ex(s3), ff1),
               U.ex_at(I.is_ex(s3), ff2), ff1, ff2, ctx, ind ++ "  f ")
    case 1n+p _ _:
      ""

# for an application node f a: infer f, whnf to a Pi, infer a, compare a's
# type with the domain the way infer's App rule does
def argchk(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
           +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +f: U32, +a: U32,
           +ctx: List<&2, U32>) -> String:
  +rf = I.infer(8192n, st, mt, nt, lp, vt, U.ex_at(I.is_ex(st), f), f, ctx)
  +wf = I.whd(I.ir_st(rf), mt, lp, vt, I.ir_ty(rf))
  +s1 = I.ir_st(wf)
  +fty : T.Ex = U.ex_at(I.is_ex(s1), I.ir_ty(wf))
  +dom : U32 = I.all_dom(fty)
  +ra = I.infer(8192n, s1, mt, nt, lp, vt, U.ex_at(I.is_ex(s1), a), a, ctx)
  +w1 = I.whd(I.ir_st(ra), mt, lp, vt, I.ir_ty(ra))
  +w2 = I.whd(I.ir_st(w1), mt, lp, vt, dom)
  +s3 = I.ir_st(w2)
  +d = I.defeq(64n, U32.is_eq(I.ir_ty(w1), I.ir_ty(w2)), s3, mt, nt, lp, vt,
               ctx, U.ex_at(I.is_ex(s3), I.ir_ty(w1)),
               U.ex_at(I.is_ex(s3), I.ir_ty(w2)))
  +s4 = I.dr_st(d)
  "    ARGCHECK defeq=" ++ tristr(I.dr_r(d)) ++ "\n"
    ++ dline(s4, mt, nt, lp, vt, I.ir_ty(w1), I.ir_ty(w2), ctx, "      top ")
    ++ dtr(6n, s4, mt, nt, lp, vt, U.ex_at(I.is_ex(s4), I.ir_ty(w1)),
           U.ex_at(I.is_ex(s4), I.ir_ty(w2)), I.ir_ty(w1), I.ir_ty(w2), ctx,
           "      ")

# descend to the innermost node whose inference fails
def wfail(fuel: Nat, +st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
          +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +x: T.Ex, +e: U32,
          +ctx: List<&2, U32>, +ind: String) -> String:
  match fuel x:
    case 0n _:
      ""
    case 1n+p T.ELam{n, t, b, bi}:
      +t2 : U32 = t
      +b2 : U32 = b
      pline(st, mt, nt, lp, vt, e, ctx, ind)
        ++ pline(st, mt, nt, lp, vt, t2, ctx, ind ++ "dom ")
        ++ wfail(p, st, mt, nt, lp, vt, U.ex_at(I.is_ex(st), b2), b2,
                 Con{t2, ctx}, ind ++ "  ")
    case 1n+p T.EAll{n, t, b, bi}:
      +pf = p
      +t2 : U32 = t
      +b2 : U32 = b
      pline(st, mt, nt, lp, vt, e, ctx, ind)
        ++ wfail(pf, st, mt, nt, lp, vt, U.ex_at(I.is_ex(st), t2), t2, ctx,
                 ind ++ "dom ")
        ++ wfail(pf, st, mt, nt, lp, vt, U.ex_at(I.is_ex(st), b2), b2,
                 Con{t2, ctx}, ind ++ "  ")
    case 1n+p T.EApp{f, a}:
      +pf = p
      +f2 : U32 = f
      +a2 : U32 = a
      pline(st, mt, nt, lp, vt, e, ctx, ind)
        ++ argchk(st, mt, nt, lp, vt, f2, a2, ctx)
        ++ wfail(pf, st, mt, nt, lp, vt, U.ex_at(I.is_ex(st), a2), a2, ctx,
                 ind ++ "arg ")
        ++ wfail(pf, st, mt, nt, lp, vt, U.ex_at(I.is_ex(st), f2), f2, ctx,
                 ind ++ "fn ")
    case 1n+p _:
      pline(st, mt, nt, lp, vt, e, ctx, ind)

# down the application spine: line per node and its argument check
def achain(fuel: Nat, +st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
           +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +x: T.Ex, +e: U32,
           +ctx: List<&2, U32>) -> String:
  match fuel x:
    case 0n _:
      ""
    case 1n+p T.EApp{f, a}:
      +f2 : U32 = f
      +a2 : U32 = a
      pline(st, mt, nt, lp, vt, e, ctx, "  ")
        ++ argchk(st, mt, nt, lp, vt, f2, a2, ctx)
        ++ achain(p, st, mt, nt, lp, vt, U.ex_at(I.is_ex(st), f2), f2, ctx)
    case 1n+p _:
      pline(st, mt, nt, lp, vt, e, ctx, "  ")

def vbody(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
          +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +e: U32, +tye: U32,
          +ctx: List<&2, U32>) -> String:
  +r = I.infer(8192n, st, mt, nt, lp, vt, U.ex_at(I.is_ex(st), e), e, ctx)
  +w1 = I.whd(I.ir_st(r), mt, lp, vt, I.ir_ty(r))
  +w2 = I.whd(I.ir_st(w1), mt, lp, vt, tye)
  +s3 = I.ir_st(w2)
  +d = I.defeq(64n, U32.is_eq(I.ir_ty(w1), I.ir_ty(w2)), s3, mt, nt, lp, vt,
               ctx, U.ex_at(I.is_ex(s3), I.ir_ty(w1)),
               U.ex_at(I.is_ex(s3), I.ir_ty(w2)))
  "body #" ++ U32.show(e) ++ " infer=" ++ okstr(I.ir_ok(r)) ++ " inferred="
    ++ tagof(U.ex_at(I.is_ex(s3), I.ir_ty(w1))) ++ " expected="
    ++ tagof(U.ex_at(I.is_ex(s3), I.ir_ty(w2))) ++ " defeq="
    ++ tristr(I.dr_r(d)) ++ "\n" ++ achain(10n, st, mt, nt, lp, vt,
                                        U.ex_at(I.is_ex(st), e), e, ctx)

# peel value lambdas against the declared Pi (tn = the whnf'd type node, ti
# its index); the type's body is whnf'd before the next step
def vpeel(fuel: Nat, +st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
          +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +x: T.Ex, +e: U32,
          +tn: T.Ex, +ti: U32, +ctx: List<&2, U32>) -> String:
  match fuel x tn:
    case 0n _ _:
      "fuel\n"
    case 1n+p T.ELam{n, t, b, bi} T.EAll{n2, t2, b2, bi2}:
      +ta : U32 = t
      +bb : U32 = b
      +tb : U32 = b2
      +w = I.whd(st, mt, lp, vt, tb)
      +s2 = I.ir_st(w)
      vpeel(p, s2, mt, nt, lp, vt, U.ex_at(I.is_ex(s2), bb), bb,
            U.ex_at(I.is_ex(s2), I.ir_ty(w)), I.ir_ty(w), Con{ta, ctx})
    case 1n+p _ _:
      vbody(st, mt, nt, lp, vt, e, ti, ctx)
        ++ "-- failure walk:\n"
        ++ wfail(8n, st, mt, nt, lp, vt, x, e, ctx, "  ")

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

def vsel(+hit: Bool, +st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
         +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +d: K.Dcl) -> String:
  match hit:
    case False{}:
      ""
    case True{}:
      +w = I.whd(st, mt, lp, vt, K.dcl_type(d))
      +s2 = I.ir_st(w)
      "== value probe, decl " ++ U32.show(K.dcl_name(d)) ++ "\n"
        ++ vpeel(64n, s2, mt, nt, lp, vt,
                 U.ex_at(I.is_ex(s2), K.dcl_value(d)), K.dcl_value(d),
                 U.ex_at(I.is_ex(s2), I.ir_ty(w)), I.ir_ty(w), Nil{})

def lastd(ds: List<&2, K.Dcl>, +acc: K.Dcl) -> K.Dcl:
  match ds:
    case Nil{}:
      acc
    case Con{head, tail}:
      lastd(tail, head)

def vreport(ds: List<&2, K.Dcl>, +st: I.IS, +mt: R.Tr<I.Meta>,
            +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
            +want: U32) -> String:
  match ds:
    case Nil{}:
      ""
    case Con{head, tail}:
      +h = head
      +hit : Bool = U32.is_eq(K.dcl_name(h), want)
      vsel(hit, st, mt, nt, lp, vt, h)
        ++ vreport(tail, st, mt, B.add_nt(h, nt), B.add_lp(h, lp),
                   B.add_vt(h, vt), want)

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
  +mt = C.build_meta(ds, ex, ln, R.TNil{})
  scan(ds, st, mt, R.TNil{}, R.TNil{}, R.TNil{}) ++ "\n"
    ++ vreport(ds, st, mt, R.TNil{}, R.TNil{}, R.TNil{},
               K.dcl_name(lastd(ds, K.DNone{})))

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
