# Differential check for the kernel machine's substitution walks (km.bend)
# against subst.bend's trie implementation, expression by expression.
#
# For every expression index e in a file this runs lift(e, c=0, d=1) and
# inst(e, j=0, v=0) through BOTH implementations and compares the results
# STRUCTURALLY (the flat side allocates different indices, so index equality
# means nothing across stores; shape equality is the contract). Prints
# "lift bad X inst bad Y of N" -- X and Y must be 0.

import Base
import ./scan.bend as S
import ./decode.bend as D
import ./term.bend as T
import ./level.bend as L
import ./store.bend as K
import ./trie.bend as R
import ./tables.bend as B
import ./subst.bend as U
import ./fstore.bend as F
import ./km.bend as M

# --- worklist pairs ---------------------------------------------------------
type TP is Data:
  TP{ti: U32, fi: U32}

type ES is Data:
  ES{ok: Bool, kids: List<&2, TP>}

type W2 is Data:
  W2{wl: List<&2, TP>, nfi: U32, badd: U32}

def feq_us(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{head, tail} Con{h2, t2}:
      U32.is_eq(head, h2) && feq_us(tail, t2)
    case _ _:
      False{}

def False2() -> ES:
  ES{False{}, Nil{}}

# same constructor, same scalar fields; children paired for the worklist
def eq_shape(x: T.Ex, y: T.Ex) -> ES:
  match x y:
    case T.EBad{} T.EBad{}:
      ES{True{}, Nil{}}
    case T.EBVar{i} T.EBVar{j}:
      ES{U32.is_eq(i, j), Nil{}}
    case T.ESort{l} T.ESort{m}:
      ES{U32.is_eq(l, m), Nil{}}
    case T.EConst{n, us} T.EConst{m, vs}:
      ES{U32.is_eq(n, m) && feq_us(us, vs), Nil{}}
    case T.EApp{f, a} T.EApp{g, b}:
      ES{True{}, Con{TP{f, g}, Con{TP{a, b}, Nil{}}}}
    case T.ELam{n, t, b, bi} T.ELam{m, u, c, b2}:
      ES{U32.is_eq(n, m) && U32.is_eq(bi, b2),
         Con{TP{t, u}, Con{TP{b, c}, Nil{}}}}
    case T.EAll{n, t, b, bi} T.EAll{m, u, c, b2}:
      ES{U32.is_eq(n, m) && U32.is_eq(bi, b2),
         Con{TP{t, u}, Con{TP{b, c}, Nil{}}}}
    case T.ELet{n, t, v, b} T.ELet{m, u, w, c}:
      ES{U32.is_eq(n, m),
         Con{TP{t, u}, Con{TP{v, w}, Con{TP{b, c}, Nil{}}}}}
    case T.EProj{tn, i, s} T.EProj{t2, j, s2}:
      ES{U32.is_eq(tn, t2) && U32.is_eq(i, j), Con{TP{s, s2}, Nil{}}}
    case T.ENat{d} T.ENat{e}:
      ES{feq_us(d, e), Nil{}}
    case T.EStr{d} T.EStr{e}:
      ES{feq_us(d, e), Nil{}}
    case _ _:
      False2()

def head_fi(wl: List<&2, TP>) -> U32:
  match wl:
    case Nil{}:
      0
    case Con{TP{ti, fi}, tail}:
      fi

def w2_wl(+w: W2) -> List<&2, TP>:
  match w:
    case W2{wl, nfi, badd}:
      wl

def w2_fi(+w: W2) -> U32:
  match w:
    case W2{wl, nfi, badd}:
      nfi

def w2_bad(+w: W2) -> U32:
  match w:
    case W2{wl, nfi, badd}:
      badd

def prep(es: ES, rest: List<&2, TP>) -> W2:
  match es:
    case ES{ok, kids}:
      +w = List.append(&2, TP, kids, rest)
      W2{w, head_fi(w), S.pick(ok, 0, 1)}

# deep compare: trie term ti against flat term (whose node for the worklist
# head arrives in `pr`), mismatches counted in `bad`
def fdq(fuel: Nat, +tt: R.Tr<T.Ex>, wl: List<&2, TP>, +bad: U32,
        pr: Array<T.Ex> & T.Ex) -> Array<T.Ex> & U32:
  match fuel wl pr:
    case 0n _ Tuple{a, nd}:
      (a, 1000000)
    case 1n+p Nil{} Tuple{a, nd}:
      (a, bad)
    case 1n+p Con{TP{ti, fi}, tail} Tuple{a, nd}:
      +w = prep(eq_shape(U.ex_at(tt, ti), nd), tail)
      fdq(p, tt, w2_wl(w), (bad + w2_bad(w) : U32),
          Array.get(T.Ex, a, w2_fi(w)))

def drive2(r: Array<T.Ex> & U32, +nx: U32) -> (Array<T.Ex> & U32) & U32:
  match r:
    case Tuple{ex, bad}:
      ((ex, nx), bad)

# one expression: compare the trie result (in sr) with the flat result (in kr)
def drive1(kr: (Array<T.Ex> & U32) & U32, +sr: U.SR) -> (Array<T.Ex> & U32) & U32:
  match kr:
    case Tuple{Tuple{ex, nx}, fi}:
      +f2 = fi
      drive2(fdq(50000000n, U.sr_t(sr), Con{TP{U.sr_i(sr), f2}, Nil{}}, 0,
                 Array.get(T.Ex, ex, f2)),
             nx)

# --- loops over every expression index --------------------------------------
def loop_lift(n: Nat, +e: U32, +ext: R.Tr<T.Ex>, +nex: U32, +acc: U32,
              kfs: (Array<T.Ex> & U32) & U32) -> U32:
  match n kfs:
    case 0n Tuple{fs, bad}:
      (acc + bad : U32)
    case 1n+p Tuple{fs, bad}:
      loop_lift(p, (e + 1 : U32), ext, nex, (acc + bad : U32),
                drive1(M.klift(100000000n, fs, e, 0, 1),
                       U.lift(256n, ext, nex, U.ex_at(ext, e), e, 0, 1)))

def loop_inst(n: Nat, +e: U32, +ext: R.Tr<T.Ex>, +nex: U32, +acc: U32,
              kfs: (Array<T.Ex> & U32) & U32) -> U32:
  match n kfs:
    case 0n Tuple{fs, bad}:
      (acc + bad : U32)
    case 1n+p Tuple{fs, bad}:
      loop_inst(p, (e + 1 : U32), ext, nex, (acc + bad : U32),
                drive1(M.kinst(100000000n, fs, e, 0, 0),
                       U.inst(256n, ext, nex, U.ex_at(ext, e), e, 0, 0)))

def fsd(+recs: List<&2, D.Rec>) -> String:
  +nex = (K.max_ex_ix(recs, 0) + 1 : U32)
  +ext = B.build_ex(recs, R.TNil{})
  "lift bad "
  ++ U32.show(loop_lift(U32.to_nat(nex), 0, ext, nex, 0,
                        ((F.fb_ex(recs,
                                  Array.new(T.Ex,
                                            Nat.add(F.fdepth(nex), 8n),
                                            T.EBad{})), nex), 0)))
  ++ " inst bad "
  ++ U32.show(loop_inst(U32.to_nat(nex), 0, ext, nex, 0,
                        ((F.fb_ex(recs,
                                  Array.new(T.Ex,
                                            Nat.add(F.fdepth(nex), 8n),
                                            T.EBad{})), nex), 0)))
  ++ " of " ++ U32.show(nex)

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
          IO.die(File, 3, "cannot read input: " ++ msg)
    case Done{value}:
      IO.pure(File, value)

def main() -> IO(Unit):
  do IO<Unit>:
    av : List<&1, String> <- IO.args()
    path : String = unwrap_arg(List.get(&1, String, av, 1n))
    oh : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    f : File <- open_or_fail(oh)
    pr : File & Result<&1, &1, U32 & String, List<&2, U32>>
      <- File.read_bytes(f, 33554432)
    bs : List<&2, U32> <- IO.pass(List<&2, U32>,
      Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, pr))
    IO.print(fsd(D.decode(bs, S.Sc.start(), D.Acc.start(), Nil{})))
