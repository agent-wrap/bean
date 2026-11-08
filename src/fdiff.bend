# Differential check: the flat Array stores (fstore.bend) against the trie
# builders (tables.bend/store.bend), index by index, over one export file.
# Prints one line: per-table mismatch counts, which must all be 0.
#
# This is M1's gate (docs/port-plan.md): the port may not proceed on a store
# whose contents differ from the one that scores 174 with WRONG:0.

import Base
import ./scan.bend as S
import ./decode.bend as D
import ./term.bend as T
import ./level.bend as L
import ./store.bend as K
import ./trie.bend as R
import ./tables.bend as B
import ./fstore.bend as F

# --- structural equality on stored values ---------------------------------
def feq_us(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{head, tail} Con{h2, t2}:
      U32.is_eq(head, h2) && feq_us(tail, t2)
    case _ _:
      False{}

def feq_at(+x: L.Atom, +y: L.Atom) -> Bool:
  match x y:
    case L.At{base, off} L.At{b2, o2}:
      U32.is_eq(base, b2) && U32.is_eq(off, o2)

def feq_ats(xs: List<&2, L.Atom>, ys: List<&2, L.Atom>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{head, tail} Con{h2, t2}:
      feq_at(head, h2) && feq_ats(tail, t2)
    case _ _:
      False{}

def feq_ln(x: L.LN, y: L.LN) -> Bool:
  match x y:
    case L.LNun{} L.LNun{}:
      True{}
    case L.LNsym{} L.LNsym{}:
      True{}
    case L.LNmax{xs} L.LNmax{ys}:
      feq_ats(xs, ys)
    case L.LNimax{a, b, off} L.LNimax{c, d, o2}:
      feq_ln(a, c) && feq_ln(b, d) && U32.is_eq(off, o2)
    case _ _:
      False{}

def feq_lvl(x: T.Lvl, y: T.Lvl) -> Bool:
  match x y:
    case T.LZero{} T.LZero{}:
      True{}
    case T.LSucc{l} T.LSucc{m}:
      U32.is_eq(l, m)
    case T.LMax{a, b} T.LMax{c, d}:
      U32.is_eq(a, c) && U32.is_eq(b, d)
    case T.LIMax{a, b} T.LIMax{c, d}:
      U32.is_eq(a, c) && U32.is_eq(b, d)
    case T.LParam{n} T.LParam{m}:
      U32.is_eq(n, m)
    case _ _:
      False{}

def feq_nm(x: T.Nm, y: T.Nm) -> Bool:
  match x y:
    case T.NAnon{} T.NAnon{}:
      True{}
    case T.NStr{pre, s} T.NStr{p2, s2}:
      U32.is_eq(pre, p2) && feq_us(s, s2)
    case T.NNum{pre, i} T.NNum{p2, i2}:
      U32.is_eq(pre, p2) && U32.is_eq(i, i2)
    case _ _:
      False{}

def feq_ex(x: T.Ex, y: T.Ex) -> Bool:
  match x y:
    case T.EBad{} T.EBad{}:
      True{}
    case T.EBVar{i} T.EBVar{j}:
      U32.is_eq(i, j)
    case T.ESort{l} T.ESort{m}:
      U32.is_eq(l, m)
    case T.EConst{n, us} T.EConst{m, vs}:
      U32.is_eq(n, m) && U32.is_eq(us, vs)
    case T.EApp{f, a} T.EApp{g, b}:
      U32.is_eq(f, g) && U32.is_eq(a, b)
    case T.ELam{n, t, b, bi} T.ELam{m, u, c, b2}:
      U32.is_eq(n, m) && U32.is_eq(t, u) && U32.is_eq(b, c)
      && U32.is_eq(bi, b2)
    case T.EAll{n, t, b, bi} T.EAll{m, u, c, b2}:
      U32.is_eq(n, m) && U32.is_eq(t, u) && U32.is_eq(b, c)
      && U32.is_eq(bi, b2)
    case T.ELet{n, t, v, b} T.ELet{m, u, w, c}:
      U32.is_eq(n, m) && U32.is_eq(t, u) && U32.is_eq(v, w)
      && U32.is_eq(b, c)
    case T.EProj{tn, i, s} T.EProj{t2, j, s2}:
      U32.is_eq(tn, t2) && U32.is_eq(i, j) && U32.is_eq(s, s2)
    case T.ENat{d} T.ENat{e}:
      U32.is_eq(d, e)
    case T.EStr{d} T.EStr{e}:
      U32.is_eq(d, e)
    case _ _:
      False{}

# --- comparison loops ------------------------------------------------------
# Each loop threads the flat array; the pending (array & flag) pair from the
# previous index is a parameter, folded into the count at entry. The flag
# convention is 1 for a mismatch.
def fcmp_ex2(r: Array<T.Ex> & T.Ex, te: T.Ex) -> Array<T.Ex> & U32:
  match r:
    case Tuple{a, fe}:
      (a, S.pick(feq_ex(fe, te), 0, 1))

def fcmp_ex(n: Nat, +i: U32, +ext: R.Tr<T.Ex>, +acc: U32,
            r: Array<T.Ex> & U32) -> U32:
  match n r:
    case 0n Tuple{a, f}:
      (acc + f : U32)
    case 1n+p Tuple{a, f}:
      fcmp_ex(p, (i + 1 : U32), ext, (acc + f : U32),
              fcmp_ex2(Array.get(T.Ex, a, i),
                       R.get(T.Ex, 64n, ext, i, T.EBad{})))

def fcmp_lv2(r: Array<T.Lvl> & T.Lvl, te: T.Lvl) -> Array<T.Lvl> & U32:
  match r:
    case Tuple{a, fe}:
      (a, S.pick(feq_lvl(fe, te), 0, 1))

def fcmp_lv(n: Nat, +i: U32, +lvt: R.Tr<T.Lvl>, +acc: U32,
            r: Array<T.Lvl> & U32) -> U32:
  match n r:
    case 0n Tuple{a, f}:
      (acc + f : U32)
    case 1n+p Tuple{a, f}:
      fcmp_lv(p, (i + 1 : U32), lvt, (acc + f : U32),
              fcmp_lv2(Array.get(T.Lvl, a, i),
                       R.get(T.Lvl, 64n, lvt, i, T.LZero{})))

def fcmp_ln2(r: Array<L.LN> & L.LN, te: L.LN) -> Array<L.LN> & U32:
  match r:
    case Tuple{a, fe}:
      (a, S.pick(feq_ln(fe, te), 0, 1))

def fcmp_ln(n: Nat, +i: U32, +lnt: R.Tr<L.LN>, +acc: U32,
            r: Array<L.LN> & U32) -> U32:
  match n r:
    case 0n Tuple{a, f}:
      (acc + f : U32)
    case 1n+p Tuple{a, f}:
      fcmp_ln(p, (i + 1 : U32), lnt, (acc + f : U32),
              fcmp_ln2(Array.get(L.LN, a, i),
                       R.get(L.LN, 64n, lnt, i, L.LNun{})))

def fcmp_nm2(r: Array<T.Nm> & T.Nm, te: T.Nm) -> Array<T.Nm> & U32:
  match r:
    case Tuple{a, fe}:
      (a, S.pick(feq_nm(fe, te), 0, 1))

def fcmp_nm(n: Nat, +i: U32, +nmt: R.Tr<T.Nm>, +acc: U32,
            r: Array<T.Nm> & U32) -> U32:
  match n r:
    case 0n Tuple{a, f}:
      (acc + f : U32)
    case 1n+p Tuple{a, f}:
      fcmp_nm(p, (i + 1 : U32), nmt, (acc + f : U32),
              fcmp_nm2(Array.get(T.Nm, a, i),
                       R.get(T.Nm, 64n, nmt, i, T.NAnon{})))

# --- driver ----------------------------------------------------------------
def fdiff_lv(st: Array<T.Lvl> & Array<L.LN>, +lvt: R.Tr<T.Lvl>,
             +lnt: R.Tr<L.LN>, +nlv: U32) -> String:
  match st:
    case Tuple{flv, fln}:
      " lv " ++ U32.show(fcmp_lv(U32.to_nat(nlv), 0, lvt, 0, (flv, 0)))
      ++ " ln " ++ U32.show(fcmp_ln(U32.to_nat(nlv), 0, lnt, 0, (fln, 0)))

def fdiff(+recs: List<&2, D.Rec>) -> String:
  +nex = (K.max_ex_ix(recs, 0) + 1 : U32)
  +nlv = (K.max_lvl_ix(recs, 0) + 1 : U32)
  +nnm = (F.max_nm_ix(recs, 0) + 1 : U32)
  +ext = B.build_ex(recs, R.TNil{})
  +lvt = B.build_lv(recs, R.TNil{})
  +lnt = B.lv_resolve(32n, U32.to_nat(nlv), lvt, R.TNil{})
  +nmt = K.build_nm(recs, R.TNil{})
  "mism ex "
  ++ U32.show(fcmp_ex(U32.to_nat(nex), 0, ext, 0,
                      (F.fb_ex(recs, Array.new(T.Ex, F.fdepth(nex),
                                               T.EBad{})), 0)))
  ++ fdiff_lv(F.flv_resolve(32n, U32.to_nat(nlv),
                            (F.fb_lv(recs, Array.new(T.Lvl, F.fdepth(nlv),
                                                     T.LZero{})),
                             Array.new(L.LN, F.fdepth(nlv), L.LNun{}))),
              lvt, lnt, nlv)
  ++ " nm "
  ++ U32.show(fcmp_nm(U32.to_nat(nnm), 0, nmt, 0,
                      (F.fb_nm(recs, Array.new(T.Nm, F.fdepth(nnm),
                                               T.NAnon{})), 0)))
  ++ " of ex=" ++ U32.show(nex) ++ " lv=" ++ U32.show(nlv)
  ++ " nm=" ++ U32.show(nnm)

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
    IO.print(fdiff(D.decode(bs, S.Sc.start(), D.Acc.start(), Nil{})))
