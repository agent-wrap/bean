# Differential check for the kernel machine's substitution walks (km.bend)
# against the trie implementations (subst.bend's lift/inst, infer.bend's
# lsubst), expression by expression.
#
# For every expression index e in a file this runs lift(e, 0, 1),
# inst(e, 0, 0) and lsubst(e, [1] -> [zero]) through BOTH implementations and
# compares the results STRUCTURALLY -- the flat side allocates different
# indices, so index equality means nothing across stores; shape equality,
# with levels compared by their normal forms, is the contract. Prints
# "lift bad X inst bad Y lsub bad Z of N" -- X, Y, Z must be 0.

import Base
import ./scan.bend as S
import ./decode.bend as D
import ./term.bend as T
import ./level.bend as L
import ./store.bend as K
import ./trie.bend as R
import ./tables.bend as B
import ./subst.bend as U
import ./infer.bend as I
import ./fstore.bend as F
import ./km.bend as M

# --- worklist pairs ---------------------------------------------------------
# isl: this pair is a LEVEL pair (compared by normal form), else an
# expression pair (compared by shape).
type TP is Data:
  TP{isl: Bool, ti: U32, fi: U32}

type ES is Data:
  ES{ok: Bool, kids: List<&2, TP>}

type W2 is Data:
  W2{wl: List<&2, TP>, nisl: Bool, nfi: U32, badd: U32}

# fetched value: an expression node or a level normal form
type FV is Data:
  FVx{x: T.Ex}
  FVl{l: L.LN}

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

def zr_bad() -> ES:
  ES{False{}, Nil{}}

def feq_us(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{head, tail} Con{h2, t2}:
      U32.is_eq(head, h2) && feq_us(tail, t2)
    case _ _:
      False{}

def eq_shape_c(+lv: ES, +n: U32, +m: U32) -> ES:
  match lv:
    case ES{ok, kids}:
      ES{ok && U32.is_eq(n, m), kids}

def zip_lv2(+rest: ES, +a: U32, +b: U32) -> ES:
  match rest:
    case ES{ok, kids}:
      ES{ok, Con{TP{True{}, a, b}, kids}}

# same constructor, same scalar fields; children paired for the worklist.
# ESort levels and EConst level arguments become LEVEL pairs.
def mk_es(+ok: Bool) -> ES:
  ES{ok, Nil{}}

# zip two level-index lists into level pairs; length mismatch is a fail
def zip_lv(xs: List<&2, U32>, ys: List<&2, U32>) -> ES:
  match xs ys:
    case Nil{} Nil{}:
      ES{True{}, Nil{}}
    case Con{head, tail} Con{h2, t2}:
      zip_lv2(zip_lv(tail, t2), head, h2)
    case _ _:
      zr_bad()

def eq_shape(x: T.Ex, y: T.Ex) -> ES:
  match x y:
    case T.EBad{} T.EBad{}:
      ES{True{}, Nil{}}
    case T.EBVar{i} T.EBVar{j}:
      ES{U32.is_eq(i, j), Nil{}}
    case T.ESort{l} T.ESort{m}:
      ES{True{}, Con{TP{True{}, l, m}, Nil{}}}
    case T.EConst{n, us} T.EConst{m, vs}:
      eq_shape_c(zip_lv(us, vs), n, m)
    case T.EApp{f, a} T.EApp{g, b}:
      ES{True{}, Con{TP{False{}, f, g}, Con{TP{False{}, a, b}, Nil{}}}}
    case T.ELam{n, t, b, bi} T.ELam{m, u, c, b2}:
      ES{U32.is_eq(n, m) && U32.is_eq(bi, b2),
         Con{TP{False{}, t, u}, Con{TP{False{}, b, c}, Nil{}}}}
    case T.EAll{n, t, b, bi} T.EAll{m, u, c, b2}:
      ES{U32.is_eq(n, m) && U32.is_eq(bi, b2),
         Con{TP{False{}, t, u}, Con{TP{False{}, b, c}, Nil{}}}}
    case T.ELet{n, t, v, b} T.ELet{m, u, w, c}:
      ES{U32.is_eq(n, m),
         Con{TP{False{}, t, u},
             Con{TP{False{}, v, w}, Con{TP{False{}, b, c}, Nil{}}}}}
    case T.EProj{tn, i, s} T.EProj{t2, j, s2}:
      ES{U32.is_eq(tn, t2) && U32.is_eq(i, j),
         Con{TP{False{}, s, s2}, Nil{}}}
    case T.ENat{d} T.ENat{e}:
      ES{feq_us(d, e), Nil{}}
    case T.EStr{d} T.EStr{e}:
      ES{feq_us(d, e), Nil{}}
    case _ _:
      zr_bad()

def w2_wl(+w: W2) -> List<&2, TP>:
  match w:
    case W2{wl, nisl, nfi, badd}:
      wl

def w2_isl(+w: W2) -> Bool:
  match w:
    case W2{wl, nisl, nfi, badd}:
      nisl

def w2_fi(+w: W2) -> U32:
  match w:
    case W2{wl, nisl, nfi, badd}:
      nfi

def w2_bad(+w: W2) -> U32:
  match w:
    case W2{wl, nisl, nfi, badd}:
      badd

def head_isl(wl: List<&2, TP>) -> Bool:
  match wl:
    case Nil{}:
      False{}
    case Con{TP{isl, ti, fi}, tail}:
      isl

def head_fi(wl: List<&2, TP>) -> U32:
  match wl:
    case Nil{}:
      0
    case Con{TP{isl, ti, fi}, tail}:
      fi

def prep(es: ES, rest: List<&2, TP>) -> W2:
  match es:
    case ES{ok, kids}:
      +w : List<&2, TP> = List.append(&2, TP, kids, rest)
      W2{w, head_isl(w), head_fi(w), S.pick(ok, 0, 1)}

# fetch the flat value for the next worklist head
def ffetch_x(pr: Array<T.Ex> & T.Ex,
             lna: Array<L.LN>) -> (Array<T.Ex> & Array<L.LN>) & FV:
  match pr:
    case Tuple{exa, nd}:
      ((exa, lna), FVx{nd})

def ffetch_l(pr: Array<L.LN> & L.LN,
             exa: Array<T.Ex>) -> (Array<T.Ex> & Array<L.LN>) & FV:
  match pr:
    case Tuple{lna, lv}:
      ((exa, lna), FVl{lv})

def ffetch_la(arrs: Array<T.Ex> & Array<L.LN>,
              +i: U32) -> (Array<T.Ex> & Array<L.LN>) & FV:
  match arrs:
    case Tuple{exa, lna}:
      ffetch_l(Array.get(L.LN, lna, i), exa)

def ffetch_xa(arrs: Array<T.Ex> & Array<L.LN>,
              +i: U32) -> (Array<T.Ex> & Array<L.LN>) & FV:
  match arrs:
    case Tuple{exa, lna}:
      ffetch_x(Array.get(T.Ex, exa, i), lna)

def ffetch(arrs: Array<T.Ex> & Array<L.LN>, +isl: Bool,
           +i: U32) -> (Array<T.Ex> & Array<L.LN>) & FV:
  match isl:
    case True{}:
      ffetch_la(arrs, i)
    case False{}:
      ffetch_xa(arrs, i)

# deep compare driven by a worklist; INVARIANT: `pr` carries the flat value
# for the worklist's head
def fdq(fuel: Nat, +tt: R.Tr<T.Ex>, +tln: R.Tr<L.LN>, wl: List<&2, TP>,
        +bad: U32,
        pr: (Array<T.Ex> & Array<L.LN>) & FV) -> (Array<T.Ex> & Array<L.LN>) & U32:
  match fuel wl pr:
    case 0n _ Tuple{arrs, fv}:
      (arrs, 1000000)
    case 1n+p Nil{} Tuple{arrs, fv}:
      (arrs, bad)
    case 1n+p Con{TP{isl, ti, fi}, tail} Tuple{arrs, FVx{nd}}:
      +w : W2 = prep(eq_shape(U.ex_at(tt, ti), nd), tail)
      fdq(p, tt, tln, w2_wl(w), (bad + w2_bad(w) : U32),
          ffetch(arrs, w2_isl(w), w2_fi(w)))
    case 1n+p Con{TP{isl, ti, fi}, tail} Tuple{arrs, FVl{lv}}:
      +w : W2 = prep(mk_es(feq_ln(R.get(L.LN, 32n, tln, ti, L.LNun{}), lv)),
                     tail)
      fdq(p, tt, tln, w2_wl(w), (bad + w2_bad(w) : U32),
          ffetch(arrs, w2_isl(w), w2_fi(w)))

def drive2(r: (Array<T.Ex> & Array<L.LN>) & U32, +nx: U32, +nlx: U32)
    -> (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & U32):
  match r:
    case Tuple{Tuple{exa, lna}, bad}:
      (((exa, nx), (lna, nlx)), bad)

# one expression: compare the trie result (index ti, under tries tt/tln)
# with the flat result (in kr)
def drive1(kr: ((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & U32,
           +tt: R.Tr<T.Ex>, +tln: R.Tr<L.LN>, +ti: U32)
    -> (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & U32):
  match kr:
    case Tuple{Tuple{Tuple{exa, nx}, Tuple{lna, nlx}}, fi}:
      +f2 : U32 = fi
      drive2(fdq(50000000n, tt, tln, Con{TP{False{}, ti, f2}, Nil{}}, 0,
                 ffetch((exa, lna), False{}, f2)),
             nx, nlx)

# --- loops over every expression index --------------------------------------
def loop_lift(n: Nat, +e: U32, +ext: R.Tr<T.Ex>, +tln: R.Tr<L.LN>,
              +nex: U32, +acc: U32,
              kfs: (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & U32)) -> U32:
  match n kfs:
    case 0n Tuple{fs, bad}:
      (acc + bad : U32)
    case 1n+p Tuple{fs, bad}:
      +r : U.SR = U.lift(256n, ext, nex, U.ex_at(ext, e), e, 0, 1)
      loop_lift(p, (e + 1 : U32), ext, tln, nex, (acc + bad : U32),
                drive1(M.klift(100000000n, fs, e, 0, 1, 256), U.sr_t(r), tln,
                       U.sr_i(r)))

def loop_inst(n: Nat, +e: U32, +ext: R.Tr<T.Ex>, +tln: R.Tr<L.LN>,
              +nex: U32, +acc: U32,
              kfs: (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & U32)) -> U32:
  match n kfs:
    case 0n Tuple{fs, bad}:
      (acc + bad : U32)
    case 1n+p Tuple{fs, bad}:
      +r : U.SR = U.inst(256n, ext, nex, U.ex_at(ext, e), e, 0, 0)
      loop_inst(p, (e + 1 : U32), ext, tln, nex, (acc + bad : U32),
                drive1(M.kinst(100000000n, fs, e, 0, 0, 256), U.sr_t(r), tln,
                       U.sr_i(r)))

# the trie-side lsubst needs a full IS; only ex/nx/lnt/nlx matter to it
def mk_is(+ext: R.Tr<T.Ex>, +tln: R.Tr<L.LN>, +nex: U32, +nlv: U32) -> I.IS:
  I.IS{ext, nex, tln, nlv, R.TNil{}, R.TNil{}, 4294967295, 4294967295,
       R.TNil{}}

def ls_ps() -> List<&2, U32>:
  Con{1, Nil{}}

def ls_qs() -> List<&2, L.LN>:
  Con{L.ln_zero(), Nil{}}

def loop_ls(n: Nat, +e: U32, +ext: R.Tr<T.Ex>, +tln: R.Tr<L.LN>,
            +nex: U32, +nlv: U32, +acc: U32, +fb: U32,
            kfs: (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & U32)) -> String:
  match n kfs:
    case 0n Tuple{fs, bad}:
      +b2 : U32 = bad
      U32.show((acc + b2 : U32)) ++ " first "
      ++ U32.show(S.pick(U32.is_eq(fb, 4294967295) && U32.is_gt(b2, 0),
                         (e - 1 : U32), fb))
    case 1n+p Tuple{fs, bad}:
      +b2 : U32 = bad
      +r : I.IR = I.lsubst(256n, mk_is(ext, tln, nex, nlv), U.ex_at(ext, e), e,
                    ls_ps(), ls_qs())
      loop_ls(p, (e + 1 : U32), ext, tln, nex, nlv, (acc + b2 : U32),
              S.pick(U32.is_eq(fb, 4294967295) && U32.is_gt(b2, 0),
                     (e - 1 : U32), fb),
              drive1(M.klsubst(100000000n, fs, e, ls_ps(), ls_qs(), 256),
                     I.is_ex(I.ir_st(r)), I.is_lnt(I.ir_st(r)),
                     I.ir_ty(r)))

# --- drivers -----------------------------------------------------------------
def flat_ln(st: Array<T.Lvl> & Array<L.LN>) -> Array<L.LN>:
  match st:
    case Tuple{lv, ln}:
      ln

def fresh_flat(+recs: List<&2, D.Rec>, +nex: U32,
               +nlv: U32) -> ((Array<T.Ex> & U32) & (Array<L.LN> & U32)):
  ((F.fb_ex(recs, Array.new(T.Ex, Nat.add(F.fdepth(nex), 12n), T.EBad{})),
    nex),
   (flat_ln(F.flv_resolve(32n, U32.to_nat(nlv),
                          (F.fb_lv(recs,
                                   Array.new(T.Lvl,
                                             Nat.add(F.fdepth(nlv), 8n),
                                             T.LZero{})),
                           Array.new(L.LN, 22n,
                                     L.LNun{})))),
    nlv))

def fsd(+recs: List<&2, D.Rec>) -> String:
  +nex = (K.max_ex_ix(recs, 0) + 1 : U32)
  +nlv = (K.max_lvl_ix(recs, 0) + 1 : U32)
  +ext = B.build_ex(recs, R.TNil{})
  +lvt = B.build_lv(recs, R.TNil{})
  +tln = B.lv_resolve(32n, U32.to_nat(nlv), lvt, R.TNil{})
  "lift bad "
  ++ U32.show(loop_lift(U32.to_nat(nex), 0, ext, tln, nex, 0,
                        (fresh_flat(recs, nex, nlv), 0)))
  ++ " inst bad "
  ++ U32.show(loop_inst(U32.to_nat(nex), 0, ext, tln, nex, 0,
                        (fresh_flat(recs, nex, nlv), 0)))
  ++ " lsub bad "
  ++ loop_ls(U32.to_nat(nex), 0, ext, tln, nex, nlv, 0, 4294967295,
             (fresh_flat(recs, nex, nlv), 0))
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
