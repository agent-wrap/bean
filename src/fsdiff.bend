# Differential check for the kernel machine's substitution walks (km.bend)
# against the trie implementations (subst.bend's lift/inst, infer.bend's
# lsubst), expression by expression.
#
# For every expression index e in a file this runs lift(e, 0, 1),
# inst(e, 0, 0) and lsubst(e, [1] -> [zero]) through BOTH implementations and
# compares the results STRUCTURALLY -- the flat side allocates different
# indices, so index equality means nothing across stores; shape equality,
# with levels compared by their normal forms, is the contract. Prints
# "lift bad X inst bad Y lsub bad Z first E of N" -- X, Y, Z must be 0.

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
import ./check.bend as C
import ./fstore.bend as F
import ./km.bend as M

# --- worklist pairs (both sides' levels are tries, so levels resolve inline)
type TP is Data:
  TP{ti: U32, fi: U32}

type ES is Data:
  ES{ok: Bool, kids: List<&2, TP>}

type W2 is Data:
  W2{wl: List<&2, TP>, nfi: U32, badd: U32}

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

def feq_us(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{head, tail} Con{h2, t2}:
      U32.is_eq(head, h2) && feq_us(tail, t2)
    case _ _:
      False{}

# level-INDEX lists compared by the normal forms the two tries hold
def feq_lvls(xs: List<&2, U32>, ys: List<&2, U32>, +tln: R.Tr<L.LN>,
             +flnt: R.Tr<L.LN>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{head, tail} Con{h2, t2}:
      feq_ln(R.get(L.LN, 32n, tln, head, L.LNun{}),
             R.get(L.LN, 32n, flnt, h2, L.LNun{}))
      && feq_lvls(tail, t2, tln, flnt)
    case _ _:
      False{}

def zr_bad() -> ES:
  ES{False{}, Nil{}}

# same constructor, same scalar fields, levels by normal form; expression
# children paired for the worklist
def eq_shape(x: T.Ex, y: T.Ex, +tln: R.Tr<L.LN>, +flnt: R.Tr<L.LN>) -> ES:
  match x y:
    case T.EBad{} T.EBad{}:
      ES{True{}, Nil{}}
    case T.EBVar{i} T.EBVar{j}:
      ES{U32.is_eq(i, j), Nil{}}
    case T.ESort{l} T.ESort{m}:
      ES{feq_ln(R.get(L.LN, 32n, tln, l, L.LNun{}),
                R.get(L.LN, 32n, flnt, m, L.LNun{})), Nil{}}
    case T.EConst{n, us} T.EConst{m, vs}:
      ES{U32.is_eq(n, m) && feq_lvls(us, vs, tln, flnt), Nil{}}
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
      zr_bad()

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
      +w : List<&2, TP> = List.append(&2, TP, kids, rest)
      W2{w, head_fi(w), S.pick(ok, 0, 1)}

# deep compare: trie term ti against flat term (whose node for the worklist
# head arrives in `pr`), mismatches counted in `bad`
def fdq(fuel: Nat, +tt: R.Tr<T.Ex>, +tln: R.Tr<L.LN>, +flnt: R.Tr<L.LN>,
        wl: List<&2, TP>, +bad: U32,
        pr: Array<T.Ex> & T.Ex) -> Array<T.Ex> & U32:
  match fuel wl pr:
    case 0n _ Tuple{a, nd}:
      (a, 1000000)
    case 1n+p Nil{} Tuple{a, nd}:
      (a, bad)
    case 1n+p Con{TP{ti, fi}, tail} Tuple{a, nd}:
      +w : W2 = prep(eq_shape(U.ex_at(tt, ti), nd, tln, flnt), tail)
      fdq(p, tt, tln, flnt, w2_wl(w), (bad + w2_bad(w) : U32),
          Array.get(T.Ex, a, w2_fi(w)))

def drive3(r: Array<T.Ex> & U32, +nx: U32, +flnt: R.Tr<L.LN>,
           +fnlx: U32, +fwm: R.Tr<U32>) -> ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>):
  match r:
    case Tuple{ex, bad}:
      (((ex, nx), bad), ((flnt, fnlx), fwm))

def drive1(kr: ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>),
           +tt: R.Tr<T.Ex>, +tln: R.Tr<L.LN>, +ti: U32)
    -> ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>):
  match kr:
    case Tuple{Tuple{Tuple{exa, nx}, fi}, Tuple{Tuple{flnt, fnlx}, fwm}}:
      +f2 : U32 = fi
      +fl : R.Tr<L.LN> = flnt
      drive3(fdq(50000000n, tt, tln, fl, Con{TP{ti, f2}, Nil{}}, 0,
                 Array.get(T.Ex, exa, f2)),
             nx, fl, fnlx, fwm)

# --- loops over every expression index --------------------------------------
def loop_lift(n: Nat, +e: U32, +ext: R.Tr<T.Ex>, +tln: R.Tr<L.LN>,
              +nex: U32, +acc: U32,
              kfs: ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>)) -> U32:
  match n kfs:
    case 0n Tuple{Tuple{fs, bad}, lv}:
      (acc + bad : U32)
    case 1n+p Tuple{Tuple{fs, bad}, Tuple{Tuple{flnt, fnlx}, fwm}}:
      +r : U.SR = U.lift(256n, ext, nex, U.ex_at(ext, e), e, 0, 1)
      loop_lift(p, (e + 1 : U32), ext, tln, nex, (acc + bad : U32),
                drive1(M.klift(100000000n, fs, flnt, fnlx, e, 0, 1, 256),
                       U.sr_t(r), tln, U.sr_i(r)))

def loop_inst(n: Nat, +e: U32, +ext: R.Tr<T.Ex>, +tln: R.Tr<L.LN>,
              +nex: U32, +acc: U32,
              kfs: ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>)) -> U32:
  match n kfs:
    case 0n Tuple{Tuple{fs, bad}, lv}:
      (acc + bad : U32)
    case 1n+p Tuple{Tuple{fs, bad}, Tuple{Tuple{flnt, fnlx}, fwm}}:
      +r : U.SR = U.inst(256n, ext, nex, U.ex_at(ext, e), e, 0, 0)
      loop_inst(p, (e + 1 : U32), ext, tln, nex, (acc + bad : U32),
                drive1(M.kinst(100000000n, fs, flnt, fnlx, e, 0, 0, 256),
                       U.sr_t(r), tln, U.sr_i(r)))

# the trie-side lsubst needs a full IS; only ex/nx/lnt/nlx matter to it
def mk_is(+ext: R.Tr<T.Ex>, +tln: R.Tr<L.LN>, +qt: R.Tr<U32>, +natn: U32,
          +nex: U32, +nlv: U32) -> I.IS:
  I.IS{ext, nex, tln, nlv, R.TNil{}, R.TNil{}, natn, 4294967295, qt}

def ls_ps() -> List<&2, U32>:
  Con{1, Nil{}}

def ls_qs() -> List<&2, L.LN>:
  Con{L.ln_zero(), Nil{}}

def loop_ls(n: Nat, +e: U32, +ext: R.Tr<T.Ex>, +tln: R.Tr<L.LN>,
            +nex: U32, +nlv: U32, +acc: U32, +fb: U32,
            kfs: ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>)) -> String:
  match n kfs:
    case 0n Tuple{Tuple{fs, bad}, lv}:
      +b2 : U32 = bad
      U32.show((acc + b2 : U32)) ++ " first "
      ++ U32.show(S.pick(U32.is_eq(fb, 4294967295) && U32.is_gt(b2, 0),
                         (e - 1 : U32), fb))
    case 1n+p Tuple{Tuple{fs, bad}, Tuple{Tuple{flnt, fnlx}, fwm}}:
      +b2 : U32 = bad
      +r : I.IR = I.lsubst(256n, mk_is(ext, tln, R.TNil{}, 4294967295, nex,
                                       nlv),
                           U.ex_at(ext, e), e, ls_ps(), ls_qs())
      loop_ls(p, (e + 1 : U32), ext, tln, nex, nlv, (acc + b2 : U32),
              S.pick(U32.is_eq(fb, 4294967295) && U32.is_gt(b2, 0),
                     (e - 1 : U32), fb),
              drive1(M.klsubst(100000000n, fs, flnt, fnlx, e, ls_ps(),
                               ls_qs(), 256),
                     I.is_ex(I.ir_st(r)), I.is_lnt(I.ir_st(r)),
                     I.ir_ty(r)))

def loop_wh(n: Nat, +e: U32, +ext: R.Tr<T.Ex>, +tln: R.Tr<L.LN>,
            +mt: R.Tr<I.Meta>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
            +qt: R.Tr<U32>, +natn: U32, +ntt: R.Tr<U32>,
            +nex: U32, +nlv: U32, +acc: U32, +fb: U32,
            kfs: ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>)) -> String:
  match n kfs:
    case 0n Tuple{Tuple{fs, bad}, lv}:
      +b2 : U32 = bad
      U32.show((acc + b2 : U32)) ++ " first "
      ++ U32.show(S.pick(U32.is_eq(fb, 4294967295) && U32.is_gt(b2, 0),
                         (e - 1 : U32), fb))
    case 1n+p Tuple{Tuple{fs, bad}, Tuple{Tuple{flnt, fnlx}, fwm}}:
      +b2 : U32 = bad
      +r : I.IR = I.whnf(256n, True{}, mk_is(ext, tln, qt, natn, nex, nlv),
                         mt, lp, vt, U.ex_at(ext, e), e, Nil{})
      loop_wh(p, (e + 1 : U32), ext, tln, mt, lp, vt, qt, natn, ntt, nex,
              nlv,
              (acc + b2 : U32),
              S.pick(U32.is_eq(fb, 4294967295) && U32.is_gt(b2, 0),
                     (e - 1 : U32), fb),
              drive1(M.kwhnf(100000000n, fs, flnt, fnlx, mt, lp, vt, qt,
                             natn, fwm, ntt, e, True{}, 256),
                     I.is_ex(I.ir_st(r)), I.is_lnt(I.ir_st(r)),
                     I.ir_ty(r)))

# --- the universe oracle, machine vs trie ------------------------------------
def fsl2(kfs: ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>),
         +bad: U32) -> (Array<T.Ex> & U32) & U32:
  match kfs:
    case Tuple{Tuple{fs, ok}, lv}:
      (fs, (bad + (1 - ok : U32) : U32))

def loop_sl2(n: Nat, +e: U32, +ext: R.Tr<T.Ex>, +tln: R.Tr<L.LN>,
             +ntt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +acc: U32,
             pr: (Array<T.Ex> & U32) & U32) -> U32:
  match n pr:
    case 0n Tuple{fs, bad}:
      (acc + bad : U32)
    case 1n+p Tuple{fs, bad}:
      loop_sl2(p, (e + 1 : U32), ext, tln, ntt, lp, (acc + bad : U32),
               fsl2(M.ksl_test(100000000n, fs, tln, 0, lp, ntt, e, Nil{},
                               I.sl(256n, ext, tln, ntt, lp,
                                    U.ex_at(ext, e), Nil{})),
                    0))

# --- defeq: the machine against the REAL I.defeq ----------------------------
def tri_u32(+t: L.Tri) -> U32:
  S.pick(L.tri_is_yes(t), 0, S.pick(L.tri_is_no(t), 1, 2))

def dq_fold(kfs: ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>),
            +want: U32) -> (Array<T.Ex> & U32) & U32:
  match kfs:
    case Tuple{Tuple{fs, got}, lv}:
      (fs, S.pick(U32.is_eq(got, want), 0, 1))

def loop_dq(n: Nat, +e: U32, +ext: R.Tr<T.Ex>, +tln: R.Tr<L.LN>,
            +mt: R.Tr<I.Meta>, +ntt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>,
            +vt: R.Tr<U32>, +qt: R.Tr<U32>, +natn: U32, +nex: U32,
            +nlv: U32, +acc: U32, +fb: U32,
            pr: (Array<T.Ex> & U32) & U32) -> String:
  match n pr:
    case 0n Tuple{fs, bad}:
      +b2 : U32 = bad
      U32.show((acc + b2 : U32)) ++ " first "
      ++ U32.show(S.pick(U32.is_eq(fb, 4294967295) && U32.is_gt(b2, 0),
                         (e - 1 : U32), fb))
    case 1n+p Tuple{fs, bad}:
      +b2 : U32 = bad
      +y : U32 = S.pick(U32.is_lt((e + 1 : U32), nex), (e + 1 : U32), 0)
      +ld : I.DR = I.defeq(256n, False{},
                           mk_is(ext, tln, qt, natn, nex, nlv), mt, ntt,
                           lp, vt, Nil{}, U.ex_at(ext, e),
                           U.ex_at(ext, y))
      loop_dq(p, (e + 1 : U32), ext, tln, mt, ntt, lp, vt, qt, natn, nex,
              nlv, (acc + b2 : U32),
              S.pick(U32.is_eq(fb, 4294967295) && U32.is_gt(b2, 0),
                     (e - 1 : U32), fb),
              dq_fold(M.kdefeq(100000000n, fs, tln, nlv, mt, lp, vt, qt,
                               natn, R.TNil{}, ntt, e, y, Nil{}, False{},
                               256),
                      tri_u32(I.dr_r(ld))))

# --- infer: the machine against the REAL I.infer ------------------------------
# The machine result encodes (ty*2 + ok). The gate compares the ok bit, the
# sentinel class of ty (bad / ill-typed / real), and for real types the
# STRUCTURE via the deep walker.
def pick_tps(+z: Bool, +x: List<&2, TP>, +y: List<&2, TP>)
    -> List<&2, TP>:
  match z:
    case True{}:
      x
    case False{}:
      y

def inf_class(+t: U32) -> U32:
  S.pick(U32.is_eq(t, 4294967295), 0,
         S.pick(U32.is_eq(t, 4294967294), 1, 2))

def inf_fold2(r: Array<T.Ex> & U32, +nx: U32,
              +shallow: Bool) -> (Array<T.Ex> & U32) & U32:
  match r:
    case Tuple{ex, bad}:
      ((ex, nx), S.pick(shallow && U32.is_eq(bad, 0), 0, 1))

def inf_fold(kfs: ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>),
             +wantty: U32, +wantok: Bool, +tt: R.Tr<T.Ex>,
             +tln: R.Tr<L.LN>) -> (Array<T.Ex> & U32) & U32:
  match kfs:
    case Tuple{Tuple{Tuple{exa, nx}, got}, Tuple{Tuple{flnt, fnlx}, fwm}}:
      +g2 : U32 = got
      +gok : Bool = U32.is_eq((g2 % 2 : U32), 1)
      +gty : U32 = S.pick(U32.is_eq((g2 / 2 : U32), 2000000000),
                          4294967295,
                          S.pick(U32.is_eq((g2 / 2 : U32), 2000000001),
                                 4294967294, (g2 / 2 : U32)))
      +gt2 : U32 = gty
      +w2 : U32 = wantty
      +okmatch : Bool = U32.is_eq(S.pick(gok, 1, 0),
                                  S.pick(wantok, 1, 0))
      +clmatch : Bool = U32.is_eq(inf_class(gt2), inf_class(w2))
      +deep : Bool = U32.is_eq(inf_class(gt2), 2)
                     && U32.is_eq(inf_class(w2), 2)
      inf_fold2(fdq(50000000n, tt, tln, flnt,
                    pick_tps(deep, Con{TP{w2, gt2}, Nil{}}, Nil{}), 0,
                    Array.get(T.Ex, exa, S.pick(deep, gt2, 0))),
                nx, okmatch && clmatch)

def loop_inf(n: Nat, +e: U32, +ext: R.Tr<T.Ex>, +tln: R.Tr<L.LN>,
             +mt: R.Tr<I.Meta>, +ntt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>,
             +vt: R.Tr<U32>, +qt: R.Tr<U32>, +natn: U32, +nex: U32,
             +nlv: U32, +acc: U32, +fb: U32,
             pr: (Array<T.Ex> & U32) & U32) -> String:
  match n pr:
    case 0n Tuple{fs, bad}:
      +b2 : U32 = bad
      U32.show((acc + b2 : U32)) ++ " first "
      ++ U32.show(S.pick(U32.is_eq(fb, 4294967295) && U32.is_gt(b2, 0),
                         (e - 1 : U32), fb))
    case 1n+p Tuple{fs, bad}:
      +b2 : U32 = bad
      +r : I.IR = I.infer(256n, mk_is(ext, tln, qt, natn, nex, nlv), mt,
                          ntt, lp, vt, U.ex_at(ext, e), e, Nil{})
      loop_inf(p, (e + 1 : U32), ext, tln, mt, ntt, lp, vt, qt, natn, nex,
               nlv, (acc + b2 : U32),
               S.pick(U32.is_eq(fb, 4294967295) && U32.is_gt(b2, 0),
                      (e - 1 : U32), fb),
               inf_fold(M.kinfer(100000000n, fs, tln, nlv, mt, lp, vt, qt,
                                 natn, R.TNil{}, ntt, e, Nil{}, 256),
                        I.ir_ty(r), I.ir_ok(r), I.is_ex(I.ir_st(r)),
                        I.is_lnt(I.ir_st(r))))

# --- drivers -----------------------------------------------------------------
def fresh_flat(+recs: List<&2, D.Rec>, +nex: U32, +tln: R.Tr<L.LN>,
               +nlv: U32) -> ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>):
  (((F.fb_ex(recs, Array.new(T.Ex, Nat.add(F.fdepth(nex), 12n), T.EBad{})),
     nex), 0),
   ((tln, nlv), R.TNil{}))

def fst_flat(r: ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>))
    -> Array<T.Ex> & U32:
  match r:
    case Tuple{Tuple{fs, z}, lv}:
      fs

def fsd(+recs: List<&2, D.Rec>) -> String:
  +nex = (K.max_ex_ix(recs, 0) + 1 : U32)
  +nlv = (K.max_lvl_ix(recs, 0) + 1 : U32)
  +ext = B.build_ex(recs, R.TNil{})
  +lvt = B.build_lv(recs, R.TNil{})
  +tln = B.lv_resolve(32n, U32.to_nat(nlv), lvt, R.TNil{})
  +ds = K.decls_of(recs, Nil{})
  +vt = B.build_vt(ds, R.TNil{})
  +lp = B.build_lp(ds, R.TNil{})
  +mt = C.build_meta(ds, ext, tln, R.TNil{})
  +qt = K.build_wk2(recs, R.TNil{})
  +natn = K.find_name(recs, [78, 97, 116], 4294967295)
  +ntt = B.build_nt(ds, R.TNil{})
  "lift bad "
  ++ U32.show(loop_lift(U32.to_nat(nex), 0, ext, tln, nex, 0,
                        fresh_flat(recs, nex, tln, nlv)))
  ++ " inst bad "
  ++ U32.show(loop_inst(U32.to_nat(nex), 0, ext, tln, nex, 0,
                        fresh_flat(recs, nex, tln, nlv)))
  ++ " lsub bad "
  ++ loop_ls(U32.to_nat(nex), 0, ext, tln, nex, nlv, 0, 4294967295,
             fresh_flat(recs, nex, tln, nlv))
  ++ " wh bad "
  ++ loop_wh(U32.to_nat(U32.min(nex, 1500)), 0, ext, tln, mt, lp, vt, qt,
             natn, ntt, nex, nlv, 0, 4294967295,
             fresh_flat(recs, nex, tln, nlv))
  ++ " sl bad "
  ++ U32.show(loop_sl2(U32.to_nat(nex), 0, ext, tln, ntt, lp, 0,
                       (fst_flat(fresh_flat(recs, nex, tln, nlv)), 0)))
  ++ " dq bad "
  ++ loop_dq(U32.to_nat(U32.min(nex, 1200)), 0, ext, tln, mt, ntt, lp, vt,
             qt, natn, nex, nlv, 0, 4294967295,
             (fst_flat(fresh_flat(recs, nex, tln, nlv)), 0))
  ++ " inf bad "
  ++ loop_inf(U32.to_nat(U32.min(nex, 1200)), 0, ext, tln, mt, ntt, lp,
              vt, qt, natn, nex, nlv, 0, 4294967295,
              (fst_flat(fresh_flat(recs, nex, tln, nlv)), 0))
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
