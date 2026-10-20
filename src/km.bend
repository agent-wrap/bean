# The kernel machine over the flat store -- M2 of docs/port-plan.md.
#
# Architecture: ONLY the expression store needs the flat Array (Type-kinded,
# one owner): it flows POSITIONALLY inside `tin`, and every Array op's pair
# re-enters via a parameter. Everything Data-kinded -- the level trie lnt and
# its next index nlx, the Meta/value/lparam tables, frames, lists -- threads
# as ordinary reusable parameters, exactly as in the old kernel. Control that
# must resume after a sub-walk or sub-reduction is a FRAME on an explicit
# stack, dispatched by the entry match.
#
# v4 adds weak head normal form (beta, zeta, delta via lsubst, projection
# reduction) on top of the three substitution walks. Depth fuel is part of
# the SEMANTICS (the old code keeps the subtree / rebuilds at fuel 0); it
# rides in frames and resets to 256 exactly where the old code resets.
#
# The machine register `tin` is ((store & MSG) & ri): MSG carries what the
# previous transition produced -- a fetched node (MX), a collected spine
# (MSP), or nothing (MN).

import Base
import ./scan.bend as S
import ./term.bend as T
import ./level.bend as L
import ./trie.bend as R
import ./subst.bend as U
import ./infer.bend as I

# --- walk parameters ---------------------------------------------------------
# op 0 = lift (c = cutoff, d = shift), 1 = inst (c = target, v = value),
# 2 = lsubst (ps = level-param names, qs = replacement normal forms).
type WP is Data:
  WP{op: U32, c: U32, d: U32, v: U32, ps: List<&2, U32>, qs: List<&2, L.LN>,
     fu: U32}

def wp_op(+w: WP) -> U32:
  match w:
    case WP{op, c, d, v, ps, qs, fu}:
      op

def wp_c(+w: WP) -> U32:
  match w:
    case WP{op, c, d, v, ps, qs, fu}:
      c

def wp_d(+w: WP) -> U32:
  match w:
    case WP{op, c, d, v, ps, qs, fu}:
      d

def wp_v(+w: WP) -> U32:
  match w:
    case WP{op, c, d, v, ps, qs, fu}:
      v

def wp_ps(+w: WP) -> List<&2, U32>:
  match w:
    case WP{op, c, d, v, ps, qs, fu}:
      ps

def wp_qs(+w: WP) -> List<&2, L.LN>:
  match w:
    case WP{op, c, d, v, ps, qs, fu}:
      qs

def wp_fu(+w: WP) -> U32:
  match w:
    case WP{op, c, d, v, ps, qs, fu}:
      fu

# entering a binder bumps lift's cutoff and inst's target; lsubst ignores c
def wp_bump(+w: WP) -> WP:
  match w:
    case WP{op, c, d, v, ps, qs, fu}:
      WP{op, (c + 1 : U32), d, v, ps, qs, fu}

# --- the machine's message register ------------------------------------------
type MG is Data:
  MX{x: T.Ex}
  MSP{hd: T.Ex, sargs: List<&2, U32>}
  MTri{t: L.Tri}
  # a constructor field type's telescope: binder count, binder types
  # (innermost first), and the result type's spine arguments
  MIH{q: U32, doms: List<&2, U32>, eb: List<&2, U32>}
  MN{}

# --- frames ----------------------------------------------------------------
type KF is Data:
  KEvL{c: U32, d: U32, e: U32, fu: U32}
  KEvI{c: U32, v: U32, e: U32, fu: U32}
  KEvS{ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32, fu: U32}
  # depth fuel exhausted: keep e untouched (the trie walks' `case 0n`)
  KKp{e: U32}
  # after the bvar-eq sentinel walk: pick the real answer for an inst bvar
  KBvI{iseq: Bool, isgt: Bool, i: U32, e: U32}
  KAp2{wp: WP, e: U32, f0: U32, a0: U32}
  KAp3{e: U32, f0: U32, a0: U32, r1: U32}
  KLm2{wp: WP, e: U32, n: U32, t0: U32, b0: U32, bi: U32}
  KLm3{e: U32, n: U32, t0: U32, b0: U32, bi: U32, r1: U32}
  KAl2{wp: WP, e: U32, n: U32, t0: U32, b0: U32, bi: U32}
  KAl3{e: U32, n: U32, t0: U32, b0: U32, bi: U32, r1: U32}
  KLt2{wp: WP, e: U32, n: U32, t0: U32, v0: U32, b0: U32}
  KLt3{wp: WP, e: U32, n: U32, t0: U32, v0: U32, b0: U32, r1: U32}
  KLt4{e: U32, n: U32, t0: U32, v0: U32, b0: U32, r1: U32, r2: U32}
  KPj2{e: U32, tn: U32, ix: U32, s0: U32}
  # ---- weak head normal form ----
  # evaluate the fetched node under the arg spine
  WEv{delta: Bool, e: U32, args: List<&2, U32>, fu: U32}
  # whnf fuel exhausted: rebuild the spine over e
  WRb{e: U32, args: List<&2, U32>}
  # a substitution walk finished; whnf its result under the spine
  WCont{delta: Bool, args: List<&2, U32>, fu: U32}
  # branch point for delta: unfold (lsubst the value) or rebuild
  WDelGo{can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
         qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32}
  # the struct of a projection finished reducing; collect its spine
  WPrj{delta: Bool, e: U32, tn: U32, idx: U32, args: List<&2, U32>, fu: U32}
  # spine collected; decide whether the head is the matching constructor
  WPrjS{delta: Bool, e: U32, tn: U32, idx: U32, args: List<&2, U32>,
        fu: U32}
  # branch point for projection reduction: take the field or rebuild
  WPrjGo{okp: Bool, delta: Bool, e: U32, fld: U32, args: List<&2, U32>,
         fu: U32}
  # ---- telescope peel (infer.bend's peel_tele), reused by K and iota ----
  # expect MX of the current type node; instantiate its codomain per value
  WPlE{tyi: U32, vals: List<&2, U32>}
  # an instantiation finished; fetch the new type node and continue peeling
  WPlC{vals: List<&2, U32>}
  # ---- the EConst reduction pipeline (K-like, unit-eta, delta) ----
  # phase 1 gate: K-like reduction applies?
  WPh1{iskr: Bool, isue: Bool, can: Bool, delta: Bool, vi: U32,
       ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32, args: List<&2, U32>,
       fu: U32, pp: U32, mn: U32, mk: U32, rcty: U32, cn: U32, p5: P5}
  # peel of the recursor's constructor type finished (ri = peeled type)
  WK2{isue: Bool, can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
      qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32, pp: U32,
      mn: U32, mk: U32, cn: U32, p5: P5}
  # spine of the peeled type collected; compare expected vs given indices
  WK3{pok: Bool, isue: Bool, can: Bool, delta: Bool, vi: U32,
      ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32, args: List<&2, U32>,
      fu: U32, pp: U32, mn: U32, mk: U32, cn: U32, p5: P5}
  # the index comparison's verdict arrives here (MTri)
  WK4{pok: Bool, isue: Bool, can: Bool, delta: Bool, vi: U32,
      ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32, args: List<&2, U32>,
      fu: U32, pp: U32, mn: U32, mk: U32, cn: U32, p5: P5}
  # index comparison answered; fire K or fall through
  WKGo{kok: Bool, isue: Bool, can: Bool, delta: Bool, vi: U32,
       ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32, args: List<&2, U32>,
       fu: U32, pp: U32, mn: U32, mk: U32, cn: U32, p5: P5}
  # phase 2 gate: unit-like structure eta
  WPh2{isue: Bool, can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
       qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32, pp: U32,
       mn: U32, cn: U32, p5: P5}
  # phase 3: literal arithmetic (Nat.add/sub/ble on two literals)
  WPh3{isar: Bool, aw: U32, isq: Bool, qneed: U32, can: Bool, delta: Bool,
       vi: U32, ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32,
       args: List<&2, U32>, fu: U32, p5: P5}
  WLa{aw: U32, isq: Bool, qneed: U32, can: Bool, delta: Bool, vi: U32,
      ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32, args: List<&2, U32>,
      fu: U32, p5: P5}
  WLb{r0: U32, aw: U32, isq: Bool, qneed: U32, can: Bool, delta: Bool,
      vi: U32, ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32,
      args: List<&2, U32>, fu: U32, p5: P5}
  WLc{r1: U32, aw: U32, isq: Bool, qneed: U32, can: Bool, delta: Bool,
      vi: U32, ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32,
      args: List<&2, U32>, fu: U32, p5: P5}
  WLd{na: T.Ex, aw: U32, isq: Bool, qneed: U32, can: Bool, delta: Bool,
      vi: U32, ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32,
      args: List<&2, U32>, fu: U32, p5: P5}
  WLGo{arok: Bool, aw: U32, da: List<&2, U32>, db: List<&2, U32>,
       isq: Bool, qneed: U32, can: Bool, delta: Bool, vi: U32,
       ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32, args: List<&2, U32>,
       fu: U32, p5: P5}
  # phase 4: quotient reduction (Quot.lift / Quot.ind on Quot.mk)
  WPh4{isq: Bool, qneed: U32, can: Bool, delta: Bool, vi: U32,
       ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32, args: List<&2, U32>,
       fu: U32, p5: P5}
  WQ1{qneed: U32, can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
      qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32, p5: P5}
  WQ2{qneed: U32, can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
      qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32, p5: P5}
  WQGo{qok: Bool, fv: U32, vv: U32, qneed: U32, can: Bool, delta: Bool,
       vi: U32, ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32,
       args: List<&2, U32>, fu: U32, p5: P5}
  # ---- phase 5: iota ----
  WPh5{p5: P5, can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
       qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32}
  WI1{need: U32, ind: U32, pp: U32, mk: U32, cn: U32, us: List<&2, U32>,
      can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
      qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32}
  WI2{need: U32, ind: U32, pp: U32, mk: U32, cn: U32, us: List<&2, U32>,
      can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
      qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32}
  WI2Go{islit: Bool, d: List<&2, U32>, orig: U32, need: U32, ind: U32,
        pp: U32, mk: U32, cn: U32, us: List<&2, U32>, can: Bool,
        delta: Bool, vi: U32, ps: List<&2, U32>, qs: List<&2, L.LN>,
        e: U32, args: List<&2, U32>, fu: U32}
  WI2b{need: U32, ind: U32, pp: U32, mk: U32, cn: U32, us: List<&2, U32>,
       can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
       qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32}
  WI3{need: U32, ind: U32, pp: U32, mk: U32, cn: U32, us: List<&2, U32>,
      can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
      qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32}
  WIGo{ok2: Bool, fields: List<&2, U32>, recsl: List<&2, U32>, ci: U32,
       ccty: U32, need: U32, pp: U32, mk: U32, cn: U32,
       us: List<&2, U32>, can: Bool, delta: Bool, vi: U32,
       ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32,
       args: List<&2, U32>, fu: U32}
  WIhNext{ic: IC}
  WIhPe{h: U32, ic: IC}
  WIhFty{h: U32, ic: IC}
  WIhScanned{h: U32, ic: IC}
  WIhL{todo: List<&2, U32>, amt: U32, lacc: List<&2, U32>,
       ebni: List<&2, U32>, doms: List<&2, U32>, ic: IC}
  WIhB{ic: IC}

type KS is Data:
  KNil{}
  KCon{f: KF, k: KS}

# fresh-level results of a level-list substitution (all Data)
type LVS is Data:
  LVS{t: R.Tr<L.LN>, nx: U32, xs: List<&2, U32>}

def lvs_t(+r: LVS) -> R.Tr<L.LN>:
  match r:
    case LVS{t, nx, xs}:
      t

def lvs_nx(+r: LVS) -> U32:
  match r:
    case LVS{t, nx, xs}:
      nx

def lvs_xs(+r: LVS) -> List<&2, U32>:
  match r:
    case LVS{t, nx, xs}:
      xs

# iota context, threaded opaquely through the earlier EConst phases
type P5 is Data:
  P5{canio: Bool, need: U32, ind: U32, pp: U32, mk: U32, cn: U32,
     us: List<&2, U32>}

# the inductive-hypothesis builder's loop context
type IC is Data:
  IC{poss: List<&2, U32>, cn: U32, us: List<&2, U32>, pre: List<&2, U32>,
     fields: List<&2, U32>, ccty: U32, pp: U32, ni: U32,
     acc: List<&2, U32>, ci: U32, need: U32, can: Bool, delta: Bool,
     vi: U32, ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32,
     args: List<&2, U32>, fu: U32}

def ic_pre(+c: IC) -> List<&2, U32>:
  match c:
    case IC{poss, cn, us, pre, fields, ccty, pp, ni, acc, ci, need, can,
            delta, vi, ps, qs, e, args, fu}:
      pre

def ic_fields(+c: IC) -> List<&2, U32>:
  match c:
    case IC{poss, cn, us, pre, fields, ccty, pp, ni, acc, ci, need, can,
            delta, vi, ps, qs, e, args, fu}:
      fields

def ic_pp(+c: IC) -> U32:
  match c:
    case IC{poss, cn, us, pre, fields, ccty, pp, ni, acc, ci, need, can,
            delta, vi, ps, qs, e, args, fu}:
      pp

def ic_ni(+c: IC) -> U32:
  match c:
    case IC{poss, cn, us, pre, fields, ccty, pp, ni, acc, ci, need, can,
            delta, vi, ps, qs, e, args, fu}:
      ni

def ic_cn(+c: IC) -> U32:
  match c:
    case IC{poss, cn, us, pre, fields, ccty, pp, ni, acc, ci, need, can,
            delta, vi, ps, qs, e, args, fu}:
      cn

def ic_us(+c: IC) -> List<&2, U32>:
  match c:
    case IC{poss, cn, us, pre, fields, ccty, pp, ni, acc, ci, need, can,
            delta, vi, ps, qs, e, args, fu}:
      us

def ic_push(+c: IC, +lm: U32) -> IC:
  match c:
    case IC{poss, cn, us, pre, fields, ccty, pp, ni, acc, ci, need, can,
            delta, vi, ps, qs, e, args, fu}:
      IC{poss, cn, us, pre, fields, ccty, pp, ni, Con{lm, acc}, ci, need,
         can, delta, vi, ps, qs, e, args, fu}

# pick a frame by a flag (frames are Data, strictness is cheap)
def pick_kf(+z: Bool, +x: KF, +y: KF) -> KF:
  match z:
    case True{}:
      x
    case False{}:
      y

# the eval frame for a walk on target e; depth 0 keeps
def kev(+wp: WP, +e: U32) -> KF:
  pick_kf(U32.is_eq(wp_fu(wp), 0), KKp{e},
    pick_kf(U32.is_eq(wp_op(wp), 0), KEvL{wp_c(wp), wp_d(wp), e, wp_fu(wp)},
            pick_kf(U32.is_eq(wp_op(wp), 1),
                    KEvI{wp_c(wp), wp_v(wp), e, wp_fu(wp)},
                    KEvS{wp_ps(wp), wp_qs(wp), e, wp_fu(wp)})))

# the whnf frame for e under args; fuel 0 rebuilds (the old `case 0n`)
def kwev(+delta: Bool, +e: U32, +args: List<&2, U32>, +fu: U32) -> KF:
  pick_kf(U32.is_eq(fu, 0), WRb{e, args}, WEv{delta, e, args, fu})

# level normal forms of use-site level arguments (infer.bend's lns_of)
def klns_of(us: List<&2, U32>, +lnt: R.Tr<L.LN>) -> List<&2, L.LN>:
  match us:
    case Nil{}:
      Nil{}
    case Con{head, tail}:
      Con{R.get(L.LN, 32n, lnt, head, L.LNun{}), klns_of(tail, lnt)}

# substitute every level in `us`, allocating each normal form into the level
# trie (infer.bend's lsub_lvls, same allocation order: head first)
def klsub_lvls(us: List<&2, U32>, +lnt: R.Tr<L.LN>, +nlx: U32,
               +ps: List<&2, U32>, +qs: List<&2, L.LN>) -> LVS:
  match us:
    case Nil{}:
      LVS{lnt, nlx, Nil{}}
    case Con{head, tail}:
      +r : LVS = klsub_lvls(tail,
                            R.set(L.LN, 32n, lnt, nlx,
                                  L.ln_subst(R.get(L.LN, 32n, lnt, head,
                                                   L.LNun{}), ps, qs),
                                  L.LNun{}),
                            (nlx + 1 : U32), ps, qs)
      LVS{lvs_t(r), lvs_nx(r), Con{nlx, lvs_xs(r)}}

# --- structural equality over the flat store (infer.bend's eq_ex) ----------
# A worklist walker: each pair carries its remaining DEPTH budget (the trie
# version's per-pair fuel), children get dep-1, dep 0 answers TUnk, and an
# equal-index pair answers TYes without reading (TUnk at dep 0) -- exactly
# the trie semantics. eq_ex never answers TNo, so TUnk absorbs.
type QI is Data:
  QA{a: U32, b: U32, dep: U32}
  QB{an: T.Ex, b: U32, dep: U32}

type QR is Data:
  QR{t: L.Tri, kids: List<&2, QI>}

def qr_t(+r: QR) -> L.Tri:
  match r:
    case QR{t, kids}:
      t

def qr_kids(+r: QR) -> List<&2, QI>:
  match r:
    case QR{t, kids}:
      kids

def pick_qis(+z: Bool, +x: List<&2, QI>, +y: List<&2, QI>) -> List<&2, QI>:
  match z:
    case True{}:
      x
    case False{}:
      y

# a child pair's contribution when the indices are already equal
def keq_same(+cdep: U32) -> L.Tri:
  L.pick_tri(U32.is_eq(cdep, 0), L.TUnk{}, L.TYes{})

# fold one child pair: equal indices contribute directly, unequal ones queue
def kq1(+x: U32, +y: U32, +cdep: U32, +t: L.Tri,
        kids: List<&2, QI>) -> QR:
  +k2 : List<&2, QI> = kids
  QR{I.tri_and(t, L.pick_tri(U32.is_eq(x, y), keq_same(cdep), L.TYes{})),
     pick_qis(U32.is_eq(x, y), k2, Con{QA{x, y, cdep}, k2})}

def kq2(+x1: U32, +y1: U32, +x2: U32, +y2: U32, +cdep: U32) -> QR:
  +r : QR = kq1(x2, y2, cdep, L.TYes{}, Nil{})
  kq1(x1, y1, cdep, qr_t(r), qr_kids(r))

# compare two fetched nodes; levels resolve through the level trie
def keq_cmp(x: T.Ex, y: T.Ex, +dep: U32, +lnt: R.Tr<L.LN>) -> QR:
  match x y:
    case T.ESort{a} T.ESort{b}:
      QR{L.ln_cmp(R.get(L.LN, 32n, lnt, a, L.LNun{}),
                  R.get(L.LN, 32n, lnt, b, L.LNun{})), Nil{}}
    case T.EBVar{a} T.EBVar{b}:
      QR{L.pick_tri(U32.is_eq(a, b), L.TYes{}, L.TUnk{}), Nil{}}
    case T.EConst{a, us} T.EConst{b, vs}:
      QR{L.pick_tri(U32.is_eq(a, b), I.eq_lvls(us, vs, lnt), L.TUnk{}),
         Nil{}}
    case T.EApp{f1, a1} T.EApp{f2, a2}:
      kq2(f1, f2, a1, a2, (dep - 1 : U32))
    case T.EAll{n1, t1, b1, i1} T.EAll{n2, t2, b2, i2}:
      kq2(t1, t2, b1, b2, (dep - 1 : U32))
    case T.ELam{n1, t1, b1, i1} T.ELam{n2, t2, b2, i2}:
      kq2(t1, t2, b1, b2, (dep - 1 : U32))
    case T.EProj{tn1, i1, s1} T.EProj{tn2, i2, s2}:
      +sc : Bool = U32.is_eq(tn1, tn2) && U32.is_eq(i1, i2)
      +r : QR = kq1(s1, s2, (dep - 1 : U32), L.TYes{}, Nil{})
      QR{L.pick_tri(sc, qr_t(r), L.TUnk{}),
         pick_qis(sc, qr_kids(r), Nil{})}
    case T.ENat{d1} T.ENat{d2}:
      QR{L.pick_tri(I.eq_u32s(d1, d2), L.TYes{}, L.TUnk{}), Nil{}}
    case T.EStr{d1} T.EStr{d2}:
      QR{L.pick_tri(I.eq_u32s(d1, d2), L.TYes{}, L.TUnk{}), Nil{}}
    case _ _:
      QR{L.TUnk{}, Nil{}}

# a dep-0 pair answers TUnk without comparing (the trie's fuel-0 entry)
def keq_cmp0b(z: Bool, x: T.Ex, y: T.Ex, +dep: U32, +lnt: R.Tr<L.LN>) -> QR:
  match z:
    case True{}:
      QR{L.TUnk{}, Nil{}}
    case False{}:
      keq_cmp(x, y, dep, lnt)

def keq_cmp0(+dep: U32, x: T.Ex, y: T.Ex, +lnt: R.Tr<L.LN>) -> QR:
  keq_cmp0b(U32.is_eq(dep, 0), x, y, dep, lnt)

# the next index the worklist's head needs fetched
def keq_next(wl: List<&2, QI>) -> U32:
  match wl:
    case Nil{}:
      0
    case Con{QA{a, b, dep}, tail}:
      a
    case Con{QB{an, b, dep}, tail}:
      b

def keq_go(fuel: Nat, +lnt: R.Tr<L.LN>, wl: List<&2, QI>, +acc: L.Tri,
           +nx: U32,
           pr: Array<T.Ex> & T.Ex) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fuel wl pr:
    case 0n _ Tuple{a, nd}:
      (((a, nx), MTri{L.TUnk{}}), 0)
    case 1n+p Nil{} Tuple{a, nd}:
      (((a, nx), MTri{acc}), 0)
    case 1n+p Con{QA{x, y, dep}, tail} Tuple{a, nd}:
      +y2 : U32 = y
      keq_go(p, lnt, Con{QB{nd, y2, dep}, tail}, acc, nx,
             Array.get(T.Ex, a, y2))
    case 1n+p Con{QB{an, y, dep}, tail} Tuple{a, nd}:
      +r : QR = keq_cmp0(dep, an, nd, lnt)
      +w : List<&2, QI> = List.append(&2, QI, qr_kids(r), tail)
      keq_go(p, lnt, w, I.tri_and(acc, qr_t(r)), nx,
             Array.get(T.Ex, a, keq_next(w)))

# zip two index lists into the initial worklist (infer.bend's
# eq_u32_lists_ex: per-element depth 256; length mismatch answers TUnk)
def kzip(xs: List<&2, U32>, ys: List<&2, U32>, +acc: L.Tri,
         kids: List<&2, QI>) -> QR:
  match xs ys:
    case Nil{} Nil{}:
      QR{acc, kids}
    case Con{x, tx} Con{y, ty}:
      +r : QR = kq1(x, y, 256, acc, kids)
      kzip(tx, ty, qr_t(r), qr_kids(r))
    case _ _:
      QR{L.TUnk{}, kids}

def keq_lists2(+r: QR, fs: Array<T.Ex> & U32,
               +lnt: R.Tr<L.LN>) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fs:
    case Tuple{ex, nx}:
      +wl : List<&2, QI> = qr_kids(r)
      keq_go(100000000n, lnt, wl, qr_t(r), nx,
             Array.get(T.Ex, ex, keq_next(wl)))

def keq_lists_tin(fs: Array<T.Ex> & U32, xs: List<&2, U32>,
                  ys: List<&2, U32>,
                  +lnt: R.Tr<L.LN>) -> ((Array<T.Ex> & U32) & MG) & U32:
  keq_lists2(kzip(xs, ys, L.TYes{}, Nil{}), fs, lnt)

# --- store shufflers --------------------------------------------------------
# TIN = ((Array<T.Ex> & U32) & MG) & U32 -- store, message, result register
def kfetch2(pr: Array<T.Ex> & T.Ex, +nx: U32,
            +ri: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match pr:
    case Tuple{ex, node}:
      (((ex, nx), MX{node}), ri)

def kfetch(fs: Array<T.Ex> & U32, +i: U32,
           +ri: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fs:
    case Tuple{ex, nx}:
      kfetch2(Array.get(T.Ex, ex, i), nx, ri)

# allocate `node`, result register = fresh index
def kalloc(fs: Array<T.Ex> & U32,
           +node: T.Ex) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fs:
    case Tuple{ex, nx}:
      +n : U32 = nx
      (((Array.set(T.Ex, ex, n, node), (n + 1 : U32)), MN{}), n)

# no allocation, result register = existing index
def kkeep(fs: Array<T.Ex> & U32,
          +e: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  ((fs, MN{}), e)

# allocate if changed, else keep e
def kalloc_if(+chg: Bool, fs: Array<T.Ex> & U32, +node: T.Ex,
              +e: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match chg:
    case True{}:
      kalloc(fs, node)
    case False{}:
      kkeep(fs, e)

# lift's bvar leaf: shift a free index, keep a bound one
def kbv_lift(fs: Array<T.Ex> & U32, +i: U32, +e: U32, +c: U32,
             +d: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  kalloc_if(U32.is_ge(i, c), fs, T.EBVar{(i + d : U32)}, e)

# inst's bvar leaf, after the sentinel walk
def kbv_fin(+iseq: Bool, +isgt: Bool, fs: Array<T.Ex> & U32, +ri: U32,
            +i: U32, +e: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match iseq:
    case True{}:
      kkeep(fs, ri)
    case False{}:
      kalloc_if(isgt, fs, T.EBVar{(i - 1 : U32)}, e)

# lsubst's sort leaf, decided
def ksort3(+same: Bool, fs: Array<T.Ex> & U32, +nlx: U32,
           +e: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match same:
    case True{}:
      kkeep(fs, e)
    case False{}:
      kalloc(fs, T.ESort{nlx})

# lsubst's const leaf: allocate the constant over fresh level indices
def ksconst(fs: Array<T.Ex> & U32, +n: U32,
            +xs: List<&2, U32>) -> ((Array<T.Ex> & U32) & MG) & U32:
  kalloc(fs, T.EConst{n, xs})

# rebuild the leftover arg spine over head h (infer.bend's rebuild)
def krebuild(args: List<&2, U32>, fs: Array<T.Ex> & U32,
             +h: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match args fs:
    case Nil{} Tuple{ex, nx}:
      (((ex, nx), MN{}), h)
    case Con{a, rest} Tuple{ex, nx}:
      +n : U32 = nx
      krebuild(rest, (Array.set(T.Ex, ex, n, T.EApp{h, a}), (n + 1 : U32)),
               n)

# collect an application spine: head node + args in application order
def kspine(fuel: Nat, acc: List<&2, U32>, +ri: U32, +nx: U32,
           pr: Array<T.Ex> & T.Ex) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fuel pr:
    case 0n Tuple{a, nd}:
      (((a, nx), MSP{nd, acc}), ri)
    case 1n+p Tuple{a, nd}:
      match nd:
        case T.EApp{f, g}:
          kspine(p, Con{g, acc}, ri, nx, Array.get(T.Ex, a, f))
        case y:
          (((a, nx), MSP{y, acc}), ri)

def kspine_tin(fs: Array<T.Ex> & U32, +i: U32,
               +ri: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fs:
    case Tuple{ex, nx}:
      kspine(256n, Nil{}, ri, nx, Array.get(T.Ex, ex, i))

# the three literal operations on decimal digits (infer.bend's lit_op)
def klit(fs: Array<T.Ex> & U32, +aw: U32, +da: List<&2, U32>,
         +db: List<&2, U32>, +tn: U32,
         +fn2: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match aw:
    case 0:
      kalloc(fs, T.ENat{I.dec_add(da, db)})
    case 1:
      kalloc(fs, T.ENat{I.dec_sub(da, db)})
    case _:
      kalloc(fs, T.EConst{S.pick(I.dec_le(da, db), tn, fn2), Nil{}})

# --- iota reduct construction (infer.bend's build_ihs tail + nat_expand) ---
def ktin_of(r: (Array<T.Ex> & U32) & U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match r:
    case Tuple{fs, x}:
      ((fs, MN{}), x)

# wrap a body in lambdas; doms arrive INNERMOST FIRST (the raw collection
# order), which is exactly the allocation order wrap_lams uses
def kwrapl(doms: List<&2, U32>,
           r: (Array<T.Ex> & U32) & U32) -> (Array<T.Ex> & U32) & U32:
  match doms r:
    case Nil{} Tuple{fs, b}:
      (fs, b)
    case Con{h, t} Tuple{Tuple{ex, nx}, b}:
      +n : U32 = nx
      kwrapl(t, ((Array.set(T.Ex, ex, n, T.ELam{0, h, b, 0}),
                  (n + 1 : U32)), n))

# fold an argument list onto a head (infer.bend's app_args)
def kapargs(xs: List<&2, U32>,
            r: (Array<T.Ex> & U32) & U32) -> (Array<T.Ex> & U32) & U32:
  match xs r:
    case Nil{} Tuple{fs, h}:
      (fs, h)
    case Con{x, t} Tuple{Tuple{ex, nx}, h}:
      +n : U32 = nx
      kapargs(t, ((Array.set(T.Ex, ex, n, T.EApp{h, x}), (n + 1 : U32)),
                  n))

def kb3(r: (Array<T.Ex> & U32) & U32, items: List<&2, U32>, +rc: U32,
        doms: List<&2, U32>) -> ((Array<T.Ex> & U32) & MG) & U32:
  match r:
    case Tuple{fs, fz}:
      ktin_of(kwrapl(doms,
                     kapargs(List.append(&2, U32, items, Con{fz, Nil{}}),
                             (fs, rc))))

def kb2(r: (Array<T.Ex> & U32) & List<&2, U32>, +rc: U32, +fldL: U32,
        items: List<&2, U32>,
        doms: List<&2, U32>) -> ((Array<T.Ex> & U32) & MG) & U32:
  match r:
    case Tuple{fs, zs}:
      kb3(kapargs(zs, (fs, fldL)), items, rc, doms)

# allocate the q bound variables of the IH's lambda telescope, descending
def kbvs(cnt: Nat, +i: U32, acc: List<&2, U32>,
         fs: Array<T.Ex> & U32) -> (Array<T.Ex> & U32) & List<&2, U32>:
  match cnt fs:
    case 0n Tuple{ex, nx}:
      ((ex, nx), I.rev_u(acc, Nil{}))
    case 1n+p2 Tuple{ex, nx}:
      +n : U32 = nx
      kbvs(p2, (i - 1 : U32), Con{n, acc},
           (Array.set(T.Ex, ex, n, T.EBVar{i}), (n + 1 : U32)))

def kalloc2p(fs: Array<T.Ex> & U32,
             +node: T.Ex) -> (Array<T.Ex> & U32) & U32:
  match fs:
    case Tuple{ex, nx}:
      +n : U32 = nx
      ((Array.set(T.Ex, ex, n, node), (n + 1 : U32)), n)

def kb1(r: (Array<T.Ex> & U32) & U32, +q: U32, +fldL: U32,
        items: List<&2, U32>,
        doms: List<&2, U32>) -> ((Array<T.Ex> & U32) & MG) & U32:
  match r:
    case Tuple{fs, rc}:
      +r2 : U32 = rc
      kb2(kbvs(U32.to_nat(q), (q - 1 : U32), Nil{}, fs), r2, fldL, items,
          doms)

# one inductive hypothesis, given the already-lifted outer terms: allocate
# the recursor constant, the z binders, `f z-bar`, the full application,
# and the wrapping lambdas -- in exactly the old allocation order
def kih_build(fs: Array<T.Ex> & U32, lifted: List<&2, U32>,
              ebni: List<&2, U32>, doms: List<&2, U32>, +q: U32, +cn: U32,
              +us: List<&2, U32>) -> ((Array<T.Ex> & U32) & MG) & U32:
  +lf : List<&2, U32> = lifted
  kb1(kalloc2p(fs, T.EConst{cn, us}), q, I.last_u(lf, 4294967295),
      List.append(&2, U32, I.drop_last(lf, Nil{}), ebni), doms)

# a nat literal expanded one constructor step (infer.bend's nat_expand)
def knatexp2(z: Bool, fs: Array<T.Ex> & U32, +d: List<&2, U32>, +zn: U32,
             +sn: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match z fs:
    case True{} Tuple{ex, nx}:
      +n : U32 = nx
      (((Array.set(T.Ex, ex, n, T.EConst{zn, Nil{}}), (n + 1 : U32)),
        MN{}), n)
    case False{} Tuple{ex, nx}:
      +n : U32 = nx
      (((Array.set(T.Ex,
                   Array.set(T.Ex,
                             Array.set(T.Ex, ex, n, T.EConst{sn, Nil{}}),
                             (n + 1 : U32),
                             T.ENat{I.dec_sub1(I.rev_u(d, Nil{}), True{},
                                               Nil{})}),
                   (n + 2 : U32), T.EApp{n, (n + 1 : U32)}),
        (n + 3 : U32)), MN{}), (n + 2 : U32))

def knatexp(fs: Array<T.Ex> & U32, +d: List<&2, U32>, +zn: U32,
            +sn: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  +d2 : List<&2, U32> = d
  knatexp2(I.dec_is_zero(d2), fs, d2, zn, sn)

# the telescope scan a field type needs: count and collect the Pi binders
# (innermost first), then the result type's application spine
def kscan_b(fuel: Nat, sargs: List<&2, U32>, +cnt: U32,
            doms: List<&2, U32>, +nx: U32,
            pr: Array<T.Ex> & T.Ex) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fuel pr:
    case 0n Tuple{a, nd}:
      (((a, nx), MIH{cnt, doms, sargs}), 0)
    case 1n+p2 Tuple{a, nd}:
      match nd:
        case T.EApp{f, g}:
          kscan_b(p2, Con{g, sargs}, cnt, doms, nx, Array.get(T.Ex, a, f))
        case y:
          (((a, nx), MIH{cnt, doms, sargs}), 0)

def kscan_a(fuel: Nat, doms: List<&2, U32>, +cnt: U32, +nx: U32,
            pr: Array<T.Ex> & T.Ex) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fuel pr:
    case 0n Tuple{a, nd}:
      (((a, nx), MIH{cnt, doms, Nil{}}), 0)
    case 1n+p2 Tuple{a, nd}:
      match nd:
        case T.EAll{n, t, b, bi}:
          kscan_a(p2, Con{t, doms}, (cnt + 1 : U32), nx,
                  Array.get(T.Ex, a, b))
        case y:
          kscan_b(256n, Nil{}, cnt, doms, nx, (a, y))

def kih_scan_tin(fs: Array<T.Ex> & U32,
                 +fty: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fs:
    case Tuple{ex, nx}:
      kscan_a(256n, Nil{}, 0, nx, Array.get(T.Ex, ex, fty))

def krev(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      krev(tail, Con{head, acc})

def head_u(xs: List<&2, U32>, +dflt: U32) -> U32:
  match xs:
    case Nil{}:
      dflt
    case Con{head, tail}:
      head

def ktail(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{head, tail}:
      tail

# a transition that touches no store: pass the store through, message MN
def knoop(fs: Array<T.Ex> & U32,
          +ri: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  ((fs, MN{}), ri)

# --- the machine -------------------------------------------------------------
# Data-kinded context rides as plain parameters: the level trie (lnt, nlx),
# the recursor Meta table mt, the lparams table lp, the value table vt.
# Returns ((store & result) & levels).
def km(fuel: Nat, +stk: KS, +lnt: R.Tr<L.LN>, +nlx: U32,
       +mt: R.Tr<I.Meta>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
       +qtt: R.Tr<U32>, +natn: U32,
       tin: ((Array<T.Ex> & U32) & MG) & U32)
    -> ((Array<T.Ex> & U32) & U32) & (R.Tr<L.LN> & U32):
  match fuel stk tin:
    case 0n _ Tuple{Tuple{fs, msg}, ri}:
      ((fs, 4294967295), (lnt, nlx))
    case 1n+p KNil{} Tuple{Tuple{fs, msg}, ri}:
      ((fs, ri), (lnt, nlx))
    case 1n+p KCon{KKp{e}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, kkeep(fs, e))
    # ---- eval: lift ----
    case 1n+p KCon{KEvL{c, d, e, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      match node:
        case T.EBVar{i}:
          km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, kbv_lift(fs, i, e, c, d))
        case T.EApp{f, a}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +f2 : U32 = f
          km(p, KCon{kev(w, f2), KCon{KAp2{w, e, f2, a}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, kfetch(fs, f2, ri))
        case T.ELam{n, t, b, bi}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLm2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, kfetch(fs, t2, ri))
        case T.EAll{n, t, b, bi}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KAl2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, kfetch(fs, t2, ri))
        case T.ELet{n, t, v, b}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLt2{w, e, n, t2, v, b}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, kfetch(fs, t2, ri))
        case T.EProj{tn, i, s}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +s2 : U32 = s
          km(p, KCon{kev(w, s2), KCon{KPj2{e, tn, i, s2}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, kfetch(fs, s2, ri))
        case _:
          km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, kkeep(fs, e))
    # ---- eval: inst ----
    case 1n+p KCon{KEvI{c, v, e, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      match node:
        case T.EBVar{i}:
          +c2 : U32 = c
          +i2 : U32 = i
          +v2 : U32 = v
          +iseq : Bool = U32.is_eq(i2, c2)
          +tgt : U32 = S.pick(iseq, v2, 4294967295)
          km(p, KCon{kev(WP{0, 0, c2, 0, Nil{}, Nil{}, 256}, tgt),
                     KCon{KBvI{iseq, U32.is_gt(i2, c2), i2, e}, k}},
             lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, tgt, ri))
        case T.EApp{f, a}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +f2 : U32 = f
          km(p, KCon{kev(w, f2), KCon{KAp2{w, e, f2, a}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, kfetch(fs, f2, ri))
        case T.ELam{n, t, b, bi}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLm2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, kfetch(fs, t2, ri))
        case T.EAll{n, t, b, bi}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KAl2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, kfetch(fs, t2, ri))
        case T.ELet{n, t, vv, b}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLt2{w, e, n, t2, vv, b}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, kfetch(fs, t2, ri))
        case T.EProj{tn, i, s}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +s2 : U32 = s
          km(p, KCon{kev(w, s2), KCon{KPj2{e, tn, i, s2}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, kfetch(fs, s2, ri))
        case _:
          km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, kkeep(fs, e))
    # ---- eval: lsubst ----
    case 1n+p KCon{KEvS{ps, qs, e, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      match node:
        case T.ESort{l}:
          +old : L.LN = R.get(L.LN, 32n, lnt, l, L.LNun{})
          +u : L.LN = L.ln_subst(old, ps, qs)
          +same : Bool = L.tri_is_yes(L.ln_cmp(old, u))
          +nl : U32 = nlx
          km(p, k,
             R.sub(L.LN, same, lnt, R.set(L.LN, 32n, lnt, nl, u, L.LNun{})),
             S.pick(same, nl, (nl + 1 : U32)), mt, lp, vt, qtt, natn,
             ksort3(same, fs, nl, e))
        case T.EConst{n, us}:
          +r : LVS = klsub_lvls(us, lnt, nlx, ps, qs)
          km(p, k, lvs_t(r), lvs_nx(r), mt, lp, vt, qtt, natn,
             ksconst(fs, n, lvs_xs(r)))
        case T.EApp{f, a}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +f2 : U32 = f
          km(p, KCon{kev(w, f2), KCon{KAp2{w, e, f2, a}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, kfetch(fs, f2, ri))
        case T.ELam{n, t, b, bi}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLm2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, kfetch(fs, t2, ri))
        case T.EAll{n, t, b, bi}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KAl2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, kfetch(fs, t2, ri))
        case T.ELet{n, t, v, b}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLt2{w, e, n, t2, v, b}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, kfetch(fs, t2, ri))
        case T.EProj{tn, i, s}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +s2 : U32 = s
          km(p, KCon{kev(w, s2), KCon{KPj2{e, tn, i, s2}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, kfetch(fs, s2, ri))
        case _:
          km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, kkeep(fs, e))
    # ---- whnf: rebuild on exhausted fuel ----
    case 1n+p KCon{WRb{e, args}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, krebuild(args, fs, e))
    # ---- whnf: eval (entry-level node dispatch; first match wins) ----
    case 1n+p KCon{WEv{delta, e, args, fu}, k}
         Tuple{Tuple{fs, MX{T.EApp{f, a}}}, ri}:
      +f2 : U32 = f
      km(p, KCon{kwev(delta, f2, Con{a, args}, (fu - 1 : U32)), k}, lnt,
         nlx, mt, lp, vt, qtt, natn, kfetch(fs, f2, ri))
    case 1n+p KCon{WEv{delta, e, Con{a, rest}, fu}, k}
         Tuple{Tuple{fs, MX{T.ELam{n, t, b, bi}}}, ri}:
      +b2 : U32 = b
      km(p, KCon{kev(WP{1, 0, 0, a, Nil{}, Nil{}, 256}, b2),
                 KCon{WCont{delta, rest, (fu - 1 : U32)}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, b2, ri))
    case 1n+p KCon{WEv{delta, e, args, fu}, k}
         Tuple{Tuple{fs, MX{T.ELet{n, t, v, b}}}, ri}:
      +b2 : U32 = b
      km(p, KCon{kev(WP{1, 0, 0, v, Nil{}, Nil{}, 256}, b2),
                 KCon{WCont{delta, args, (fu - 1 : U32)}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, b2, ri))
    case 1n+p KCon{WEv{delta, e, args, fu}, k}
         Tuple{Tuple{fs, MX{T.EConst{n, us}}}, ri}:
      +n2 : U32 = n
      +a2 : List<&2, U32> = args
      +vi : U32 = R.get(U32, 32n, vt, n2, 4294967295)
      +d2 : Bool = delta
      +can : Bool = Bool.and(d2, U32.is_ne(vi, 4294967295))
      +mi : I.Meta = R.get(I.Meta, 32n, mt, n2, I.MNone{})
      +pp : U32 = I.meta_p(mi)
      +mn : U32 = I.meta_n(mi)
      +mk : U32 = I.meta_k(mi)
      +la : U32 = I.len_u(a2, 0)
      +iskr : Bool = U32.is_eq(I.meta_kf(mi), 1)
                     && U32.is_gt(la, (pp + 1 + mn + mk : U32))
      +uind : I.Meta = R.get(I.Meta, 32n, mt, I.meta_ind(mi), I.MNone{})
      +isue : Bool = I.meta_is_rec(mi) && I.meta_is_ind(uind)
                     && U32.is_eq(I.meta_nf(uind), 0)
                     && U32.is_eq(mk, 0)
                     && U32.is_gt(la, (pp + 1 + mn : U32))
      +need : U32 = (pp + 1 + mn + mk : U32)
      +u2 : List<&2, U32> = us
      km(p, KCon{WPh1{iskr, isue, can, d2, vi,
                      R.get(List<&2, U32>, 32n, lp, n2, Nil{}),
                      klns_of(u2, lnt), e, a2, fu, pp, mn, mk,
                      I.meta_rcty(mi), n2,
                      P5{I.meta_is_rec(mi) && U32.is_gt(la, need), need,
                         I.meta_ind(mi), pp, mk, n2, u2}}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, knoop(fs, ri))
    case 1n+p KCon{WEv{delta, e, args, fu}, k}
         Tuple{Tuple{fs, MX{T.EProj{tn, idx, sx}}}, ri}:
      +s2 : U32 = sx
      +f2 : U32 = (fu - 1 : U32)
      km(p, KCon{kwev(delta, s2, Nil{}, f2),
                 KCon{WPrj{delta, e, tn, idx, args, f2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, s2, ri))
    case 1n+p KCon{WEv{delta, e, args, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, krebuild(args, fs, e))
    # ---- whnf: continue on a substitution result ----
    case 1n+p KCon{WCont{delta, args, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{kwev(delta, r2, args, fu), k}, lnt, nlx, mt, lp, vt, qtt, natn,
         kfetch(fs, r2, 0))
    # ---- EConst pipeline: phase 1, K-like reduction ----
    case 1n+p KCon{WPh1{True{}, isue, can, delta, vi, ps, qs, e, args, fu,
                        pp, mn, mk, rcty, cn, p5}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +p2 : U32 = pp
      +r2 : U32 = rcty
      +a2 : List<&2, U32> = args
      km(p, KCon{WPlE{r2, I.take_u(a2, p2, Nil{})},
                 KCon{WK2{isue, can, delta, vi, ps, qs, e, a2, fu, p2, mn,
                          mk, cn, p5}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, r2, ri))
    case 1n+p KCon{WPh1{False{}, isue, can, delta, vi, ps, qs, e, args, fu,
                        pp, mn, mk, rcty, cn, p5}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WPh2{isue, can, delta, vi, ps, qs, e, args, fu, pp, mn,
                      cn, p5}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, knoop(fs, ri))
    # ---- telescope peel (ordered: the Pi case must precede the stuck one)
    case 1n+p KCon{WPlE{tyi, Nil{}}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, kkeep(fs, tyi))
    case 1n+p KCon{WPlE{tyi, Con{v, rest}}, k}
         Tuple{Tuple{fs, MX{T.EAll{n, t, b, bi}}}, ri}:
      +b2 : U32 = b
      km(p, KCon{kev(WP{1, 0, 0, v, Nil{}, Nil{}, 256}, b2),
                 KCon{WPlC{rest}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, b2, ri))
    case 1n+p KCon{WPlE{tyi, Con{v, rest}}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, kkeep(fs, 4294967295))
    case 1n+p KCon{WPlC{vals}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WPlE{r2, vals}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         kfetch(fs, r2, 0))
    # ---- K: peel done -> spine of the peeled type ----
    case 1n+p KCon{WK2{isue, can, delta, vi, ps, qs, e, args, fu, pp, mn,
                       mk, cn, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WK3{U32.is_ne(r2, 4294967295), isue, can, delta, vi, ps,
                     qs, e, args, fu, pp, mn, mk, cn, p5}, k},
         lnt, nlx, mt, lp, vt, qtt, natn,
         kspine_tin(fs, S.pick(U32.is_ne(r2, 4294967295), r2, 0), 0))
    # ---- K: spine done -> compare expected and given indices ----
    case 1n+p KCon{WK3{pok, isue, can, delta, vi, ps, qs, e, args, fu, pp,
                       mn, mk, cn, p5}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +a2 : List<&2, U32> = args
      +p2 : U32 = pp
      +m2 : U32 = mn
      +k2 : U32 = mk
      km(p, KCon{WK4{pok, isue, can, delta, vi, ps, qs, e, a2, fu, p2, m2,
                     k2, cn, p5}, k},
         lnt, nlx, mt, lp, vt, qtt, natn,
         keq_lists_tin(fs, I.skip_u(sargs, p2),
                       I.take_u(I.skip_u(a2, (p2 + 1 + m2 : U32)), k2,
                                Nil{}),
                       lnt))
    # ---- K: verdict arrived ----
    case 1n+p KCon{WK4{pok, isue, can, delta, vi, ps, qs, e, args, fu, pp,
                       mn, mk, cn, p5}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{WKGo{Bool.and(pok, L.tri_is_yes(t)), isue, can, delta, vi,
                      ps, qs, e, args, fu, pp, mn, mk, cn, p5}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, knoop(fs, ri))
    case 1n+p KCon{WKGo{True{}, isue, can, delta, vi, ps, qs, e, args, fu,
                        pp, mn, mk, cn, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +p2 : U32 = pp
      +mi2 : U32 = I.nth_u(a2, (p2 + 1 : U32), 4294967295)
      km(p, KCon{kwev(delta, mi2, I.skip_u(a2, (p2 + 1 + mn + mk + 1 : U32)),
                      (fu - 1 : U32)), k},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, mi2, ri))
    case 1n+p KCon{WKGo{False{}, isue, can, delta, vi, ps, qs, e, args, fu,
                        pp, mn, mk, cn, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WPh2{isue, can, delta, vi, ps, qs, e, args, fu, pp, mn,
                      cn, p5}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, knoop(fs, ri))
    # ---- phase 2: unit-like structure eta ----
    case 1n+p KCon{WPh2{True{}, can, delta, vi, ps, qs, e, args, fu, pp,
                        mn, cn, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +p2 : U32 = pp
      +mi2 : U32 = I.nth_u(a2, (p2 + 1 : U32), 4294967295)
      km(p, KCon{kwev(delta, mi2, I.skip_u(a2, (p2 + 1 + mn + 1 : U32)),
                      (fu - 1 : U32)), k},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, mi2, ri))
    case 1n+p KCon{WPh2{False{}, can, delta, vi, ps, qs, e, args, fu, pp,
                        mn, cn, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      +n2 : U32 = cn
      +a2 : List<&2, U32> = args
      +la : U32 = I.len_u(a2, 0)
      +aw : U32 = S.pick(U32.is_eq(n2, R.get(U32, 32n, qtt, 5,
                                             4294967295)), 0,
                   S.pick(U32.is_eq(n2, R.get(U32, 32n, qtt, 6,
                                              4294967295)), 1,
                    S.pick(U32.is_eq(n2, R.get(U32, 32n, qtt, 7,
                                               4294967295)), 2, 3)))
      +isql : Bool = U32.is_eq(n2, R.get(U32, 32n, qtt, 0, 4294967295))
                     && U32.is_gt(la, 5)
      +isqi : Bool = U32.is_eq(n2, R.get(U32, 32n, qtt, 1, 4294967295))
                     && U32.is_gt(la, 4)
      km(p, KCon{WPh3{U32.is_lt(aw, 3) && U32.is_gt(la, 1), aw,
                      Bool.or(isql, isqi), S.pick(isql, 5, 4), can, delta,
                      vi, ps, qs, e, a2, fu, p5}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, knoop(fs, ri))
    # ---- phase 3: literal arithmetic ----
    case 1n+p KCon{WPh3{True{}, aw, isq, qneed, can, delta, vi, ps, qs, e,
                        args, fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +a0 : U32 = I.nth_u(a2, 0, 4294967295)
      km(p, KCon{kwev(delta, a0, Nil{}, (fu - 1 : U32)),
                 KCon{WLa{aw, isq, qneed, can, delta, vi, ps, qs, e, a2,
                          fu, p5}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, a0, ri))
    case 1n+p KCon{WPh3{False{}, aw, isq, qneed, can, delta, vi, ps, qs, e,
                        args, fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WPh4{isq, qneed, can, delta, vi, ps, qs, e, args, fu, p5},
                 k},
         lnt, nlx, mt, lp, vt, qtt, natn, knoop(fs, ri))
    case 1n+p KCon{WLa{aw, isq, qneed, can, delta, vi, ps, qs, e, args,
                       fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +a1 : U32 = I.nth_u(a2, 1, 4294967295)
      km(p, KCon{kwev(delta, a1, Nil{}, (fu - 1 : U32)),
                 KCon{WLb{ri, aw, isq, qneed, can, delta, vi, ps, qs, e,
                          a2, fu, p5}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, a1, 0))
    case 1n+p KCon{WLb{r0, aw, isq, qneed, can, delta, vi, ps, qs, e, args,
                       fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = r0
      km(p, KCon{WLc{ri, aw, isq, qneed, can, delta, vi, ps, qs, e, args,
                     fu, p5}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, r2, 0))
    case 1n+p KCon{WLc{r1, aw, isq, qneed, can, delta, vi, ps, qs, e, args,
                       fu, p5}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +r2 : U32 = r1
      km(p, KCon{WLd{node, aw, isq, qneed, can, delta, vi, ps, qs, e, args,
                     fu, p5}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, r2, 0))
    case 1n+p KCon{WLd{na, aw, isq, qneed, can, delta, vi, ps, qs, e, args,
                       fu, p5}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +n1 : T.Ex = na
      +n2x : T.Ex = node
      km(p, KCon{WLGo{I.is_nat_lit(n1) && I.is_nat_lit(n2x), aw,
                      I.nat_digits(n1), I.nat_digits(n2x), isq, qneed, can,
                      delta, vi, ps, qs, e, args, fu, p5}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, knoop(fs, ri))
    case 1n+p KCon{WLGo{True{}, aw, da, db, isq, qneed, can, delta, vi, ps,
                        qs, e, args, fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WCont{delta, I.skip_u(args, 2), (fu - 1 : U32)}, k},
         lnt, nlx, mt, lp, vt, qtt, natn,
         klit(fs, aw, da, db, R.get(U32, 32n, qtt, 8, 4294967295),
              R.get(U32, 32n, qtt, 9, 4294967295)))
    case 1n+p KCon{WLGo{False{}, aw, da, db, isq, qneed, can, delta, vi,
                        ps, qs, e, args, fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WPh4{isq, qneed, can, delta, vi, ps, qs, e, args, fu, p5},
                 k},
         lnt, nlx, mt, lp, vt, qtt, natn, knoop(fs, ri))
    # ---- phase 4: quotient reduction ----
    case 1n+p KCon{WPh4{True{}, qneed, can, delta, vi, ps, qs, e, args,
                        fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +q2 : U32 = qneed
      +qm : U32 = I.nth_u(a2, q2, 4294967295)
      km(p, KCon{kwev(delta, qm, Nil{}, (fu - 1 : U32)),
                 KCon{WQ1{q2, can, delta, vi, ps, qs, e, a2, fu, p5},
                      k}},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, qm, ri))
    case 1n+p KCon{WPh4{False{}, qneed, can, delta, vi, ps, qs, e, args,
                        fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WPh5{p5, can, delta, vi, ps, qs, e, args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, knoop(fs, ri))
    case 1n+p KCon{WQ1{qneed, can, delta, vi, ps, qs, e, args, fu, p5}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WQ2{qneed, can, delta, vi, ps, qs, e, args, fu, p5}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, kspine_tin(fs, r2, 0))
    case 1n+p KCon{WQ2{qneed, can, delta, vi, ps, qs, e, args, fu, p5}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +a2 : List<&2, U32> = args
      +sa : List<&2, U32> = sargs
      km(p, KCon{WQGo{U32.is_eq(I.const_nm2(hd),
                                R.get(U32, 32n, qtt, 2, 4294967295))
                      && U32.is_gt(I.len_u(sa, 0), 2),
                      I.nth_u(a2, 3, 4294967295), I.nth_u(sa, 2,
                                                          4294967295),
                      qneed, can, delta, vi, ps, qs, e, a2, fu, p5}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, knoop(fs, ri))
    case 1n+p KCon{WQGo{True{}, fv, vv, qneed, can, delta, vi, ps, qs, e,
                        args, fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WCont{delta, I.skip_u(args, (qneed + 1 : U32)),
                       (fu - 1 : U32)}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, kalloc(fs, T.EApp{fv, vv}))
    case 1n+p KCon{WQGo{False{}, fv, vv, qneed, can, delta, vi, ps, qs, e,
                        args, fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WPh5{p5, can, delta, vi, ps, qs, e, args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, knoop(fs, ri))
    # ---- whnf: delta branch ----
    case 1n+p KCon{WDelGo{True{}, delta, vi, ps, qs, e, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +v2 : U32 = vi
      km(p, KCon{kev(WP{2, 0, 0, 0, ps, qs, 256}, v2),
                 KCon{WCont{delta, args, (fu - 1 : U32)}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, v2, ri))
    case 1n+p KCon{WDelGo{False{}, delta, vi, ps, qs, e, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, krebuild(args, fs, e))
    # ---- whnf: projection, struct reduced -> collect its spine ----
    case 1n+p KCon{WPrj{delta, e, tn, idx, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WPrjS{delta, e, tn, idx, args, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, kspine_tin(fs, r2, r2))
    # ---- whnf: projection, spine collected -> constructor? ----
    case 1n+p KCon{WPrjS{delta, e, tn, idx, args, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +cmi : I.Meta = R.get(I.Meta, 32n, mt, I.const_nm2(hd), I.MNone{})
      km(p, KCon{WPrjGo{I.meta_is_ctor(cmi), delta, e,
                        I.nth_u(sargs, (I.meta_p(cmi) + idx : U32),
                                4294967295),
                        args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, knoop(fs, ri))
    # ---- whnf: projection branch ----
    case 1n+p KCon{WPrjGo{True{}, delta, e, fld, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +f2 : U32 = fld
      km(p, KCon{kwev(delta, f2, args, fu), k}, lnt, nlx, mt, lp, vt, qtt, natn,
         kfetch(fs, f2, ri))
    case 1n+p KCon{WPrjGo{False{}, delta, e, fld, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, krebuild(args, fs, e))
    # ---- phase 5: iota (recursor reduction) ----
    case 1n+p KCon{WPh5{P5{True{}, need, ind, pp, mk, cn, us}, can, delta,
                        vi, ps, qs, e, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +nd2 : U32 = need
      +maj : U32 = I.nth_u(a2, nd2, 4294967295)
      km(p, KCon{kwev(delta, maj, Nil{}, (fu - 1 : U32)),
                 KCon{WI1{nd2, ind, pp, mk, cn, us, can, delta, vi, ps, qs,
                          e, a2, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, maj, ri))
    case 1n+p KCon{WPh5{P5{False{}, need, ind, pp, mk, cn, us}, can, delta,
                        vi, ps, qs, e, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WDelGo{can, delta, vi, ps, qs, e, args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, knoop(fs, ri))
    case 1n+p KCon{WI1{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs,
                       e, args, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WI2{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs, e,
                     args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, r2, r2))
    case 1n+p KCon{WI2{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs,
                       e, args, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +i2 : U32 = ind
      +nd : T.Ex = node
      km(p, KCon{WI2Go{I.is_nat_lit(nd) && U32.is_eq(i2, natn),
                       I.nat_digits(nd), ri, need, i2, pp, mk, cn, us, can,
                       delta, vi, ps, qs, e, args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, knoop(fs, 0))
    case 1n+p KCon{WI2Go{True{}, d, orig, need, ind, pp, mk, cn, us, can,
                         delta, vi, ps, qs, e, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WI2b{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs, e,
                      args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn,
         knatexp(fs, d, R.get(U32, 32n, qtt, 3, 4294967295),
                 R.get(U32, 32n, qtt, 4, 4294967295)))
    case 1n+p KCon{WI2Go{False{}, d, orig, need, ind, pp, mk, cn, us, can,
                         delta, vi, ps, qs, e, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WI2b{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs, e,
                      args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, knoop(fs, orig))
    case 1n+p KCon{WI2b{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs,
                        e, args, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WI3{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs, e,
                     args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, kspine_tin(fs, r2, 0))
    case 1n+p KCon{WI3{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs,
                       e, args, fu}, k} Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +p2 : U32 = pp
      +i2 : U32 = ind
      +cmi : I.Meta = R.get(I.Meta, 32n, mt, I.const_nm2(hd), I.MNone{})
      km(p, KCon{WIGo{I.meta_is_ctor(cmi)
                      && U32.is_eq(I.meta_ind(cmi), i2),
                      I.skip_u(sargs, p2), I.meta_recs(cmi),
                      I.meta_ci(cmi), I.meta_ccty(cmi), need, p2, mk, cn,
                      us, can, delta, vi, ps, qs, e, args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, knoop(fs, ri))
    case 1n+p KCon{WIGo{True{}, fields, recsl, ci, ccty, need, pp, mk, cn,
                        us, can, delta, vi, ps, qs, e, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +n2 : U32 = need
      km(p, KCon{WIhNext{IC{recsl, cn, us,
                            I.take_u(a2, (n2 - mk : U32), Nil{}), fields,
                            ccty, pp, mk, Nil{}, ci, n2, can, delta, vi,
                            ps, qs, e, a2, fu}}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, knoop(fs, ri))
    case 1n+p KCon{WIGo{False{}, fields, recsl, ci, ccty, need, pp, mk, cn,
                        us, can, delta, vi, ps, qs, e, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WDelGo{can, delta, vi, ps, qs, e, args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, knoop(fs, ri))
    # ---- the IH builder loop ----
    case 1n+p KCon{WIhNext{IC{Nil{}, cn, us, pre, fields, ccty, pp, ni,
                              acc, ci, need, can, delta, vi, ps, qs, e,
                              args, fu}}, k} Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +p2 : U32 = pp
      km(p, KCon{WCont{delta, I.skip_u(a2, (need + 1 : U32)),
                       (fu - 1 : U32)}, k},
         lnt, nlx, mt, lp, vt, qtt, natn,
         ktin_of(kapargs(List.append(&2, U32, fields, krev(acc, Nil{})),
                         (fs, I.nth_u(a2, (p2 + 1 + ci : U32),
                                      4294967295)))))
    case 1n+p KCon{WIhNext{IC{Con{h, t}, cn, us, pre, fields, ccty, pp, ni,
                              acc, ci, need, can, delta, vi, ps, qs, e,
                              args, fu}}, k} Tuple{Tuple{fs, msg}, ri}:
      +h2 : U32 = h
      +pr2 : List<&2, U32> = pre
      +fl2 : List<&2, U32> = fields
      +cc2 : U32 = ccty
      +p2 : U32 = pp
      km(p, KCon{WPlE{cc2,
                      List.append(&2, U32, I.take_u(pr2, p2, Nil{}),
                                  I.take_u(fl2, (h2 - 1 : U32), Nil{}))},
                 KCon{WIhPe{h2, IC{t, cn, us, pr2, fl2, cc2, p2, ni, acc,
                                   ci, need, can, delta, vi, ps, qs, e,
                                   args, fu}}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, cc2, ri))
    case 1n+p KCon{WIhPe{h, ic}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WIhFty{h, ic}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         kfetch(fs, r2, 0))
    case 1n+p KCon{WIhFty{h, ic}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      km(p, KCon{WIhScanned{h, ic}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         kih_scan_tin(fs, I.all_dom(node)))
    case 1n+p KCon{WIhScanned{h, ic}, k}
         Tuple{Tuple{fs, MIH{q, doms, eb}}, ri}:
      +ic2 : IC = ic
      +q2 : U32 = q
      +items : List<&2, U32> =
        List.append(&2, U32, ic_pre(ic2),
                    Con{I.nth_u(ic_fields(ic2), (h - 1 : U32),
                                4294967295), Nil{}})
      +first : U32 = head_u(items, 4294967295)
      km(p, KCon{kev(WP{0, 0, q2, 0, Nil{}, Nil{}, 256}, first),
                 KCon{WIhL{ktail(items), q2, Nil{},
                           I.take_u(I.skip_u(eb, ic_pp(ic2)), ic_ni(ic2),
                                    Nil{}),
                           doms, ic2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, first, ri))
    case 1n+p KCon{WIhL{Nil{}, amt, lacc, ebni, doms, ic}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +ic2 : IC = ic
      km(p, KCon{WIhB{ic2}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         kih_build(fs, krev(Con{ri, lacc}, Nil{}), ebni, doms, amt,
                   ic_cn(ic2), ic_us(ic2)))
    case 1n+p KCon{WIhL{Con{x, t}, amt, lacc, ebni, doms, ic}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      +a2 : U32 = amt
      km(p, KCon{kev(WP{0, 0, a2, 0, Nil{}, Nil{}, 256}, x2),
                 KCon{WIhL{t, a2, Con{ri, lacc}, ebni, doms, ic}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, x2, 0))
    case 1n+p KCon{WIhB{ic}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WIhNext{ic_push(ic, ri)}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, knoop(fs, 0))
    # ---- resume frames for the walks ----
    case 1n+p KCon{KBvI{iseq, isgt, i, e}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, kbv_fin(iseq, isgt, fs, ri, i, e))
    case 1n+p KCon{KAp2{wp, e, f0, a0}, k} Tuple{Tuple{fs, msg}, ri}:
      +w : WP = wp
      +a2 : U32 = a0
      km(p, KCon{kev(w, a2), KCon{KAp3{e, f0, a2, ri}, k}}, lnt, nlx, mt,
         lp, vt, qtt, natn, kfetch(fs, a2, 0))
    case 1n+p KCon{KAp3{e, f0, a0, r1}, k} Tuple{Tuple{fs, msg}, ri}:
      +r1b : U32 = r1
      +rib : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn,
         kalloc_if(Bool.not(U32.is_eq(r1b, f0) && U32.is_eq(rib, a0)),
                   fs, T.EApp{r1b, rib}, e))
    case 1n+p KCon{KLm2{wp, e, n, t0, b0, bi}, k} Tuple{Tuple{fs, msg}, ri}:
      +b2 : U32 = b0
      km(p, KCon{kev(wp_bump(wp), b2), KCon{KLm3{e, n, t0, b2, bi, ri}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, b2, 0))
    case 1n+p KCon{KLm3{e, n, t0, b0, bi, r1}, k} Tuple{Tuple{fs, msg}, ri}:
      +r1b : U32 = r1
      +rib : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn,
         kalloc_if(Bool.not(U32.is_eq(r1b, t0) && U32.is_eq(rib, b0)),
                   fs, T.ELam{n, r1b, rib, bi}, e))
    case 1n+p KCon{KAl2{wp, e, n, t0, b0, bi}, k} Tuple{Tuple{fs, msg}, ri}:
      +b2 : U32 = b0
      km(p, KCon{kev(wp_bump(wp), b2), KCon{KAl3{e, n, t0, b2, bi, ri}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, b2, 0))
    case 1n+p KCon{KAl3{e, n, t0, b0, bi, r1}, k} Tuple{Tuple{fs, msg}, ri}:
      +r1b : U32 = r1
      +rib : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn,
         kalloc_if(Bool.not(U32.is_eq(r1b, t0) && U32.is_eq(rib, b0)),
                   fs, T.EAll{n, r1b, rib, bi}, e))
    case 1n+p KCon{KLt2{wp, e, n, t0, v0, b0}, k} Tuple{Tuple{fs, msg}, ri}:
      +w : WP = wp
      +v02 : U32 = v0
      km(p, KCon{kev(w, v02), KCon{KLt3{w, e, n, t0, v02, b0, ri}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, v02, 0))
    case 1n+p KCon{KLt3{wp, e, n, t0, v0, b0, r1}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +b2 : U32 = b0
      km(p, KCon{kev(wp_bump(wp), b2),
                 KCon{KLt4{e, n, t0, v0, b2, r1, ri}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, kfetch(fs, b2, 0))
    case 1n+p KCon{KLt4{e, n, t0, v0, b0, r1, r2}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r1b : U32 = r1
      +r2b : U32 = r2
      +rib : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn,
         kalloc_if(Bool.not(U32.is_eq(r1b, t0) && U32.is_eq(r2b, v0)
                            && U32.is_eq(rib, b0)),
                   fs, T.ELet{n, r1b, r2b, rib}, e))
    case 1n+p KCon{KPj2{e, tn, ix, s0}, k} Tuple{Tuple{fs, msg}, ri}:
      +rib : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn,
         kalloc_if(Bool.not(U32.is_eq(rib, s0)), fs,
                   T.EProj{tn, ix, rib}, e))

    # A frame/message combination no transition produces; unreachable by
    # construction (every eval frame follows a fetch), mapped to the error
    # sentinel rather than an abort.
    case 1n+p _ Tuple{Tuple{fs, msg}, ri}:
      ((fs, 4294967294), (lnt, nlx))

# --- entry points ------------------------------------------------------------
def klift(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>, +nlx: U32,
          +e: U32, +c: U32, +d: U32, +fu: U32)
    -> ((Array<T.Ex> & U32) & U32) & (R.Tr<L.LN> & U32):
  +e2 : U32 = e
  km(fuel, KCon{kev(WP{0, c, d, 0, Nil{}, Nil{}, fu}, e2), KNil{}}, lnt,
     nlx, R.TNil{}, R.TNil{}, R.TNil{}, R.TNil{}, 4294967295,
     kfetch(fs, e2, 0))

def kinst(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>, +nlx: U32,
          +e: U32, +j: U32, +v: U32, +fu: U32)
    -> ((Array<T.Ex> & U32) & U32) & (R.Tr<L.LN> & U32):
  +e2 : U32 = e
  km(fuel, KCon{kev(WP{1, j, 0, v, Nil{}, Nil{}, fu}, e2), KNil{}}, lnt,
     nlx, R.TNil{}, R.TNil{}, R.TNil{}, R.TNil{}, 4294967295,
     kfetch(fs, e2, 0))

def klsubst(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>, +nlx: U32,
            +e: U32, +ps: List<&2, U32>, +qs: List<&2, L.LN>, +fu: U32)
    -> ((Array<T.Ex> & U32) & U32) & (R.Tr<L.LN> & U32):
  +e2 : U32 = e
  km(fuel, KCon{kev(WP{2, 0, 0, 0, ps, qs, fu}, e2), KNil{}}, lnt, nlx,
     R.TNil{}, R.TNil{}, R.TNil{}, R.TNil{}, 4294967295,
     kfetch(fs, e2, 0))

def kwhnf(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>, +nlx: U32,
          +mt: R.Tr<I.Meta>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
          +qtt: R.Tr<U32>, +natn: U32, +e: U32, +delta: Bool, +fu: U32)
    -> ((Array<T.Ex> & U32) & U32) & (R.Tr<L.LN> & U32):
  +e2 : U32 = e
  km(fuel, KCon{kwev(delta, e2, Nil{}, fu), KNil{}}, lnt, nlx, mt, lp, vt,
     qtt, natn, kfetch(fs, e2, 0))
