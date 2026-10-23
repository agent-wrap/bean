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
  # the walked subterm has no loose bvar at or above the cutoff (kfetch_w)
  MKeep{}
  MSP{hd: T.Ex, sargs: List<&2, U32>}
  MTri{t: L.Tri}
  # a constructor field type's telescope: binder count, binder types
  # (innermost first), and the result type's spine arguments
  MIH{q: U32, doms: List<&2, U32>, eb: List<&2, U32>}
  # a level normal form (the sl universe oracle's answers)
  MLn{l: L.LN}
  # an inference result: a type index and the ok flag
  MIR{ty: U32, ok: Bool}
  MN{}

# --- frames ----------------------------------------------------------------
type KF is Data:
  KEvL{c: U32, d: U32, e: U32, fu: U32}
  KEvI{c: U32, v: U32, e: U32, fu: U32}
  # instantiate several bound variables at once (Lean's instantiate with a
  # substitution): vs[j] replaces #(c+j), lifted by c; #i >= c+|vs| drops by
  # |vs|. Beta of `(fun x1..xk => b) a1..ak` is ONE walk of b, not k
  KEvM{c: U32, vs: List<&2, U32>, e: U32, fu: U32}
  KBvM{inr: Bool, isgt: Bool, i: U32, m: U32, e: U32}
  # beta: the leading lambdas taken so far (innermost argument first)
  WBt{taken: List<&2, U32>, rest: List<&2, U32>, delta: Bool, fu: U32,
      cur: U32, ctx: List<&2, U32>}
  KEvS{ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32, fu: U32}
  # depth fuel exhausted: keep e untouched (the trie walks' `case 0n`)
  KKp{e: U32}
  # walk (lift/inst/lsubst) fuel ran out: the subterm is kept UNSHIFTED, so
  # the result is no longer definitionally equal to the input. Flagged in the
  # declaration CORRUPT (store flag 2): fcheck declines.
  KKpF{e: U32}
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
  WEv{delta: Bool, e: U32, args: List<&2, U32>, fu: U32, ctx: List<&2, U32>}
  # whnf fuel exhausted: rebuild the spine over e
  WRb{e: U32, args: List<&2, U32>, ctx: List<&2, U32>}
  WRbP{e: U32, args: List<&2, U32>, ctx: List<&2, U32>}
  # rule-based iota (MRecR: nested/mutual recursors): whnf the major, find
  # the rule for its constructor, reduce through the delta path
  RI0{delta: Bool, e: U32, args: List<&2, U32>, fu: U32, mj: U32, pre: U32,
      rules: List<&2, U32>, ps: List<&2, U32>, qs: List<&2, L.LN>, ctx: List<&2, U32>}
  RI1{delta: Bool, e: U32, args: List<&2, U32>, fu: U32, mj: U32, pre: U32,
      rules: List<&2, U32>, ps: List<&2, U32>, qs: List<&2, L.LN>, ctx: List<&2, U32>}
  RI2{delta: Bool, e: U32, args: List<&2, U32>, fu: U32, mj: U32, pre: U32,
      rules: List<&2, U32>, ps: List<&2, U32>, qs: List<&2, L.LN>, ctx: List<&2, U32>}
  RI3{hit: Bool, rhs: U32, delta: Bool, e: U32, args: List<&2, U32>,
      fu: U32, ps: List<&2, U32>, qs: List<&2, L.LN>, ctx: List<&2, U32>}
  # a substitution walk finished; whnf its result under the spine
  WCont{delta: Bool, args: List<&2, U32>, fu: U32, ctx: List<&2, U32>}
  # branch point for delta: unfold (lsubst the value) or rebuild
  WDelGo{can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
         qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32, ctx: List<&2, U32>}
  # the struct of a projection finished reducing; collect its spine
  WPrj{delta: Bool, e: U32, tn: U32, idx: U32, args: List<&2, U32>, fu: U32, ctx: List<&2, U32>}
  # spine collected; decide whether the head is the matching constructor
  WPrjSx{delta: Bool, e: U32, tn: U32, idx: U32, args: List<&2, U32>,
         fu: U32, ctx: List<&2, U32>}
  WPrjS2{str: Bool, hd: T.Ex, sargs: List<&2, U32>, delta: Bool, e: U32,
         tn: U32, idx: U32, args: List<&2, U32>, fu: U32, ctx: List<&2, U32>}
  WPrjS{delta: Bool, e: U32, tn: U32, idx: U32, args: List<&2, U32>,
        fu: U32, ctx: List<&2, U32>}
  # branch point for projection reduction: take the field or rebuild
  WPrjGo{okp: Bool, delta: Bool, e: U32, fld: U32, args: List<&2, U32>,
         fu: U32, ctx: List<&2, U32>}
  # ---- telescope peel (infer.bend's peel_tele), reused by K and iota ----
  # expect MX of the current type node; instantiate its codomain per value
  WPlE{tyi: U32, vals: List<&2, U32>, ctx: List<&2, U32>}
  # peel: the leading Pis an argument is there for, then ONE instantiation
  WPlB{taken: List<&2, U32>, rest: List<&2, U32>, cur: U32, ctx: List<&2, U32>}
  # Lean's instantiate_value_lparams cache: the level-instantiated body of
  # a constant node e (name + level indices, exact) under memo key 2^30 + e
  WDelH{hit: Bool, h: U32, delta: Bool, vi: U32, ps: List<&2, U32>,
        qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32, ctx: List<&2, U32>}
  WDelSt{e: U32, vi: U32, ctx: List<&2, U32>}
  # iota on a structure-like major that is not a constructor application:
  # the projections are its fields (WSe receives them as an MSP)
  WSe{recsl: List<&2, U32>, need: U32, pp: U32, mk: U32, cn: U32,
      us: List<&2, U32>, can: Bool, delta: Bool, vi: U32,
      ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32, args: List<&2, U32>,
      fu: U32, ctx: List<&2, U32>}
  WI3c{isct: Bool, se: Bool, fields: List<&2, U32>, recsl: List<&2, U32>, ci: U32,
       ccty: U32, need: U32, pp: U32, mk: U32, cn: U32,
       us: List<&2, U32>, can: Bool, delta: Bool, vi: U32,
       ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32, args: List<&2, U32>,
       fu: U32, ind: U32, ctx: List<&2, U32>}
  # an instantiation finished; fetch the new type node and continue peeling
  WPlC{vals: List<&2, U32>, ctx: List<&2, U32>}
  # ---- the EConst reduction pipeline (K-like, unit-eta, delta) ----
  # phase 1 gate: K-like reduction applies?
  WPh1{iskr: Bool, isue: Bool, can: Bool, delta: Bool, vi: U32,
       ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32, args: List<&2, U32>,
       fu: U32, pp: U32, mn: U32, mk: U32, rcty: U32, cn: U32, p5: P5, ctx: List<&2, U32>}
  # peel of the recursor's constructor type finished (ri = peeled type)
  WK2{isue: Bool, can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
      qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32, pp: U32,
      mn: U32, mk: U32, cn: U32, p5: P5, ctx: List<&2, U32>}
  # spine of the peeled type collected; compare expected vs given indices
  WK3{pok: Bool, isue: Bool, can: Bool, delta: Bool, vi: U32,
      ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32, args: List<&2, U32>,
      fu: U32, pp: U32, mn: U32, mk: U32, cn: U32, p5: P5, ctx: List<&2, U32>}
  # the index comparison's verdict arrives here (MTri)
  WK4{pok: Bool, isue: Bool, can: Bool, delta: Bool, vi: U32,
      ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32, args: List<&2, U32>,
      fu: U32, pp: U32, mn: U32, mk: U32, cn: U32, p5: P5,
      xs: List<&2, U32>, ys: List<&2, U32>, ctx: List<&2, U32>}
  WK4b{need: Bool, t: L.Tri, pok: Bool, isue: Bool, can: Bool, delta: Bool,
       vi: U32, ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32,
       args: List<&2, U32>, fu: U32, pp: U32, mn: U32, mk: U32, cn: U32,
       p5: P5, xs: List<&2, U32>, ys: List<&2, U32>, ctx: List<&2, U32>}
  WK5{pok: Bool, isue: Bool, can: Bool, delta: Bool, vi: U32,
      ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32, args: List<&2, U32>,
      fu: U32, pp: U32, mn: U32, mk: U32, cn: U32, p5: P5, ctx: List<&2, U32>}
  DLs{xs: List<&2, U32>, ys: List<&2, U32>, ctx: List<&2, U32>}
  DLs1{y: U32, xt: List<&2, U32>, yt: List<&2, U32>, ctx: List<&2, U32>}
  DLs2{wx: U32, xt: List<&2, U32>, yt: List<&2, U32>, ctx: List<&2, U32>}
  DLs3{xt: List<&2, U32>, yt: List<&2, U32>, ctx: List<&2, U32>}
  DLs4{go: Bool, t: L.Tri, xt: List<&2, U32>, yt: List<&2, U32>, ctx: List<&2, U32>}
  # index comparison answered; fire K or fall through
  WKGo{kok: Bool, isue: Bool, can: Bool, delta: Bool, vi: U32,
       ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32, args: List<&2, U32>,
       fu: U32, pp: U32, mn: U32, mk: U32, cn: U32, p5: P5, ctx: List<&2, U32>}
  # phase 2 gate: unit-like structure eta
  WPh2{isue: Bool, can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
       qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32, pp: U32,
       mn: U32, cn: U32, p5: P5, ctx: List<&2, U32>}
  # phase 3: literal arithmetic (Nat.add/sub/ble on two literals)
  WPh3{isar: Bool, aw: U32, isq: Bool, qneed: U32, can: Bool, delta: Bool,
       vi: U32, ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32,
       args: List<&2, U32>, fu: U32, p5: P5, ctx: List<&2, U32>}
  WLa{aw: U32, isq: Bool, qneed: U32, can: Bool, delta: Bool, vi: U32,
      ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32, args: List<&2, U32>,
      fu: U32, p5: P5, ctx: List<&2, U32>}
  WLb{r0: U32, aw: U32, isq: Bool, qneed: U32, can: Bool, delta: Bool,
      vi: U32, ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32,
      args: List<&2, U32>, fu: U32, p5: P5, ctx: List<&2, U32>}
  WLc{r1: U32, aw: U32, isq: Bool, qneed: U32, can: Bool, delta: Bool,
      vi: U32, ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32,
      args: List<&2, U32>, fu: U32, p5: P5, ctx: List<&2, U32>}
  WLd{na: T.Ex, aw: U32, isq: Bool, qneed: U32, can: Bool, delta: Bool,
      vi: U32, ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32,
      args: List<&2, U32>, fu: U32, p5: P5, ctx: List<&2, U32>}
  WLGo{arok: Bool, aw: U32, da: List<&2, U32>, db: List<&2, U32>,
       isq: Bool, qneed: U32, can: Bool, delta: Bool, vi: U32,
       ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32, args: List<&2, U32>,
       fu: U32, p5: P5, ctx: List<&2, U32>}
  # phase 4: quotient reduction (Quot.lift / Quot.ind on Quot.mk)
  WPh4{isq: Bool, qneed: U32, can: Bool, delta: Bool, vi: U32,
       ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32, args: List<&2, U32>,
       fu: U32, p5: P5, ctx: List<&2, U32>}
  WQ1{qneed: U32, can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
      qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32, p5: P5, ctx: List<&2, U32>}
  WQ2{qneed: U32, can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
      qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32, p5: P5, ctx: List<&2, U32>}
  WQGo{qok: Bool, fv: U32, vv: U32, qneed: U32, can: Bool, delta: Bool,
       vi: U32, ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32,
       args: List<&2, U32>, fu: U32, p5: P5, ctx: List<&2, U32>}
  # ---- phase 5: iota ----
  WPh5{p5: P5, can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
       qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32, ctx: List<&2, U32>}
  WI1{need: U32, ind: U32, pp: U32, mk: U32, cn: U32, us: List<&2, U32>,
      can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
      qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32, ctx: List<&2, U32>}
  WI2{need: U32, ind: U32, pp: U32, mk: U32, cn: U32, us: List<&2, U32>,
      can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
      qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32, ctx: List<&2, U32>}
  WI2Go{islit: Bool, d: List<&2, U32>, orig: U32, need: U32, ind: U32,
        pp: U32, mk: U32, cn: U32, us: List<&2, U32>, can: Bool,
        delta: Bool, vi: U32, ps: List<&2, U32>, qs: List<&2, L.LN>,
        e: U32, args: List<&2, U32>, fu: U32, ctx: List<&2, U32>}
  WI2b{need: U32, ind: U32, pp: U32, mk: U32, cn: U32, us: List<&2, U32>,
       can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
       qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32, ctx: List<&2, U32>}
  WI3{need: U32, ind: U32, pp: U32, mk: U32, cn: U32, us: List<&2, U32>,
      can: Bool, delta: Bool, vi: U32, ps: List<&2, U32>,
      qs: List<&2, L.LN>, e: U32, args: List<&2, U32>, fu: U32, ctx: List<&2, U32>}
  WIGo{ok2: Bool, fields: List<&2, U32>, recsl: List<&2, U32>, ci: U32,
       ccty: U32, need: U32, pp: U32, mk: U32, cn: U32,
       us: List<&2, U32>, can: Bool, delta: Bool, vi: U32,
       ps: List<&2, U32>, qs: List<&2, L.LN>, e: U32,
       args: List<&2, U32>, fu: U32, ctx: List<&2, U32>}
  # ---- definitional equality (infer.bend's defeq) ----
  # entry: fuel guard, same-index shortcut, then fetch both sides
  DSub{z0: Bool, same: Bool, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  # the closed-pair YES cache (Lean's equivalence manager, restricted to
  # closed terms: an open pair's answer can depend on the binder types)
  DSc0{xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DSc0b{hit0: Bool, cl: Bool, ch: U32, xi: U32, yi: U32, ctx: List<&2, U32>,
        fu: U32}
  DSc1{hit: Bool, cl: Bool, ch: U32, xi: U32, yi: U32, ctx: List<&2, U32>,
       fu: U32}
  DSRec{cl: Bool, ch: U32, xi: U32, yi: U32}
  # Lean's proof-by-reflection path (is_def_eq_core): a closed `t =?= true`
  # first evaluates t fully -- `Eq.refl true : decide p = true`, the shape
  # of every omega/decide certificate. YES if it reaches `true`, else the
  # ordinary comparison
  DDc0{cl: Bool, ch: U32, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DDc1{xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DDc2{xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DDc3{tru: Bool, cl: Bool, ch: U32, xi: U32, yi: U32, ctx: List<&2, U32>,
       fu: U32}
  DDc3x{tru: Bool, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DEx{xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DEy{xn: T.Ex, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  # ---- is_def_eq_core (the port): whnf_core both sides (cheap proj,
  # full-whnf recursor majors), quick, proof irrelevance, the lazy delta
  # loop to a genuine stall, then the structural tail on the stalled pair
  DE2{yi: U32, ctx: List<&2, U32>, fu: U32}
  DE3{wx: U32, ctx: List<&2, U32>, fu: U32}
  DE3b{same: Bool, wx: U32, wy: U32, ctx: List<&2, U32>, fu: U32}
  DE3c{wx: U32, wy: U32, ctx: List<&2, U32>, fu: U32}
  DE3d{yes: Bool, wx: U32, wy: U32, ctx: List<&2, U32>, fu: U32}
  DEL{x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  DE4{x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  DE4b{yes: Bool, nopair: Bool, x: U32, y: U32, ctx: List<&2, U32>,
       fu: U32}
  DE5{ctx: List<&2, U32>, fu: U32}
  DE6{b: U32, ctx: List<&2, U32>, fu: U32}
  DE7{wa: U32, ctx: List<&2, U32>, fu: U32}
  DE7b{same: Bool, wa: U32, wb: U32, ctx: List<&2, U32>, fu: U32}
  PI6h{no: Bool, yes: Bool, cl: Bool, x: U32, y: U32, ctx: List<&2, U32>,
       fu: U32}
  # after the stall: whnf_core with FULL whnf under projections (Lean's
  # second whnf_core pass); a changed pair re-enters is_def_eq_core
  DPr0{x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  DPq1{x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  DPq2{tn1: U32, i1: U32, s1: U32, x: U32, y: U32, ctx: List<&2, U32>,
       fu: U32}
  DPq3{same: Bool, s1: U32, s2: U32, x: U32, y: U32, ctx: List<&2, U32>,
       fu: U32}
  DPq4{s1: U32, s2: U32, x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  DPq4b{yes: Bool, nopair: Bool, s1: U32, s2: U32, x: U32, y: U32,
        ctx: List<&2, U32>, fu: U32}
  DPq4x{x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  DPq5p{x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  DPq6{a: U32, b: U32, x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  DPq7{ha: T.Ex, sa: List<&2, U32>, a: U32, b: U32, x: U32, y: U32,
       ctx: List<&2, U32>, fu: U32}
  DPq8{cc: Bool, pa: U32, sa: List<&2, U32>, pb: U32, sb: List<&2, U32>,
       a: U32, b: U32, x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  DPq5{yes: Bool, x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  DPr1{left: Bool, chg: Bool, x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  DPr2{left: Bool, chg: Bool, tn: U32, i: U32, s: U32, sargs: List<&2, U32>,
       x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  DPr3{left: Bool, chg: Bool, x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  DPr2b{same: Bool, left: Bool, chg: Bool, tn: U32, i: U32, s: U32,
        sargs: List<&2, U32>, x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  DPr3b{left: Bool, chg: Bool, x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  DPr4{left: Bool, chg: Bool, x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  # binders: domains (DSub), then bodies under the binder (DSub)
  DAl3g{no: Bool, d1: L.Tri, b1: U32, b2: U32, t1: U32, ctx: List<&2, U32>,
        fu: U32}
  # is_def_eq_app: the functions, then the arguments, each by DSub
  DAp1{f1: U32, a1: U32, f2: U32, a2: U32, xi: U32, yi: U32,
       ctx: List<&2, U32>, fu: U32}
  DAp2{yes: Bool, f1: U32, a1: U32, f2: U32, a2: U32, xi: U32, yi: U32,
       ctx: List<&2, U32>, fu: U32}
  DAp3{f1: U32, a1: U32, f2: U32, a2: U32, xi: U32, yi: U32,
       ctx: List<&2, U32>, fu: U32}
  DAp4{yes: Bool, f1: U32, a1: U32, f2: U32, a2: U32, xi: U32, yi: U32,
       ctx: List<&2, U32>, fu: U32}
  DApN1{t: L.Tri, xi: U32, yi: U32, ctx: List<&2, U32>}
  # is_def_eq_app by spines: the heads, then the arguments first to last
  DAs1{xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DAs2{hx: U32, sx: List<&2, U32>, xi: U32, yi: U32, ctx: List<&2, U32>,
       fu: U32}
  DAs3{same: Bool, hx: U32, hy: U32, sx: List<&2, U32>, sy: List<&2, U32>,
       xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DAs4{sx: List<&2, U32>, sy: List<&2, U32>, xi: U32, yi: U32,
       ctx: List<&2, U32>, fu: U32}
  DAs5{yes: Bool, sx: List<&2, U32>, sy: List<&2, U32>, xi: U32, yi: U32,
       ctx: List<&2, U32>, fu: U32}
  # is_def_eq_binding: consecutive binders of one kind in one pass
  DBd1{b1: U32, b2: U32, ctx: List<&2, U32>, fu: U32}
  DBd2{xn: T.Ex, b1: U32, b2: U32, ctx: List<&2, U32>, fu: U32}
  DApN2{t: L.Tri, cx: Bool, xi: U32, yi: U32, ctx: List<&2, U32>}
  # Pi/Pi: domains then bodies under the binder
  DAl2{w1: U32, t1: U32, t2: U32, b1: U32, b2: U32, ctx: List<&2, U32>,
       fu: U32}
  DAl2b{w1: U32, t1: U32, t2: U32, b1: U32, b2: U32, ctx: List<&2, U32>,
        fu: U32}
  DAl3{b1: U32, b2: U32, t1: U32, ctx: List<&2, U32>, fu: U32}
  DAl4{d1: L.Tri, b1: U32, b2: U32, t1: U32, ctx: List<&2, U32>, fu: U32}
  DAl5{d1: L.Tri, w3: U32, b1: U32, b2: U32, t1: U32, ctx: List<&2, U32>,
       fu: U32}
  DAl6{d1: L.Tri}
  # Lam/Lam: bodies under the binder
  DLm2{b1: U32, b2: U32, t1: U32, ctx: List<&2, U32>, fu: U32}
  DLm3{w3: U32, b1: U32, b2: U32, t1: U32, ctx: List<&2, U32>, fu: U32}
  DLm3b{w3: U32, b1: U32, b2: U32, t1: U32, ctx: List<&2, U32>, fu: U32}
  DLm4{}
  # App/App: function sides (unless they already agree), then arguments
  DAq1{f1: U32, f2: U32, a1: U32, a2: U32, xi: U32, yi: U32,
       ctx: List<&2, U32>, fu: U32}
  DAqGo{fsame: Bool, f1: U32, f2: U32, a1: U32, a2: U32, xi: U32, yi: U32,
        ctx: List<&2, U32>, fu: U32}
  DAq2{f1: U32, f2: U32, a1: U32, a2: U32, xi: U32, yi: U32,
       ctx: List<&2, U32>, fu: U32}
  DAq3{w1: U32, f1: U32, f2: U32, a1: U32, a2: U32, xi: U32, yi: U32,
       ctx: List<&2, U32>, fu: U32}
  DAq3b{a1: U32, a2: U32, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DAq4{d1: L.Tri, a1: U32, a2: U32, xi: U32, yi: U32, ctx: List<&2, U32>,
       fu: U32}
  DAq5{d1: L.Tri, w3: U32, a1: U32, a2: U32, xi: U32, yi: U32,
       ctx: List<&2, U32>, fu: U32}
  DAq6{d1: L.Tri, xi: U32, yi: U32, ctx: List<&2, U32>}
  # DAqGo{True} argument congruence (Lean's is_def_eq_args): if BOTH
  # arguments are applications of the same constant (same levels, same
  # arity), walk a worklist of argument pairs: same-head pairs are expanded,
  # any other pair is a leaf compared by full whnf + defeq. All leaves YES =>
  # YES (congruence). The first non-YES abandons the attempt and falls back
  # to the unchanged whnf+defeq path -- never trusted as NO.
  DAqH1{a1: U32, a2: U32, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DAqH2{h1: T.Ex, s1: List<&2, U32>, a1: U32, a2: U32, xi: U32, yi: U32,
        ctx: List<&2, U32>, fu: U32}
  DAqH3{gate: Bool, s1: List<&2, U32>, s2: List<&2, U32>, a1: U32, a2: U32,
        xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DCgL{xs: List<&2, U32>, ys: List<&2, U32>, a1: U32, a2: U32, xi: U32,
       yi: U32, ctx: List<&2, U32>, fu: U32}
  DCgS1{x: U32, y: U32, xt: List<&2, U32>, yt: List<&2, U32>, a1: U32,
        a2: U32, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DCgS2{h1: T.Ex, s1: List<&2, U32>, x: U32, y: U32, xt: List<&2, U32>,
        yt: List<&2, U32>, a1: U32, a2: U32, xi: U32, yi: U32,
        ctx: List<&2, U32>, fu: U32}
  DCgS3{gate: Bool, nb: Bool, s1: List<&2, U32>, s2: List<&2, U32>, x: U32,
        y: U32,
        xt: List<&2, U32>, yt: List<&2, U32>, a1: U32, a2: U32, xi: U32,
        yi: U32, ctx: List<&2, U32>, fu: U32}
  DCgS4{bail: Bool, x: U32, y: U32, xt: List<&2, U32>, yt: List<&2, U32>,
        a1: U32, a2: U32, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DCgW1{y: U32, xt: List<&2, U32>, yt: List<&2, U32>, a1: U32, a2: U32,
        xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DCgW2{wx: U32, xt: List<&2, U32>, yt: List<&2, U32>, a1: U32, a2: U32,
        xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DCgK{xt: List<&2, U32>, yt: List<&2, U32>, a1: U32, a2: U32, xi: U32,
       yi: U32, ctx: List<&2, U32>, fu: U32}
  DCgK2{yes: Bool, xt: List<&2, U32>, yt: List<&2, U32>, a1: U32, a2: U32,
        xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  # lazy-delta args-first (Lean's isDefEqArgs): collect both spines; if the
  # heads are the SAME constant with equal arity, compare arguments pairwise
  # by defeq. All-yes answers YES soundly (congruence); anything else FALLS
  # BACK to the unchanged DAq1 path -- never a premature NO, since a
  # constant-ignoring function could still make the two equal after
  # unfolding. Purely additive: only turns declines into accepts.
  DLz1{f1: U32, f2: U32, a1: U32, a2: U32, xi: U32, yi: U32,
       ctx: List<&2, U32>, fu: U32}
  DLz2{hx: T.Ex, sx: List<&2, U32>, f1: U32, f2: U32, a1: U32, a2: U32,
       xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DLz2b{samehd: Bool, sx: List<&2, U32>, sy: List<&2, U32>, f1: U32,
        f2: U32, a1: U32, a2: U32, xi: U32, yi: U32, ctx: List<&2, U32>,
        fu: U32}
  DStr0{ok: Bool, left: Bool, d: List<&2, U32>, other: U32,
        ctx: List<&2, U32>, fu: U32}
  DStr1{left: Bool, other: U32, ctx: List<&2, U32>, fu: U32}
  DStr2{left: Bool, other: U32, ctx: List<&2, U32>, fu: U32}
  DStr3{}
  DLzD{f1: U32, f2: U32, a1: U32, a2: U32, xi: U32, yi: U32,
       ctx: List<&2, U32>, fu: U32}
  DLzD2{yes: Bool, f1: U32, f2: U32, a1: U32, a2: U32, xi: U32, yi: U32,
        ctx: List<&2, U32>, fu: U32}
  DLzA{xs: List<&2, U32>, ys: List<&2, U32>, f1: U32, f2: U32, a1: U32,
       a2: U32, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DLzA0{same: Bool, xh: U32, yh: U32, xt: List<&2, U32>, yt: List<&2, U32>,
        f1: U32, f2: U32, a1: U32, a2: U32, xi: U32, yi: U32,
        ctx: List<&2, U32>, fu: U32}
  DLzAp{xh: U32, yh: U32, xt: List<&2, U32>, yt: List<&2, U32>,
        f1: U32, f2: U32, a1: U32, a2: U32, xi: U32, yi: U32,
        ctx: List<&2, U32>, fu: U32}
  DLzAq{yes: Bool, xh: U32, yh: U32, xt: List<&2, U32>, yt: List<&2, U32>,
        f1: U32, f2: U32, a1: U32, a2: U32, xi: U32, yi: U32,
        ctx: List<&2, U32>, fu: U32}
  DLzAx{xt: List<&2, U32>, yt: List<&2, U32>, yh: U32, f1: U32, f2: U32,
        a1: U32, a2: U32, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DLzAy{xt: List<&2, U32>, yt: List<&2, U32>, wx: U32, f1: U32, f2: U32,
        a1: U32, a2: U32, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DLzAk{xt: List<&2, U32>, yt: List<&2, U32>, f1: U32, f2: U32, a1: U32,
        a2: U32, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DLzAk2{yes: Bool, xt: List<&2, U32>, yt: List<&2, U32>, f1: U32, f2: U32,
         a1: U32, a2: U32, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  # projection/projection: same (type,index) -> compare structures by defeq,
  # YES answers YES (congruence); else fall back to the DC1 catch-all.
  DPjDecide{sp: Bool, xn: T.Ex, yn: T.Ex, xi: U32, yi: U32,
            ctx: List<&2, U32>, fu: U32}
  DPjK{xn: T.Ex, yn: T.Ex, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DPjK2{yes: Bool, xn: T.Ex, yn: T.Ex, xi: U32, yi: U32,
        ctx: List<&2, U32>, fu: U32}
  # second attempt: compare the two structures WHNF'd (defeq's precondition)
  # -- a stuck projection keeps its ORIGINAL structure, so one side can be
  # `(Nat.brecOn.go m n F).1` and the other `(Nat.rec .. n).1`; they agree
  # only after unfolding. Still YES-only; otherwise the catch-all.
  DPjW1{xn: T.Ex, yn: T.Ex, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DPjW2{w1: U32, xn: T.Ex, yn: T.Ex, xi: U32, yi: U32, ctx: List<&2, U32>,
        fu: U32}
  DPjW3{xn: T.Ex, yn: T.Ex, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DPjW4{yes: Bool, xn: T.Ex, yn: T.Ex, xi: U32, yi: U32,
        ctx: List<&2, U32>, fu: U32}
  # Const/Const: shared type then its universe
  DCn2{a: U32, us: List<&2, U32>, b: U32, vs: List<&2, U32>, ta: U32,
       tb: U32, ctx: List<&2, U32>}
  DCn3x{a: U32, us: List<&2, U32>, b: U32, vs: List<&2, U32>, ta: U32,
        tb: U32, samety: Bool, ctx: List<&2, U32>}
  DCn3{a: U32, us: List<&2, U32>, b: U32, vs: List<&2, U32>, ta: U32,
       tb: U32, samety: Bool}
  DCn4{a: U32, us: List<&2, U32>, b: U32, vs: List<&2, U32>, ta: U32,
       tb: U32, samety: Bool}
  # dq_or_irrel: proof-irrelevance fallback on a non-yes verdict
  DIr1{t: L.Tri, xi: U32, yi: U32, ctx: List<&2, U32>}
  # an eta comparison (lambda against a non-lambda) that did not answer YES:
  # proof irrelevance may still settle it -- Lean tries it on every pair
  DEtX{xi: U32, yi: U32, ctx: List<&2, U32>}
  DEtX2{yes: Bool, t: L.Tri, xi: U32, yi: U32, ctx: List<&2, U32>}
  DIr2{t: L.Tri, hx: T.Ex, nx: U32, yi: U32, xi: U32, ctx: List<&2, U32>}
  DIrEt{eta: Bool, gate: Bool, t: L.Tri, xi: U32, yi: U32,
        ctx: List<&2, U32>}
  DIrE1{gate: Bool, t: L.Tri, xi: U32, yi: U32, ctx: List<&2, U32>}
  DIrE2{xn: T.Ex, gate: Bool, t: L.Tri, xi: U32, yi: U32,
        ctx: List<&2, U32>}
  DIrE3{gate: Bool, t: L.Tri, xi: U32, yi: U32, ctx: List<&2, U32>}
  DIrGo{gate: Bool, t: L.Tri, xi: U32, yi: U32, ctx: List<&2, U32>}
  DIr4{t: L.Tri, yi: U32, ctx: List<&2, U32>}
  DTyF{x: U32, ctx: List<&2, U32>}
  DTyF2{none: Bool, x: U32, ctx: List<&2, U32>}
  DTyF3{old: U32}
  DTyFs{x: U32, ctx: List<&2, U32>}
  DIr5{t: L.Tri, rx: U32, ctx: List<&2, U32>}
  DIr6{pz: Bool, t: L.Tri, rx: U32, ry: U32, ctx: List<&2, U32>}
  # compare the two TYPES with full defeq (whnf'd), not structurally:
  # `Nat.le (succ n) (succ n)` and `n < n + 1` are the same proposition only
  # after unfolding LT.lt and +. The trie engine cannot do this (infer and
  # defeq may not recurse into each other); frames can.
  DIr5x{ok: Bool, t: L.Tri, rx: U32, ry: U32, ctx: List<&2, U32>}
  # Lean's order: x's type must be a Prop BEFORE the types are compared;
  # comparing first lets that defeq fall back to proof irrelevance on the
  # types themselves, which climbs Sort u, Sort u+1, .. without end
  DIr5p{t: L.Tri, rx: U32, ry: U32, ctx: List<&2, U32>}
  DIr5q{zero: Bool, t: L.Tri, rx: U32, ry: U32, ctx: List<&2, U32>}
  DIr5r{unk: Bool, zy: Bool, t: L.Tri, rx: U32, ry: U32,
        ctx: List<&2, U32>}
  DIr5s{t: L.Tri, rx: U32, ry: U32, ctx: List<&2, U32>}
  DIr5u{t: L.Tri, rx: U32, ry: U32, ctx: List<&2, U32>}
  PI1{cl: Bool, x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  PI1g{has: Bool, tx: U32, cl: Bool, x: U32, y: U32, ctx: List<&2, U32>,
       fu: U32}
  PI2{tx: U32, cl: Bool, x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  PI2g{prf: Bool, tx: U32, cl: Bool, x: U32, y: U32, ctx: List<&2, U32>,
       fu: U32}
  PI3{tx: U32, cl: Bool, x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  PI3g{has: Bool, tx: U32, ty: U32, cl: Bool, x: U32, y: U32,
       ctx: List<&2, U32>, fu: U32}
  PI6{cl: Bool, x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  PI6g{yes: Bool, cl: Bool, x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  DIr5v{un: Bool, zy: Bool, t: L.Tri, rx: U32, ry: U32, ctx: List<&2, U32>}
  DIr5w{t: L.Tri, rx: U32, ry: U32, ctx: List<&2, U32>}
  DIr5wg{bad: Bool, t: L.Tri, rx: U32, ry: U32, ctx: List<&2, U32>}
  DIr5wf{t: L.Tri, rx: U32, ry: U32, ctx: List<&2, U32>}
  DIr5wz{t: L.Tri, rx: U32, ry: U32, ctx: List<&2, U32>}
  DIr5y{t: L.Tri, rx: U32, ry: U32, ctx: List<&2, U32>}
  DIr5z{t: L.Tri, rx: U32, ry: U32, wx: U32, ctx: List<&2, U32>}
  DIr7{pz: Bool, t: L.Tri, both: Bool, sq: L.Tri}
  # BVar/BVar with type analysis (proof irrelevance, unit eta, denial)
  DBv1{a: U32, b: U32, tb: U32, taok: Bool, tbok: Bool,
       ctx: List<&2, U32>}
  DBv2{a: U32, b: U32, la: U32, taok: Bool, tbok: Bool,
       ctx: List<&2, U32>}
  DBv3{a: U32, b: U32, lb: U32, taok: Bool, tbok: Bool,
       ctx: List<&2, U32>}
  DBv4{a: U32, b: U32, wa: U32, taok: Bool, tbok: Bool,
       ctx: List<&2, U32>}
  DBv5{a: U32, b: U32, wa: U32, wb: U32, taok: Bool, tbok: Bool,
       ctx: List<&2, U32>}
  DBv6{a: U32, b: U32, wa: U32, wb: U32, samety: Bool, both: Bool,
       ctx: List<&2, U32>}
  DBv7{a: U32, b: U32, wa: U32, wb: U32, samety: Bool, both: Bool, rtok: Bool,
       ctx: List<&2, U32>}
  DBv8{a: U32, b: U32, wa: U32, wb: U32, samety: Bool, both: Bool, rtok: Bool,
       ctx: List<&2, U32>}
  DBv9{a: U32, b: U32, wa: U32, wb: U32, samety: Bool, both: Bool, part1: Bool,
       part1n: Bool,
       ctx: List<&2, U32>}
  DBv10{a: U32, b: U32, wa: U32, wb: U32, samety: Bool, both: Bool,
        isprop: Bool, notprop: Bool, ctx: List<&2, U32>}
  DBvGo{deep: Bool, yes: Bool, t: L.Tri, wa: U32, wb: U32,
        ctx: List<&2, U32>}
  DBvT{}
  # function eta, lambda left / lambda right
  DEtL1{t1: U32, b1: U32, ctx: List<&2, U32>, fu: U32}
  DEtL2{ly: U32, t1: U32, b1: U32, ctx: List<&2, U32>, fu: U32}
  DEtL3{t1: U32, b1: U32, ctx: List<&2, U32>, fu: U32}
  DEtL4{ap: U32, t1: U32, ctx: List<&2, U32>, fu: U32}
  DEtL5{w1: U32, t1: U32, ctx: List<&2, U32>, fu: U32}
  DEtL6{}
  DEtR1{t2: U32, b2: U32, ctx: List<&2, U32>, fu: U32}
  DEtR2{lx: U32, t2: U32, b2: U32, ctx: List<&2, U32>, fu: U32}
  DEtR3{t2: U32, b2: U32, ctx: List<&2, U32>, fu: U32}
  DEtR4{ap: U32, t2: U32, b2: U32, ctx: List<&2, U32>, fu: U32}
  DEtR5{w1: U32, t2: U32, ctx: List<&2, U32>, fu: U32}
  # literal against a numeral in constructor form
  DNtL1{d: List<&2, U32>, ctx: List<&2, U32>, fu: U32}
  DNtL2{d: List<&2, U32>, wy: U32, ctx: List<&2, U32>, fu: U32}
  DNtL3{islit: Bool, d: List<&2, U32>, wy: U32, ctx: List<&2, U32>,
        fu: U32}
  DNtL4{islit: Bool, wy: U32, ctx: List<&2, U32>, fu: U32}
  DNtL5{islit: Bool}
  DNtR1{d: List<&2, U32>, ctx: List<&2, U32>, fu: U32}
  DNtR2{d: List<&2, U32>, wx: U32, ctx: List<&2, U32>, fu: U32}
  DNtR3{islit: Bool, d: List<&2, U32>, wx: U32, ctx: List<&2, U32>,
        fu: U32}
  DNtR4{islit: Bool, wx: U32, ctx: List<&2, U32>, fu: U32}
  # the structural catch-all: spines, swap, structure eta or denial
  DC1{xn: T.Ex, yn: T.Ex, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DC2x{xn: T.Ex, yn: T.Ex, hx: T.Ex, sx: List<&2, U32>, xi: U32, yi: U32,
       ctx: List<&2, U32>, fu: U32}
  DCGo{eok: Bool, pxi: U32, pyi: U32, pxn: T.Ex, pyn: T.Ex, hd: T.Ex,
       hdy: T.Ex, spx: List<&2, U32>, spy: List<&2, U32>, cp: U32,
       cnf: U32, cind: U32, ctx: List<&2, U32>, fu: U32}
  DCe1{tk: List<&2, U32>, cnf: U32, cind: U32, pyi: U32, pxi: U32,
       ctx: List<&2, U32>, fu: U32}
  DCe3{}
  DSub2{pxi: U32, ctx: List<&2, U32>, fu: U32}
  # rigidity chain: maybe rec_stuck on either side
  DCr1{cx: Bool, pxn: T.Ex, hd: T.Ex, spx: List<&2, U32>, pxi: U32,
       pyi: U32, pyn: T.Ex, hdy: T.Ex, spy: List<&2, U32>,
       ctx: List<&2, U32>, fu: U32}
  DCr2{cx: Bool, pxi: U32, pyi: U32, pyn: T.Ex, hdy: T.Ex,
       spy: List<&2, U32>, ctx: List<&2, U32>, fu: U32}
  DCr2b{cpx: Bool, pxi: U32, pyi: U32, pyn: T.Ex, hdy: T.Ex,
        spy: List<&2, U32>, ctx: List<&2, U32>, fu: U32}
  DCr3{pxi: U32, pyi: U32, pyn: T.Ex, hdy: T.Ex, spy: List<&2, U32>,
       ctx: List<&2, U32>, fu: U32}
  DCr3Go{cy: Bool, pyn: T.Ex, hdy: T.Ex, spy: List<&2, U32>, pxi: U32,
         pyi: U32, ctx: List<&2, U32>, fu: U32}
  DCr5{pxi: U32, pyi: U32, ctx: List<&2, U32>, fu: U32}
  # the rigid denial: type oracle + universe, deny outside Prop
  DRg1{cheaprig: Bool, pxi: U32, pyi: U32, ctx: List<&2, U32>, fu: U32}
  DRg2{pxi: U32, pyi: U32, ctx: List<&2, U32>, fu: U32}
  DRg3{rtok: Bool, pxi: U32, pyi: U32, ctx: List<&2, U32>, fu: U32}
  # one reduction of each side at a shape mismatch, then dq_or_irrel
  DDl1{isno: Bool, pxi: U32, pyi: U32, ctx: List<&2, U32>, fu: U32}
  DDl2{pyi: U32, pxi: U32, ctx: List<&2, U32>}
  DDl3{w1: U32, pxi: U32, pyi: U32, ctx: List<&2, U32>}
  DDl4{pxi: U32, pyi: U32, ctx: List<&2, U32>}
  # rec_stuck: a recursor application that can never reduce
  RSGo{ok0: Bool, maj: U32, pp: U32, ni: U32, mn: U32, kf: U32,
       rcty: U32, ind: U32, sargs: List<&2, U32>, ctx: List<&2, U32>}
  RS2{pp: U32, ni: U32, mn: U32, kf: U32, rcty: U32, ind: U32,
      sargs: List<&2, U32>, ctx: List<&2, U32>}
  RS3{wm2: U32, pp: U32, ni: U32, mn: U32, kf: U32, rcty: U32, ind: U32,
      sargs: List<&2, U32>, ctx: List<&2, U32>}
  RS4{mn2: T.Ex, pp: U32, ni: U32, mn: U32, kf: U32, rcty: U32, ind: U32,
      sargs: List<&2, U32>, ctx: List<&2, U32>}
  RSK{dok: Bool, base: Bool, pp: U32, ni: U32, mn: U32, rcty: U32,
      sargs: List<&2, U32>, ctx: List<&2, U32>}
  RS5{base: Bool, pp: U32, ni: U32, mn: U32, sargs: List<&2, U32>, ctx: List<&2, U32>}
  RS6{pok: Bool, base: Bool, pp: U32, ni: U32, mn: U32,
      sargs: List<&2, U32>, ctx: List<&2, U32>}
  RS7{base: Bool, pok: Bool}
  # pairwise index comparison with the constant denial (k_idx_cmp)
  KI0{xs: List<&2, U32>, ys: List<&2, U32>, acc: L.Tri, ctx: List<&2, U32>}
  KI1{a: U32, b: U32, ta: List<&2, U32>, tb: List<&2, U32>, acc: L.Tri, ctx: List<&2, U32>}
  KI2{an: T.Ex, a: U32, b: U32, ta: List<&2, U32>, tb: List<&2, U32>,
      acc: L.Tri, ctx: List<&2, U32>}
  KI3b{precond: Bool, t1: U32, t2: U32, a: U32, b: U32, ta: List<&2, U32>,
       tb: List<&2, U32>, acc: L.Tri, ctx: List<&2, U32>}
  # the cheap comparison was inconclusive: full defeq of the two indices
  # (whnf both, then DSub under the term's context); NO is sound here
  # because DSub receives fully reduced inputs
  KIF{full: Bool, t: L.Tri, precond: Bool, t1: U32, t2: U32, a: U32,
      b: U32, ta: List<&2, U32>, tb: List<&2, U32>, acc: L.Tri,
      ctx: List<&2, U32>}
  KIF2{precond: Bool, t1: U32, t2: U32, b: U32, ta: List<&2, U32>,
       tb: List<&2, U32>, acc: L.Tri, ctx: List<&2, U32>}
  KIF3{wa: U32, precond: Bool, t1: U32, t2: U32, ta: List<&2, U32>,
       tb: List<&2, U32>, acc: L.Tri, ctx: List<&2, U32>}
  KIF4{precond: Bool, t1: U32, t2: U32, ta: List<&2, U32>,
       tb: List<&2, U32>, acc: L.Tri, ctx: List<&2, U32>}
  KIGo2{precond: Bool, e2: L.Tri, t1: U32, t2: U32, ta: List<&2, U32>,
        tb: List<&2, U32>, acc: L.Tri, ctx: List<&2, U32>}
  KI4{e2: L.Tri, t1: U32, ta: List<&2, U32>, tb: List<&2, U32>,
      acc: L.Tri, ctx: List<&2, U32>}
  KI5{e2: L.Tri, t1: U32, tqy: Bool, ta: List<&2, U32>,
      tb: List<&2, U32>, acc: L.Tri}
  KI6{e2: L.Tri, tqy: Bool, ta: List<&2, U32>, tb: List<&2, U32>,
      acc: L.Tri, ctx: List<&2, U32>}
  # ---- type inference (infer.bend's infer) ----
  ISub{xi: U32, ctx: List<&2, U32>, fu: U32}
  ISubC{xi: U32, ctx: List<&2, U32>, fu: U32}
  ISubD{ok: Bool, xi: U32, ctx: List<&2, U32>, fu: U32}
  ISubE{ok: Bool, xi: U32, cid: U32, ctx: List<&2, U32>, fu: U32}
  ISubF{ok: Bool, io: Bool, xi: U32, ctx: List<&2, U32>, fu: U32}
  ISubF2{ok2: Bool, io: U32, xi: U32, pk: U32, ctx: List<&2, U32>, fu: U32}
  ISubM{hit: Bool, cl: Bool, t: U32, tok: Bool, xi: U32, key: U32,
        ctx: List<&2, U32>, fu: U32}
  IMemo{cl: Bool, key: U32}
  IEvGo{z0: Bool, xi: U32, ctx: List<&2, U32>, fu: U32}
  IEv{xi: U32, ctx: List<&2, U32>, fu: U32}
  IAl3b{ty: U32, b: U32, ra: U32, raok: Bool, ctx: List<&2, U32>,
        fu: U32}
  IAl5b{ka: T.Ex, ra: U32, raok: Bool, rb: U32, rbok: Bool,
        ctx: List<&2, U32>, fu: U32}
  IStrGo{bad: Bool, sn: U32}
  INatGo{bad: Bool}
  # whnf of `Nat.succ a`: when `a` whnfs to a literal, the result is the
  # literal a+1 (Lean's kernel does the same). Without it
  # `Nat.ble (Nat.succ 55296) 4294967296` -- every `Nat.decLt` -- missed the
  # literal accelerator and recursed in unary. w3 is the unchanged pipeline.
  WScB{issuc: Bool, a0: U32, w3: KF, ctx: List<&2, U32>}
  WSc2{w3: KF, ctx: List<&2, U32>}
  WSc3{w3: KF, ctx: List<&2, U32>}
  WSc4{islit: Bool, d: List<&2, U32>, w3: KF, ctx: List<&2, U32>}
  ICnGo{bad: Bool, ti: U32, ps: List<&2, U32>, qs: List<&2, L.LN>}
  # wrap the incoming result register as an inference result
  IWrap{ok: Bool}
  ISrtGo{un: Bool, u: L.LN}
  IAl2{ty: U32, b: U32, ctx: List<&2, U32>, fu: U32}
  IAl3{ty: U32, b: U32, ra: U32, raok: Bool, ctx: List<&2, U32>, fu: U32}
  IAl4{ty: U32, ka: T.Ex, ra: U32, raok: Bool, ctx: List<&2, U32>,
       fu: U32}
  IAl5{ka: T.Ex, ra: U32, raok: Bool, rb: U32, rbok: Bool,
       ctx: List<&2, U32>, fu: U32}
  IAl6{ka: T.Ex, kb: T.Ex, ra: U32, raok: Bool, rb: U32, rbok: Bool}
  IAl7{ka: T.Ex, kb: T.Ex, nska: Bool, ra: U32, raok: Bool, rb: U32,
       rbok: Bool}
  IAlGo{allok: Bool, bad: Bool, ka: T.Ex, kb: T.Ex}
  ILm2{n: U32, ty: U32, bi: U32}
  ILmGo{ok: Bool, bty: U32, n: U32, ty: U32, bi: U32}
  IBv{ok: Bool}
  ILt2{ctx: List<&2, U32>, fu: U32}
  IAp2{a: U32, f: U32, ctx: List<&2, U32>, fu: U32}
  IAp3{a: U32, f: U32, rf: U32, rfok: Bool, ctx: List<&2, U32>, fu: U32}
  IAp3b{a: U32, f: U32, rf: U32, rfok: Bool, ctx: List<&2, U32>, fu: U32}
  # `f a` where f is `g a` (the same argument twice, e.g. a shared lambda
  # passed twice): f's inference just checked a under this very context --
  # its argument check is the last one run (defeq never infers) -- so a's
  # recorded type (the record slot, krec_slot) is reused, not re-inferred
  IApR{a: U32, node: T.Ex, rf: U32, rfok: Bool, ctx: List<&2, U32>, fu: U32}
  IApR2{hit: Bool, a: U32, node: T.Ex, rf: U32, rfok: Bool,
        ctx: List<&2, U32>, fu: U32}
  IApRr{a0: U32, a: U32, node: T.Ex, rf: U32, rfok: Bool,
        ctx: List<&2, U32>, fu: U32}
  IAp4{a: U32, node: T.Ex, rf: U32, rfok: Bool, ctx: List<&2, U32>,
       fu: U32}
  IAp5{a: U32, node: T.Ex, ra: U32, raok: Bool, rf: U32, rfok: Bool,
       ctx: List<&2, U32>, fu: U32}
  IAp5Go{isyes: Bool, a: U32, node: T.Ex, ra: U32, raok: Bool, rf: U32,
         rfok: Bool, ctx: List<&2, U32>, fu: U32}
  IAp5iq{a: U32, node: T.Ex, ra: U32, raok: Bool, rf: U32, rfok: Bool,
         ctx: List<&2, U32>, fu: U32}
  IAp5io{io: Bool, a: U32, node: T.Ex, ra: U32, raok: Bool, rf: U32,
         rfok: Bool, ctx: List<&2, U32>, fu: U32}
  IAp5c{a: U32, node: T.Ex, ra: U32, raok: Bool, rf: U32, rfok: Bool,
        ctx: List<&2, U32>, fu: U32}
  IAp5d{w1: U32, a: U32, node: T.Ex, ra: U32, raok: Bool, rf: U32,
        rfok: Bool, ctx: List<&2, U32>, fu: U32}
  IAp6{w1: U32, w2: U32, a: U32, node: T.Ex, ra: U32, raok: Bool, rf: U32,
       rfok: Bool, ctx: List<&2, U32>, fu: U32}
  IAp6Go{isyes: Bool, w1: U32, w2: U32, a: U32, node: T.Ex, ra: U32,
         raok: Bool, rf: U32, rfok: Bool, ctx: List<&2, U32>, fu: U32}
  IAp7{a: U32, node: T.Ex, ra: U32, raok: Bool, rf: U32, rfok: Bool,
       ctx: List<&2, U32>, fu: U32}
  IAp8{dq: L.Tri, a: U32, node: T.Ex, ra: U32, raok: Bool, rf: U32,
       rfok: Bool, ctx: List<&2, U32>, fu: U32}
  IAp9{hx: T.Ex, dq: L.Tri, a: U32, node: T.Ex, ra: U32, raok: Bool,
       rf: U32, rfok: Bool, ctx: List<&2, U32>, fu: U32}
  IAp10{bad: Bool, ok: Bool}
  IPj2{tn: U32, idx: U32, sx: U32, ctx: List<&2, U32>, fu: U32}
  IPj3{tn: U32, idx: U32, sx: U32, rs: U32, rsok: Bool,
       ctx: List<&2, U32>, fu: U32}
  IPj4{tn: U32, idx: U32, sx: U32, rs: U32, rsok: Bool,
       ctx: List<&2, U32>, fu: U32}
  IPj5{tn: U32, idx: U32, sx: U32, sty: T.Ex, rs: U32, rsok: Bool,
       ctx: List<&2, U32>, fu: U32}
  IPj6{ok: Bool, ppx: U32, ppd: U32, pr: U32, tn: U32, idx: U32, sx: U32,
       sargs: List<&2, U32>, rs: U32, ctx: List<&2, U32>}
  IPj7{lsr: U32, ok: Bool, ppx: U32, ppd: U32, pr: U32, tn: U32, idx: U32,
       sargs: List<&2, U32>, rs: U32, ctx: List<&2, U32>}
  IPj8{ok: Bool, ppx: U32, ppd: U32, pr: U32, idx: U32, rs: U32,
       ctx: List<&2, U32>}
  IPj9{pt: U32, ok: Bool, ppx: U32, ppd: U32, pr: U32, idx: U32, rs: U32,
       ctx: List<&2, U32>}
  IPj10{ok: Bool, ptok: Bool, isall: Bool, ppx: U32, ppd: U32, pr: U32, idx: U32,
        rs: U32, fldty: U32}
  IPjOut{ok: Bool, rity: U32, ok2: Bool}
  IPj5b{mism: Bool, tn: U32, idx: U32, sx: U32, hd: T.Ex, rs: U32,
        rsok: Bool, ctx: List<&2, U32>, fu: U32}
  SLX0{e: U32, ctx: List<&2, U32>}
  SLX0g{dec: Bool, u: L.LN, e: U32, ctx: List<&2, U32>}
  SLX1{u: L.LN}
  SLX1g{bad: Bool, u: L.LN}
  SLX2{u: L.LN}
  SLX3{u: L.LN}
  IPjQ{need: Bool, lsr: U32, ok: Bool, ppx: U32, ppd: U32, pr: U32, tn: U32,
       idx: U32, sx: U32, sargs: List<&2, U32>, rs: U32, ctx: List<&2, U32>}
  IPjR1{lsr: U32, ok: Bool, ppx: U32, ppd: U32, pr: U32, tn: U32,
        idx: U32, sx: U32, sargs: List<&2, U32>, rs: U32, ctx: List<&2, U32>}
  IPjR2{lsr: U32, ok: Bool, ppx: U32, ppd: U32, pr: U32, tn: U32,
        idx: U32, sx: U32, sargs: List<&2, U32>, rs: U32, ctx: List<&2, U32>}
  IPjR3{lsr: U32, ok: Bool, ppx: U32, ppd: U32, pr: U32, tn: U32,
        idx: U32, sx: U32, sargs: List<&2, U32>, rs: U32, ctx: List<&2, U32>}
  IPjR4{isall: Bool, lsr: U32, ok: Bool, ppx: U32, ppd: U32, pr: U32,
        tn: U32, idx: U32, sx: U32, sargs: List<&2, U32>, rs: U32,
        ctx: List<&2, U32>}
  IOut{}
  # ---- the typed-check path (check.bend's ck_typed .. ck_infer) ----
  CkT1{isthm: Bool, vi: U32, fu: U32}
  CkT2{isthm: Bool, ti1: U32, vi: U32}
  CkT3{isthm: Bool, ti1: U32, vi: U32, rty: U32, riok: Bool}
  CkT4{isthm: Bool, ti1: U32, vi: U32, rty: U32, riok: Bool}
  CkT5{isthm: Bool, ti1: U32, vi: U32, u: L.LN, rtybad: Bool}
  CkT6{isthm: Bool, ti1: U32, vi: U32, u: L.LN, rtybad: Bool,
       shape: U32, iscc: Bool}
  CkT7{b1: Bool, b2: Bool, ti1: U32, vi: U32}
  CkT8{novalue: Bool, ti1: U32, vi: U32}
  CkV2{vi: U32, fu: U32}
  CkEy0{xi: U32, tye: U32, ctx: List<&2, U32>, fu: U32}
  CkE8c{shape: U32, iscc: Bool, lt: U32, xi: U32, tye: U32,
        ctx: List<&2, U32>, fu: U32}
  CkVOut{}
  CkEx{xi: U32, tye: U32, ctx: List<&2, U32>, fu: U32}
  CkEy{xn: T.Ex, xi: U32, tye: U32, ctx: List<&2, U32>, fu: U32}
  CkE2{a1: U32, b1: U32, a2: U32, xi: U32, tye: U32, ctx: List<&2, U32>,
       fu: U32}
  CkE3{a1: U32, a2: U32, xi: U32, tye: U32, ctx: List<&2, U32>, fu: U32}
  CkE4{sub: L.Tri, a1: U32, a2: U32, xi: U32, tye: U32,
       ctx: List<&2, U32>, fu: U32}
  CkE5{sub: L.Tri, wd1: U32, a1: U32, a2: U32, xi: U32, tye: U32,
       ctx: List<&2, U32>, fu: U32}
  CkE6{sub: L.Tri, xi: U32, tye: U32, ctx: List<&2, U32>, fu: U32}
  CkE6Go{isyes: Bool, xi: U32, tye: U32, ctx: List<&2, U32>, fu: U32}
  CkE7{tye: U32, ctx: List<&2, U32>, fu: U32}
  CkE8{lt: U32, xi: U32, tye: U32, ctx: List<&2, U32>, fu: U32}
  CkE8b{nat: Bool, lt: U32, xi: U32, tye: U32, ctx: List<&2, U32>,
        fu: U32}
  CkE9{b1: Bool, b2: Bool, xi: U32, tye: U32, ctx: List<&2, U32>, fu: U32}
  CkI2{tye: U32, ctx: List<&2, U32>}
  CkI3{tye: U32, rty: U32, riok: Bool, ctx: List<&2, U32>}
  CkI4{w1: U32, samef: Bool, rty: U32, riok: Bool, ctx: List<&2, U32>}
  CkI5{rtybad: Bool, riok: Bool}
  # convert a final tri verdict to the machine's U32 result register
  DOut{}
  # dq_type_of: the type oracle (answers an index, 4294967295 = unknown)
  DTy1{ctx: List<&2, U32>}
  DTyGo{m1: Bool, m2: Bool, ti: U32, dlift: U32, ps: List<&2, U32>,
        qs: List<&2, L.LN>, sargs: List<&2, U32>}
  DTy2{sargs: List<&2, U32>}
  # the universe oracle (infer.bend's sl): "which Sort does this type
  # inhabit", pure reads, answers via MLn
  SLEv{e: U32, ctx: List<&2, U32>, fu: U32}
  SLIm{b: U32, t: U32, ctx: List<&2, U32>, fu: U32}
  SLIm2{dln: L.LN}
  SLBv{}
  SLCst{n: U32, us: List<&2, U32>}
  SLAp1{ctx: List<&2, U32>}
  SLAp2{nm: U32, us: List<&2, U32>}
  # fuel-exhausted oracle: answers unknown
  SLUn{}
  # compare the oracle's answer against an expected form (test harness)
  SLChk{want: L.LN}
  # memoised whnf (infer.bend's whd): check, reduce, store
  DWhd{i: U32, ctx: List<&2, U32>}
  # ---- lazy delta probe (YES only) ----
  # Lean's lazy_delta_reduction as a probe: whnf_core both sides; identical
  # -> YES; the same constant head (levels, arity) -> the arguments
  # pairwise; otherwise unfold the head of greater definition height one
  # step (both on a tie) and repeat. Every step is a sound reduction, so a
  # YES is final; anything else answers UNK and the caller falls back to
  # its full-whnf path. Fuel bounds the waste.
  LZ0{x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  # Lean's failure cache for lazy delta: a pair the probe could not settle
  # is recorded (hashed key, fingerprint value) and answers UNK at once the
  # next time. A collision can only cost a YES (an UNK), never invent one
  LZ0u{x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  LZ0g{hit: Bool, x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  # the decisive entry (is_def_eq_core's lazy_delta_reduction): no entry
  # failure cache, only the per-declaration budget
  LZ0d{x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  LZ0du{x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  LZC{key: U32, fp: U32, x: U32, y: U32, ctx: List<&2, U32>}
  LZC2{yes: Bool, key: U32, fp: U32, t: L.Tri, x: U32, y: U32, ctx: List<&2, U32>}
  LZ0b{stop: Bool, same: Bool, x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  LZ1{y: U32, fu: U32, ctx: List<&2, U32>}
  LZ2{x: U32, fu: U32, ctx: List<&2, U32>}
  LZ3{same: Bool, x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  LZ4{x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  # Lean's is_def_eq_offset at the top of every lazy-delta iteration:
  # `0 =?= Nat.zero` is YES, `succ a =?= succ b` (a literal n > 0 counts as
  # `succ (n-1)`) is decided by is_def_eq_core on the predecessors
  LZOx{x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  # dx: the digits of x when x is a literal (Nil otherwise): two literals
  # are decided by their digits (Lean's quick_is_def_eq on literals), never
  # peeled one successor at a time
  LZOy{x: U32, y: U32, lx: Bool, dx: List<&2, U32>, fu: U32,
       ctx: List<&2, U32>}
  LZOy2{x: U32, y: U32, px: U32, both: Bool, eqd: Bool, fu: U32,
        ctx: List<&2, U32>}
  LZOz{code: U32, x: U32, y: U32, px: U32, py: U32, fu: U32,
       ctx: List<&2, U32>}
  LZOr{}
  LZ5{x: U32, y: U32, hx: T.Ex, sx: List<&2, U32>, fu: U32, ctx: List<&2, U32>}
  LZ6{samehd: Bool, sx: List<&2, U32>, sy: List<&2, U32>, ux: Bool,
      uy: Bool, x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  LZA{xs: List<&2, U32>, ys: List<&2, U32>, ux: Bool, uy: Bool, x: U32,
      y: U32, fu: U32, ctx: List<&2, U32>}
  LZA2{yes: Bool, xs: List<&2, U32>, ys: List<&2, U32>, ux: Bool, uy: Bool,
       x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  LZA3{xs: List<&2, U32>, ys: List<&2, U32>, ux: Bool, uy: Bool, x: U32,
       y: U32, fu: U32, ctx: List<&2, U32>}
  # Lean's is_def_eq_args compares the arguments with the full defeq: an
  # argument pair the probe does not settle is whnf_core'd (no delta) and
  # compared by DSub; only a YES is used, failures are cached, and the
  # per-declaration probe budget bounds the recursion
  LZF{a: U32, b: U32, ctx: List<&2, U32>}
  LZF2u{a: U32, b: U32, ctx: List<&2, U32>}
  LZF2{yes: Bool, a: U32, b: U32, ctx: List<&2, U32>}
  LZF3{b: U32, ctx: List<&2, U32>}
  LZF4{wa: U32, ctx: List<&2, U32>}
  LZF5{a: U32, b: U32, ctx: List<&2, U32>}
  LZF6{seen: Bool, a: U32, b: U32, ctx: List<&2, U32>}
  LZU{ux: Bool, uy: Bool, x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  # neither head unfolds, but a side headed by a projection `s.i` still
  # reduces in Lean's whnf_core: its structure is whnf'd WITH delta
  # (reduce_proj) -- `(instHOrOfOrOp Nat Nat.instOrOp).1 a b`. Rebuild
  # `s'.i args` and probe again
  LZQ1{left: Bool, x: U32, y: U32, fu: U32, nxt: KF, ctx: List<&2, U32>}
  # Lean's reduce_nat at every lazy step, BEFORE unfolding: a side that is
  # a literal operation (Nat.add/sub/ble/mul/pow/div/mod/beq on two
  # arguments) is whnf'd -- the machine computes literal arithmetic -- so
  # `Nat.add 123456789 987654321` never unfolds into brecOn
  LZR0{go: Bool, opx: Bool, opy: Bool, ax1: U32, ax2: U32, ay1: U32,
       ay2: U32, nxt: KF, x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  # Lean guards that step with `!has_fvar(t_n) && !has_fvar(s_n)`: a
  # literal operation on an OPEN term is never whnf'd in the loop (the
  # full whnf of `BitVec.toNat (rotate x)` descended a 2^31 literal
  # one successor at a time)
  LZR0z{opx: Bool, opy: Bool, ax1: U32, ax2: U32, ay1: U32,
        ay2: U32, nxt: KF, x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  LZR0c{opx: Bool, opy: Bool, ax1: U32, ax2: U32, ay1: U32,
        ay2: U32, nxt: KF, x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  LZR0y{cl: Bool, opx: Bool, opy: Bool, ax1: U32, ax2: U32, ay1: U32,
        ay2: U32, nxt: KF, x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  LZPj{go: Bool, px: Bool, nxt: KF, x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  LZRg{opy: Bool, ay1: U32, ay2: U32, nxt: KF, x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  LZRg2{yes: Bool, opy: Bool, ay1: U32, ay2: U32, nxt: KF, x: U32, y: U32,
        fu: U32, ctx: List<&2, U32>}
  LZR1{opy: Bool, ay1: U32, ay2: U32, nxt: KF, x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  LZRh{wx: U32, nxt: KF, x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  LZRh2{yes: Bool, wx: U32, nxt: KF, x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  # both arguments of a literal operation whnf to literals?
  KLit2{a: U32, b: U32, ctx: List<&2, U32>}
  KLit2b{b: U32, ctx: List<&2, U32>}
  KLit2c{b: U32, ctx: List<&2, U32>}
  KLit2d{na: T.Ex, ctx: List<&2, U32>}
  KLit2e{na: T.Ex, ctx: List<&2, U32>}
  LZR2{wx: U32, nxt: KF, x: U32, y: U32, fu: U32, ctx: List<&2, U32>}
  LZR3{same: Bool, wx: U32, wy: U32, nxt: KF, fu: U32, ctx: List<&2, U32>}
  LZQ2{left: Bool, tn: U32, i: U32, s: U32, sargs: List<&2, U32>,
       other: U32, fu: U32, nxt: KF, ctx: List<&2, U32>}
  LZQ3{same: Bool, left: Bool, tn: U32, i: U32, s: U32,
       sargs: List<&2, U32>, other: U32, fu: U32, nxt: KF, ctx: List<&2, U32>}
  LZQ4{left: Bool, other: U32, fu: U32, ctx: List<&2, U32>}
  LZU2{uy: Bool, y: U32, fu: U32, ctx: List<&2, U32>}
  LZU3{x: U32, fu: U32, ctx: List<&2, U32>}
  LZUn{x: U32, ctx: List<&2, U32>}
  LZUn1{go: KF, ctx: List<&2, U32>}
  LZUn2{}
  # hooks: the caller's fallback continuations
  DAqLz{a1: U32, a2: U32, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DAqLz2{yes: Bool, a1: U32, a2: U32, xi: U32, yi: U32, ctx: List<&2, U32>,
         fu: U32}
  DCgLz{xt: List<&2, U32>, yt: List<&2, U32>, a1: U32, a2: U32, xi: U32,
        yi: U32, ctx: List<&2, U32>, fu: U32}
  DCgLz2{yes: Bool, xt: List<&2, U32>, yt: List<&2, U32>, a1: U32, a2: U32,
         xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  # rollback region around a whnf memo miss (see KRb's handler)
  # decisive lazy defeq: the lazy probe, then (unsettled) an eager
  # comparison of the probe's furthest-unfolded pair
  LD{x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  LDk{x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  LDk1{yes: Bool, nopair: Bool, x: U32, y: U32, ctx: List<&2, U32>,
       fu: U32}
  LDp{x: U32, y: U32, ctx: List<&2, U32>, fu: U32}
  LDw{y: U32, ctx: List<&2, U32>, fu: U32}
  LDw2{wx: U32, ctx: List<&2, U32>, fu: U32}
  KRb{mark: U32, snap: R.Tr<U32>}
  KRbN{mark: U32, snap: R.Tr<U32>}
  KRb3{comp: Bool, mark: U32}
  # a yes-only probe's answer without the pair it leaves (register 0)
  KZr{}
  KRb2{comp: Bool, mark: U32}
  DWhdGo{hit: Bool, h: U32, i: U32, ctx: List<&2, U32>}
  DWhdSt{i: U32, ctx: List<&2, U32>}
  DWhdM{i: U32, ctx: List<&2, U32>}
  DWhdF{i: U32, fu: U32, ctx: List<&2, U32>}
  DWhdFM{i: U32, fu: U32, ctx: List<&2, U32>}
  DWhdFG{hit: Bool, h: U32, i: U32, fu: U32, ctx: List<&2, U32>}
  WIhNext{ic: IC, ctx: List<&2, U32>}
  WIhPe{h: U32, ic: IC, ctx: List<&2, U32>}
  WIhFty{h: U32, ic: IC, ctx: List<&2, U32>}
  WIhScanned{h: U32, ic: IC, ctx: List<&2, U32>}
  WIhL{todo: List<&2, U32>, amt: U32, lacc: List<&2, U32>,
       ebni: List<&2, U32>, doms: List<&2, U32>, ic: IC, ctx: List<&2, U32>}
  WIhB{ic: IC, ctx: List<&2, U32>}

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
# (matches, not pick_kf: a strict pick built all five frames -- lists and
# all -- on every subterm a walk entered, and freed four)
def kev3(+op: U32, +c: U32, +d: U32, +v: U32, ps: List<&2, U32>,
         qs: List<&2, L.LN>, +fu: U32, +e: U32) -> KF:
  match op:
    case 0:
      KEvL{c, d, e, fu}
    case 1:
      KEvI{c, v, e, fu}
    case 3:
      KEvM{c, ps, e, fu}
    case _:
      KEvS{ps, qs, e, fu}

def kev2(+out: Bool, +op: U32, +c: U32, +d: U32, +v: U32,
         ps: List<&2, U32>, qs: List<&2, L.LN>, +fu: U32, +e: U32) -> KF:
  match out:
    case True{}:
      KKpF{e}
    case False{}:
      kev3(op, c, d, v, ps, qs, fu, e)

def kev(+wp: WP, +e: U32) -> KF:
  match wp:
    case WP{op, c, d, v, ps, qs, fu}:
      +f2 : U32 = fu
      kev2(U32.is_eq(f2, 0), op, c, d, v, ps, qs, f2, e)

# the whnf frame for e under args; fuel 0 rebuilds (the old `case 0n`)
# out of whnf fuel: rebuild and flag INCOMPLETE (a reject is no longer
# trustworthy). Without delta (only the lazy delta probe whnf's that way, and
# only its YES is used) the cut-short term is still a sound reduct: no flag.
def kwev2(+out: Bool, +delta: Bool, +e: U32, args: List<&2, U32>,
          +fu: U32, ctx: List<&2, U32>) -> KF:
  match out delta:
    case True{} True{}:
      WRb{e, args, ctx}
    case True{} False{}:
      WRbP{e, args, ctx}
    case False{} _:
      WEv{delta, e, args, fu, ctx}

def kwev(+delta: Bool, +e: U32, +args: List<&2, U32>, +fu: U32,
         ctx: List<&2, U32>) -> KF:
  +f2 : U32 = fu
  kwev2(U32.is_eq(f2, 0), delta, e, args, f2, ctx)

# level normal forms of use-site level arguments (infer.bend's lns_of)
def klns_of(us: List<&2, U32>, +lnt: R.Tr<L.LN>) -> List<&2, L.LN>:
  match us:
    case Nil{}:
      Nil{}
    case Con{head, tail}:
      Con{R.get(L.LN, 64n, lnt, head, L.LNun{}), klns_of(tail, lnt)}

# --- level interning ----------------------------------------------------
# Lean hash-conses levels; km names a level by an index into lnt. lsubst
# used to mint a fresh index for every level it produced, so two copies of
# the same body over the same levels were different nodes (the pointer
# table could not share them), and every index-keyed cache saw them as
# different terms. Each produced level now goes through a one-slot table in
# lnt itself, at key 2^31 + hash: the slot names an earlier index (encoded
# as LNimax{LNun, LNun, index}), reused when its level is the same normal
# form (ln_cmp YES), else a fresh index takes the slot.
def kat_hash(xs: List<&2, L.Atom>, +h: U32) -> U32:
  match xs:
    case Nil{}:
      h
    case Con{head, tail}:
      match head:
        case L.At{b, o}:
          kat_hash(tail, (((h * 31 : U32) + (b * 2654435761 : U32) : U32)
                          + (o * 40503 : U32) : U32))

def kln_hash(a: L.LN) -> U32:
  match a:
    case L.LNun{}:
      1
    case L.LNsym{}:
      2
    case L.LNmax{xs}:
      kat_hash(xs, 3)
    case L.LNimax{x, y, off}:
      ((((kln_hash(x) * 31 : U32) + kln_hash(y) : U32) * 31 : U32)
       + (off + 4 : U32) : U32)
    case L.LNmx{xs, y, r}:
      kat_hash(xs, ((kln_hash(y) * 31 : U32) + kln_hash(r) : U32))

def kpick_lt(+z: Bool, +x: R.Tr<L.LN>, +y: R.Tr<L.LN>) -> R.Tr<L.LN>:
  match z:
    case True{}:
      x
    case False{}:
      y

def klv_ptr(+a: L.LN) -> U32:
  match a:
    case L.LNimax{x, y, off}:
      match x y:
        case L.LNun{} L.LNun{}:
          off
        case _ _:
          4294967295
    case _:
      4294967295

def klv_key(+u: L.LN) -> U32:
  (2147483648 + U32.and(kln_hash(u), 2147483647) : U32)

# the index naming level u: an interned one, or nlx (then interned)
def klv_find(+lnt: R.Tr<L.LN>, +nlx: U32, +u: L.LN) -> U32:
  +t : R.Tr<L.LN> = lnt
  +u2 : L.LN = u
  +c : U32 = klv_ptr(R.get(L.LN, 64n, t, klv_key(u2), L.LNun{}))
  +hit : Bool = U32.is_lt(c, nlx)
                && L.tri_is_yes(L.ln_cmp(R.get(L.LN, 64n, t, c, L.LNun{}), u2))
  S.pick(hit, c, nlx)

# record u at index i when i is fresh (i == nlx): lnt and the slot
def klv_add(+lnt: R.Tr<L.LN>, +nlx: U32, +i: U32, +u: L.LN) -> R.Tr<L.LN>:
  +u2 : L.LN = u
  R.set_if(L.LN, U32.is_eq(i, nlx),
           R.set_if(L.LN, U32.is_eq(i, nlx), lnt, i, u2, L.LNun{}),
           klv_key(u2), L.LNimax{L.LNun{}, L.LNun{}, i}, L.LNun{})

def kpick_lta(+same: Bool, +lnt: R.Tr<L.LN>, +nl: U32, +i: U32,
              +u: L.LN) -> R.Tr<L.LN>:
  match same:
    case True{}:
      lnt
    case False{}:
      klv_add(lnt, nl, i, u)

# substitute every level in `us`, interning each normal form (head first)
def klsub_lvls(us: List<&2, U32>, +lnt: R.Tr<L.LN>, +nlx: U32,
               +ps: List<&2, U32>, +qs: List<&2, L.LN>) -> LVS:
  match us:
    case Nil{}:
      LVS{lnt, nlx, Nil{}}
    case Con{head, tail}:
      +t : R.Tr<L.LN> = lnt
      +u : L.LN = L.ln_subst(R.get(L.LN, 64n, t, head, L.LNun{}), ps, qs)
      +i : U32 = klv_find(t, nlx, u)
      +r : LVS = klsub_lvls(tail, klv_add(t, nlx, i, u),
                            S.pick(U32.is_eq(i, nlx), (nlx + 1 : U32), nlx),
                            ps, qs)
      LVS{lvs_t(r), lvs_nx(r), Con{i, lvs_xs(r)}}

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
      QR{L.ln_cmp(R.get(L.LN, 64n, lnt, a, L.LNun{}),
                  R.get(L.LN, 64n, lnt, b, L.LNun{})), Nil{}}
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
      +t2 : L.Tri = I.tri_and(acc, qr_t(r))
      # the first mismatch ends the walk (Lean's == stops there too)
      +w : List<&2, QI> = pick_qis(L.tri_is_yes(t2),
                                   List.append(&2, QI, qr_kids(r), tail),
                                   Nil{})
      keq_go(p, lnt, w, t2, nx, Array.get(T.Ex, a, keq_next(w)))

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
# --- hash-consing (proven in bench/hashcons.bend) -------------------------
# A region of the expression Array itself, [base, base+KMASK], is an open-
# addressing hash table of node pointers: slot = base + (fingerprint &
# KMASK), linear probe. A fixed-K scan (always iterates, no early return ->
# no mutual recursion) finds the first structural match and the first free
# slot; kalloc then shares, or appends at nx and records the pointer. Children are already
# hash-consed, so structural equality is tag + field-index equality (no
# recursion). This restores the export's DAG sharing through reduction, so
# the whnf memo hits and reduction stays linear.
# the pointer table's size: slots [base, base + ktbl), then the shared-
# argument record (base + ktbl), the epoch (base + ktbl + 1), and the
# allocation region from base + ktbl + 2. 2^22: a large declaration
# allocates past a million nodes, and a full table stops entering new ones
# (the store stops being canonical)
def ktbl() -> U32:
  4194304

def kmask() -> U32:
  4194303

def kmix(+h: U32, +x: U32) -> U32:
  (U32.xor(h, x) * 16777619 : U32)

def kmix_l(xs: List<&2, U32>, +h: U32) -> U32:
  match xs:
    case Nil{}:
      h
    case Con{head, tail}:
      kmix_l(tail, kmix(h, head))

def kfp(+x: T.Ex) -> U32:
  match x:
    case T.EBad{}:
      0
    case T.EBVar{i}:
      kmix(kmix(2166136261, 1), i)
    case T.ESort{l}:
      kmix(kmix(2166136261, 2), l)
    case T.EConst{n, us}:
      kmix_l(us, kmix(kmix(2166136261, 3), n))
    case T.EApp{f, a}:
      kmix(kmix(kmix(2166136261, 4), f), a)
    case T.ELam{n, t, b, bi}:
      kmix(kmix(kmix(2166136261, 5), t), b)
    case T.EAll{n, t, b, bi}:
      kmix(kmix(kmix(2166136261, 6), t), b)
    case T.ELet{n, t, v, b}:
      kmix(kmix(kmix(kmix(2166136261, 7), t), v), b)
    case T.EProj{tn, i, s}:
      kmix(kmix(kmix(kmix(2166136261, 8), tn), i), s)
    case T.ENat{d}:
      kmix_l(d, kmix(2166136261, 9))
    case T.EStr{d}:
      kmix_l(d, kmix(2166136261, 10))

def kueq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{a, as} Con{b, bs}:
      U32.is_eq(a, b) && kueq(as, bs)
    case _ _:
      False{}

def kexeq(+x: T.Ex, +y: T.Ex) -> Bool:
  match x y:
    case T.EBVar{i} T.EBVar{j}:
      U32.is_eq(i, j)
    case T.ESort{l} T.ESort{m}:
      U32.is_eq(l, m)
    case T.EConst{n, us} T.EConst{m, vs}:
      U32.is_eq(n, m) && kueq(us, vs)
    case T.EApp{f, a} T.EApp{g, b}:
      U32.is_eq(f, g) && U32.is_eq(a, b)
    case T.ELam{n, t, b, bi} T.ELam{m, u, c, b2}:
      U32.is_eq(t, u) && U32.is_eq(b, c)
    case T.EAll{n, t, b, bi} T.EAll{m, u, c, b2}:
      U32.is_eq(t, u) && U32.is_eq(b, c)
    case T.ELet{n, t, v, b} T.ELet{m, u, w, c}:
      U32.is_eq(t, u) && U32.is_eq(v, w) && U32.is_eq(b, c)
    case T.EProj{tn, i, s} T.EProj{t2, j, s2}:
      U32.is_eq(tn, t2) && U32.is_eq(i, j) && U32.is_eq(s, s2)
    case T.ENat{d} T.ENat{e}:
      kueq(d, e)
    case T.EStr{d} T.EStr{e}:
      kueq(d, e)
    case _ _:
      False{}

def kis_bad(+x: T.Ex) -> Bool:
  match x:
    case T.EBad{}:
      True{}
    case _:
      False{}

def knxt(+base: U32, +slot: U32) -> U32:
  (base + U32.and((slot + 1 - base : U32), kmask()) : U32)

def kpu(+z: Bool, +x: U32, +y: U32) -> U32:
  match z:
    case True{}:
      x
    case False{}:
      y

# The table holds POINTERS: a slot is EBad (never used), or EApp{j, h} for
# the node at index j with fingerprint h. Nodes themselves are always
# appended at nx, so rolling nx back (KRb) frees them all at once; a pointer
# at or above nx is then a tombstone: probing passes over it (a live entry
# may lie beyond) and an insertion may reuse it. The node behind a pointer
# is read only when the fingerprints agree.
def kpn2(pr: Array<T.Ex> & T.Ex, +ent: T.Ex,
         +node: T.Ex) -> Array<T.Ex> & (T.Ex & Bool):
  match pr:
    case Tuple{a, cand}:
      (a, (ent, kexeq(cand, node)))

# A table entry is EProj{epoch, index, fingerprint}. The epoch (slot
# base + 2^20 + 1, bumped per declaration by kbump) retires every pointer an
# earlier declaration left: allocation restarts per declaration, so such a
# pointer would otherwise come back to life once allocation passed it --
# never matching (the slot holds another node), never free, and the 24-probe
# clusters filled until new nodes could not be entered at all (two copies of
# one term, which every index-keyed cache then told apart). An entry of
# another epoch reads as a tombstone (EBVar{0}: not EBad, pointer unknown).
def kep_of(+e: T.Ex) -> U32:
  match e:
    case T.EBVar{i}:
      i
    case _:
      0

def kep_slot(+base: U32) -> U32:
  (base + ktbl() + 1 : U32)

def kep2(pr: Array<T.Ex> & T.Ex) -> Array<T.Ex> & U32:
  match pr:
    case Tuple{a, e}:
      (a, kep_of(e))

def kpn3(+cmp: Bool, +live: Bool, a: Array<T.Ex>, +j: U32, +h: U32,
         +node: T.Ex) -> Array<T.Ex> & (T.Ex & Bool):
  match cmp:
    case True{}:
      kpn2(Array.get(T.Ex, a, j), T.EApp{j, h}, node)
    case False{}:
      match live:
        case True{}:
          (a, (T.EApp{j, h}, False{}))
        case False{}:
          (a, (T.EBVar{0}, False{}))

def kpn1(pr: Array<T.Ex> & T.Ex, +nx: U32, +fp: U32, +ep: U32, +look: Bool,
         +node: T.Ex) -> Array<T.Ex> & (T.Ex & Bool):
  match pr:
    case Tuple{a, T.EProj{e0, j, h}}:
      +j2 : U32 = j
      +h2 : U32 = h
      +live : Bool = U32.is_eq(e0, ep)
      kpn3(look && live && U32.is_lt(j2, nx) && U32.is_eq(h2, fp), live, a,
           j2, h2, node)
    case Tuple{a, ent}:
      (a, (ent, False{}))

def kps2(pr: Array<T.Ex> & U32, +s: U32, +nx: U32, +fp: U32, +look: Bool,
         +node: T.Ex) -> Array<T.Ex> & (T.Ex & Bool):
  match pr:
    case Tuple{a, ep}:
      kpn1(Array.get(T.Ex, a, s), nx, fp, ep, look, node)

def kprobe_slot(a: Array<T.Ex>, +s: U32, +nx: U32, +fp: U32, +look: Bool,
                +node: T.Ex, +base: U32) -> Array<T.Ex> & (T.Ex & Bool):
  kps2(kep2(Array.get(T.Ex, a, kep_slot(base))), s, nx, fp, look, node)

def kptr_of(+x: T.Ex) -> U32:
  match x:
    case T.EApp{j, h}:
      j
    case _:
      4294967295

# fixed-K scan: the first hit (a node index) and the first free slot
# (never used, or a tombstone); stops at a never-used slot
def kscan(k: Nat, +done: Bool, +base: U32, +node: T.Ex, +slot: U32,
          +found: U32, +fempty: U32, +stopped: Bool, +nx: U32, +fp: U32,
          pr: Array<T.Ex> & (T.Ex & Bool)) -> Array<T.Ex> & (U32 & U32):
  match k done pr:
    case 0n _ Tuple{ex, cand}:
      (ex, (found, fempty))
    # a hit, or a never-used slot (nothing lies beyond it): stop probing
    case 1n+p True{} Tuple{ex, cand}:
      (ex, (found, fempty))
    case 1n+p False{} Tuple{ex, Tuple{ent, hit0}}:
      +e2 : T.Ex = ent
      +eb : Bool = kis_bad(e2)
      +pj : U32 = kptr_of(e2)
      +tomb : Bool = Bool.not(eb) && U32.is_ge(pj, nx)
      +hit : Bool = Bool.not(stopped) && hit0
                    && U32.is_eq(found, 4294967295)
      +f2 : U32 = kpu(hit, pj, found)
      +fe2 : U32 = kpu((eb || tomb) && Bool.not(stopped)
                       && U32.is_eq(fempty, 4294967295), slot, fempty)
      +slot2 : U32 = knxt(base, slot)
      +st2 : Bool = Bool.or(stopped, eb)
      +f3 : U32 = f2
      +dn : Bool = st2 || U32.is_ne(f3, 4294967295)
      kscan(p, dn, base, node, slot2, f3, fe2, st2, nx, fp,
            kprobe_slot(ex, slot2, nx, fp, Bool.not(dn), node, base))

# --- loose-bvar ranges in the store --------------------------------------
# Every node written to slot i also records lbr(node) -- one more than its
# largest loose bound variable -- at slot i + hb as T.EBVar{lbr} (hb = half
# the store array, a function of the hash-cons base; allocation stays below
# hb, see fcheck's overflow guard). An unwritten lbr slot reads as
# unknown (4294967295), which propagates through max. lift and instantiate
# keep a subterm whose lbr is at most their cutoff without walking it --
# Lean's has_loose_bvars test; without it a shared subterm (a DAG) is
# walked as a tree (perf/shared-subterm: 2^1000).
# log2 of hb, the usable store capacity: room for the export, the hash-cons
# table and 2^20 more, rounded up twice. The store array is 2*hb (see
# khalf). A floor of 2^25 was tried: every run then pays ~4 GB (a slot costs
# ~64 bytes, all initialised) and perf/magma-list-pair-n7 still overflows --
# the store never frees a slot, which is the real limit there.
def sdepth(+base: U32) -> Nat:
  Nat.add(U32.log2(((base + ktbl() : U32) + 2097152 : U32)), 2n)

def khalf(+base: U32) -> U32:
  U32.shln(1, sdepth(base))


# --- per-declaration flags in the store --------------------------------
# Kept out of the memo trie: a trie set copies a path (and a rollback
# region's snapshot keeps the old one alive until it is freed), and these
# are written constantly and must survive rollbacks anyway. They live in
# the hash table's unused loose-bvar shadow, slot base + hb + k, as
# EBVar{v} (an unwritten slot reads 0); kbump clears them per declaration.
#   0 lazy-probe budget used, 1 OVF, 2 CORRUPT, 3 INCOMPLETE, 4 infer_only
def kfl_slot(+base: U32, +k: U32) -> U32:
  ((base + khalf(base) : U32) + k : U32)

def kfl_v(+e: T.Ex) -> U32:
  match e:
    case T.EBVar{i}:
      i
    case _:
      0

def kfl_tin2(pr: Array<T.Ex> & T.Ex, +nx: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match pr:
    case Tuple{a, e}:
      (((a, nx), MN{}), kfl_v(e))

# flag k as the register
def kfl_tin(fs: Array<T.Ex> & U32, +base: U32,
            +k: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fs:
    case Tuple{ex, nx}:
      kfl_tin2(Array.get(T.Ex, ex, kfl_slot(base, k)), nx)

def kfl_set(fs: Array<T.Ex> & U32, +base: U32, +k: U32,
            +v: U32) -> Array<T.Ex> & U32:
  match fs:
    case Tuple{ex, nx}:
      (Array.set(T.Ex, ex, kfl_slot(base, k), T.EBVar{v}), nx)

def kfl_set_if(+go: Bool, fs: Array<T.Ex> & U32, +base: U32, +k: U32,
               +v: U32) -> Array<T.Ex> & U32:
  match go:
    case True{}:
      kfl_set(fs, base, k, v)
    case False{}:
      fs

# an overflow inside a region: OVF and CORRUPT
def kfl_ovf(+ovf: Bool, a: Array<T.Ex>, +base: U32) -> Array<T.Ex>:
  match ovf:
    case True{}:
      Array.set(T.Ex, Array.set(T.Ex, a, kfl_slot(base, 1), T.EBVar{1}),
                kfl_slot(base, 2), T.EBVar{1})
    case False{}:
      a

# OVF | CORRUPT << 1 | INCOMPLETE << 2, for the verdict
def kfl_fl3(pr: Array<T.Ex> & T.Ex, +acc: U32) -> Array<T.Ex> & U32:
  match pr:
    case Tuple{a, e}:
      (a, (acc + S.pick(U32.is_eq(kfl_v(e), 0), 0, 4) : U32))

def kfl_fl2(pr: Array<T.Ex> & T.Ex, +base: U32, +acc: U32) -> Array<T.Ex> & U32:
  match pr:
    case Tuple{a, e}:
      kfl_fl3(Array.get(T.Ex, a, kfl_slot(base, 3)),
              (acc + S.pick(U32.is_eq(kfl_v(e), 0), 0, 2) : U32))

def kfl_fl1(pr: Array<T.Ex> & T.Ex, +base: U32) -> Array<T.Ex> & U32:
  match pr:
    case Tuple{a, e}:
      kfl_fl2(Array.get(T.Ex, a, kfl_slot(base, 2)), base,
              S.pick(U32.is_eq(kfl_v(e), 0), 0, 1))

def kfl_flags(a: Array<T.Ex>, +base: U32) -> Array<T.Ex> & U32:
  kfl_fl1(Array.get(T.Ex, a, kfl_slot(base, 1)), base)

def kfl_clear(a: Array<T.Ex>, +base: U32) -> Array<T.Ex>:
  Array.set(T.Ex, Array.set(T.Ex, Array.set(T.Ex, Array.set(T.Ex,
    Array.set(T.Ex, a, kfl_slot(base, 0), T.EBVar{0}),
    kfl_slot(base, 1), T.EBVar{0}), kfl_slot(base, 2), T.EBVar{0}),
    kfl_slot(base, 3), T.EBVar{0}), kfl_slot(base, 4), T.EBVar{0})

# A node's shadow slot (i + hb): EApp{lbr, stamp}, or ELet{lbr, stamp, w,
# gc} once its whnf w is memoised at generation gc. The stamp is the
# rollback generation G (kg_slot) when the node was written; G grows at
# every rollback, compaction and declaration, and kgd_slot keeps G as the
# declaration began. A memo is valid while w's stamp is at most gc (w
# was not freed and rewritten since) and gc is of this declaration (later
# declarations can make km's whnf stronger) -- sound without the memo
# trie's snapshots.
def klb_unpack(pr: Array<T.Ex> & T.Ex) -> Array<T.Ex> & U32:
  match pr:
    case Tuple{a, T.EApp{l, st}}:
      (a, l)
    case Tuple{a, T.ELet{l, st, r, rs}}:
      (a, l)
    case Tuple{a, T.EBVar{l}}:
      (a, l)
    case Tuple{a, x}:
      (a, 4294967295)

def klb_l(+e: T.Ex) -> U32:
  match e:
    case T.EApp{l, st}:
      l
    case T.ELet{l, st, r, rs}:
      l
    case T.EBVar{l}:
      l
    case _:
      4294967295

def kst(+e: T.Ex) -> U32:
  match e:
    case T.EApp{l, st}:
      st
    case T.ELet{l, st, r, rs}:
      st
    case _:
      4294967294

# G and the declaration's start sit in node slots hb - 1 and hb - 2, which
# allocation never reaches (kput stops at hb - 2); NOT at the array's end,
# where the sentinels 4294967295 / 4294967294 wrap and must read EBad
def kg_slot(+hb: U32) -> U32:
  (hb - 1 : U32)

def kgd_slot(+hb: U32) -> U32:
  (hb - 2 : U32)

def kg_v(+e: T.Ex) -> U32:
  match e:
    case T.EBVar{v}:
      v
    case _:
      0

def kg_bump2(pr: Array<T.Ex> & T.Ex, +hb: U32) -> Array<T.Ex>:
  match pr:
    case Tuple{a, e}:
      Array.set(T.Ex, a, kg_slot(hb), T.EBVar{(kg_v(e) + 1 : U32)})

def kg_bump(+go: Bool, a: Array<T.Ex>, +hb: U32) -> Array<T.Ex>:
  match go:
    case True{}:
      kg_bump2(Array.get(T.Ex, a, kg_slot(hb)), hb)
    case False{}:
      a

# a new declaration: G + 1, recorded as the declaration's start
def kg_decl2(pr: Array<T.Ex> & T.Ex, +hb: U32) -> Array<T.Ex>:
  match pr:
    case Tuple{a, e}:
      +g : U32 = (kg_v(e) + 1 : U32)
      Array.set(T.Ex, Array.set(T.Ex, a, kg_slot(hb), T.EBVar{g}),
                kgd_slot(hb), T.EBVar{g})

def kg_decl(a: Array<T.Ex>, +hb: U32) -> Array<T.Ex>:
  kg_decl2(Array.get(T.Ex, a, kg_slot(hb)), hb)

# --- the success cache, in the store ------------------------------------
# Lean caches every is_def_eq success. km's memo trie is restored at the
# end of every rollback region, so a YES proved inside one (a proof's type
# compared for proof irrelevance, a whnf's inner work) was proved again at
# the next occurrence: `Exists =?= Exists` 1,124 times in one iterator
# lemma, 348k DSub calls for 84k distinct pairs. The cache lives in the
# hash table's unused loose-bvar shadow (never rolled back): 2^17 two-slot
# entries at kfl_slot(base, 1024 + 2*(hash & mask)) -- EProj{x, y, ctxhash}
# and EBVar{gc}, gc the rollback generation G at the write. Valid like a
# whnf memo: gc is of this declaration (G at its start, kgd_slot) and
# neither node's stamp exceeds gc (neither was freed and rewritten since).
# The context hash covers the binders' types, which a YES between open
# terms may rest on (proof irrelevance, unit eta).
def kyc_key(+x: U32, +y: U32, +ch: U32) -> U32:
  (1024 + (2 * U32.and((((x * 2654435761 : U32) + (y * 40503 : U32) : U32)
                        + (ch * 97 : U32) : U32), 131071) : U32) : U32)

# a node's stamp: export nodes (EBVar{lbr} shadows) are never freed
def kyst(+e: T.Ex) -> U32:
  match e:
    case T.EApp{l, st}:
      st
    case T.ELet{l, st, r, rs}:
      st
    case T.EBVar{l}:
      0
    case _:
      4294967294

def kyc_h5(pr: Array<T.Ex> & T.Ex, +gc: U32, +okx: Bool) -> Array<T.Ex> & Bool:
  match pr:
    case Tuple{a, e}:
      (a, okx && U32.is_le(kyst(e), gc))

def kyc_h4(pr: Array<T.Ex> & T.Ex, +hb: U32, +y: U32,
           +gc: U32) -> Array<T.Ex> & Bool:
  match pr:
    case Tuple{a, e}:
      kyc_h5(Array.get(T.Ex, a, (y + hb : U32)), gc, U32.is_le(kyst(e), gc))

def kyc_h3b(+ok: Bool, a: Array<T.Ex>, +hb: U32, +x: U32, +y: U32,
            +gc: U32) -> Array<T.Ex> & Bool:
  match ok:
    case True{}:
      kyc_h4(Array.get(T.Ex, a, (x + hb : U32)), hb, y, gc)
    case False{}:
      (a, False{})

def kyc_h3(pr: Array<T.Ex> & T.Ex, +hb: U32, +x: U32, +y: U32,
           +gc: U32) -> Array<T.Ex> & Bool:
  match pr:
    case Tuple{a, gde}:
      kyc_h3b(U32.is_ge(gc, kg_v(gde)), a, hb, x, y, gc)

def kyc_h2(pr: Array<T.Ex> & T.Ex, +hb: U32, +x: U32,
           +y: U32) -> Array<T.Ex> & Bool:
  match pr:
    case Tuple{a, e}:
      kyc_h3(Array.get(T.Ex, a, kgd_slot(hb)), hb, x, y, kfl_v(e))

def kyc_h1b(+ok: Bool, a: Array<T.Ex>, +base: U32, +k: U32, +x: U32,
            +y: U32) -> Array<T.Ex> & Bool:
  match ok:
    case True{}:
      kyc_h2(Array.get(T.Ex, a, kfl_slot(base, (k + 1 : U32))), khalf(base),
             x, y)
    case False{}:
      (a, False{})

def kyc_h1(pr: Array<T.Ex> & T.Ex, +base: U32, +k: U32, +x: U32, +y: U32,
           +ch: U32) -> Array<T.Ex> & Bool:
  match pr:
    case Tuple{a, e}:
      match e:
        case T.EProj{tn, idx, sx}:
          kyc_h1b(U32.is_eq(tn, x) && U32.is_eq(idx, y) && U32.is_eq(sx, ch),
                  a, base, k, x, y)
        case _:
          (a, False{})

def kyc_hit(a: Array<T.Ex>, +base: U32, +x: U32, +y: U32,
            +ch: U32) -> Array<T.Ex> & Bool:
  +k : U32 = kyc_key(x, y, ch)
  kyc_h1(Array.get(T.Ex, a, kfl_slot(base, k)), base, k, x, y, ch)

# the lookup as the register: 1 hit, 0 miss
def kyc_tin2(pr: Array<T.Ex> & Bool, +nx: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match pr:
    case Tuple{a, h}:
      (((a, nx), MN{}), S.pick(h, 1, 0))

def kyc_tin(fs: Array<T.Ex> & U32, +base: U32, +x: U32, +y: U32,
            +ch: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fs:
    case Tuple{ex, nx}:
      kyc_tin2(kyc_hit(ex, base, x, y, ch), nx)

def kyc_s1(pr: Array<T.Ex> & T.Ex, +base: U32, +k: U32, +x: U32, +y: U32,
           +ch: U32) -> Array<T.Ex>:
  match pr:
    case Tuple{a, g}:
      Array.set(T.Ex, Array.set(T.Ex, a, kfl_slot(base, k), T.EProj{x, y, ch}),
                kfl_slot(base, (k + 1 : U32)), T.EBVar{kg_v(g)})

def kyc_set(+go: Bool, a: Array<T.Ex>, +base: U32, +x: U32, +y: U32,
            +ch: U32) -> Array<T.Ex>:
  match go:
    case True{}:
      kyc_s1(Array.get(T.Ex, a, kg_slot(khalf(base))), base, kyc_key(x, y, ch),
             x, y, ch)
    case False{}:
      a

# --- the inference memo, in the store ------------------------------------
# The same scheme for infer(x) under a context: the hash-consed pair node
# pk = EApp{x, cid} names (x, context) exactly; 2^17 two-slot entries at
# kfl_slot(base, 263168 + 2*(hash & mask)): EProj{pk, infer_only, value}
# and EBVar{gc}; valid while gc is of this declaration and neither pk nor
# the type node (value & 0x7FFFFFFF, unless the ill-typed marker) was
# freed and rewritten since. Lean's infer cache is never discarded; km's
# memo trie is restored at every region's end, which re-inferred the same
# terms 4-7x (INF calls vs distinct) in the omega proofs.
def kyi_key(+pk: U32, +io: U32) -> U32:
  (263168 + (2 * U32.and(((pk * 2654435761 : U32) + (io * 40503 : U32) : U32),
                         131071) : U32) : U32)

def kyi_h5(pr: Array<T.Ex> & T.Ex, +gc: U32, +okp: Bool,
           +v: U32) -> Array<T.Ex> & U32:
  match pr:
    case Tuple{a, e}:
      (a, S.pick(okp && U32.is_le(kyst(e), gc), v, 4294967295))

# the type node must also lie below the allocation pointer: a freed node
# keeps its old stamp until its slot is rewritten (the whnf memo's rule)
def kyi_h4(pr: Array<T.Ex> & T.Ex, +hb: U32, +nx: U32, +v: U32,
           +gc: U32) -> Array<T.Ex> & U32:
  match pr:
    case Tuple{a, e}:
      +v2 : U32 = U32.and(v, 2147483647)
      +isnode : Bool = U32.is_lt(v2, (hb - 2 : U32))
      kyi_h5(Array.get(T.Ex, a, (S.pick(isnode, v2, 0) + hb : U32)), gc,
             U32.is_le(kyst(e), gc)
             && (Bool.not(isnode) || U32.is_lt(v2, nx)), v)

def kyi_h3b(+ok: Bool, a: Array<T.Ex>, +hb: U32, +nx: U32, +pk: U32,
            +v: U32, +gc: U32) -> Array<T.Ex> & U32:
  match ok:
    case True{}:
      kyi_h4(Array.get(T.Ex, a, (pk + hb : U32)), hb, nx, v, gc)
    case False{}:
      (a, 4294967295)

def kyi_h3(pr: Array<T.Ex> & T.Ex, +hb: U32, +nx: U32, +pk: U32, +v: U32,
           +gc: U32) -> Array<T.Ex> & U32:
  match pr:
    case Tuple{a, gde}:
      kyi_h3b(U32.is_ge(gc, kg_v(gde)), a, hb, nx, pk, v, gc)

def kyi_h2(pr: Array<T.Ex> & T.Ex, +hb: U32, +nx: U32, +pk: U32,
           +v: U32) -> Array<T.Ex> & U32:
  match pr:
    case Tuple{a, e}:
      kyi_h3(Array.get(T.Ex, a, kgd_slot(hb)), hb, nx, pk, v, kfl_v(e))

def kyi_h1b(+ok: Bool, a: Array<T.Ex>, +base: U32, +nx: U32, +k: U32,
            +pk: U32, +v: U32) -> Array<T.Ex> & U32:
  match ok:
    case True{}:
      kyi_h2(Array.get(T.Ex, a, kfl_slot(base, (k + 1 : U32))), khalf(base),
             nx, pk, v)
    case False{}:
      (a, 4294967295)

def kyi_h1(pr: Array<T.Ex> & T.Ex, +base: U32, +nx: U32, +k: U32, +pk: U32,
           +io: U32) -> Array<T.Ex> & U32:
  match pr:
    case Tuple{a, e}:
      match e:
        case T.EProj{tn, idx, sx}:
          kyi_h1b(U32.is_eq(tn, pk) && U32.is_eq(idx, io), a, base, nx, k, pk,
                  sx)
        case _:
          (a, 4294967295)

# the memoised value for (pk, io) as the register, or 4294967295
def kyi_tin2(pr: Array<T.Ex> & U32, +nx: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match pr:
    case Tuple{a, v}:
      (((a, nx), MN{}), v)

def kyi_tin(fs: Array<T.Ex> & U32, +base: U32, +pk: U32,
            +io: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fs:
    case Tuple{ex, nx}:
      +k : U32 = kyi_key(pk, io)
      +n2 : U32 = nx
      kyi_tin2(kyi_h1(Array.get(T.Ex, ex, kfl_slot(base, k)), base, n2, k, pk,
                      io),
               n2)

def kyi_s1(pr: Array<T.Ex> & T.Ex, +base: U32, +k: U32, +pk: U32, +io: U32,
           +v: U32) -> Array<T.Ex>:
  match pr:
    case Tuple{a, g}:
      Array.set(T.Ex, Array.set(T.Ex, a, kfl_slot(base, k), T.EProj{pk, io, v}),
                kfl_slot(base, (k + 1 : U32)), T.EBVar{kg_v(g)})

def kyi_set(+go: Bool, a: Array<T.Ex>, +base: U32, +pk: U32, +io: U32,
            +v: U32) -> Array<T.Ex>:
  match go:
    case True{}:
      kyi_s1(Array.get(T.Ex, a, kg_slot(khalf(base))), base, kyi_key(pk, io),
             pk, io, v)
    case False{}:
      a

def klb_get(a: Array<T.Ex>, +j: U32, +hb: U32) -> Array<T.Ex> & U32:
  klb_unpack(Array.get(T.Ex, a, (j + hb : U32)))

# a node's lbr as the register (0: closed)
def klb_tin(r: Array<T.Ex> & U32, +nx: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match r:
    case Tuple{a, l}:
      (((a, nx), MN{}), l)

# under one binder: bvar 0 is bound, the rest shift down; unknown stays
def klb_dec(+l: U32) -> U32:
  S.pick(U32.is_eq(l, 0), 0,
         S.pick(U32.is_eq(l, 4294967295), 4294967295, (l - 1 : U32)))

def kput_fin2(pr: Array<T.Ex> & T.Ex, +j: U32, +l: U32) -> Array<T.Ex>:
  match pr:
    case Tuple{a, g}:
      Array.set(T.Ex, a, j, T.EApp{l, kg_v(g)})

def kput_fin(a: Array<T.Ex>, +j: U32, +l: U32, +hb: U32) -> Array<T.Ex>:
  kput_fin2(Array.get(T.Ex, a, kg_slot(hb)), j, l)

def kput_ap2(pr: Array<T.Ex> & U32, +lf: U32, +hb: U32, +i: U32,
             +node: T.Ex) -> Array<T.Ex>:
  match pr:
    case Tuple{a, lg}:
      kput_fin(Array.set(T.Ex, a, i, node), (i + hb : U32), U32.max(lf, lg), hb)

def kput_ap(pr: Array<T.Ex> & U32, +g: U32, +hb: U32, +i: U32,
            +node: T.Ex) -> Array<T.Ex>:
  match pr:
    case Tuple{a, lf}:
      kput_ap2(klb_get(a, g, hb), lf, hb, i, node)

def kput_bd2(pr: Array<T.Ex> & U32, +lt: U32, +hb: U32, +i: U32,
             +node: T.Ex) -> Array<T.Ex>:
  match pr:
    case Tuple{a, lb}:
      kput_fin(Array.set(T.Ex, a, i, node), (i + hb : U32),
               U32.max(lt, klb_dec(lb)), hb)

def kput_bd(pr: Array<T.Ex> & U32, +b: U32, +hb: U32, +i: U32,
            +node: T.Ex) -> Array<T.Ex>:
  match pr:
    case Tuple{a, lt}:
      kput_bd2(klb_get(a, b, hb), lt, hb, i, node)

def kput_lt3(pr: Array<T.Ex> & U32, +m: U32, +hb: U32, +i: U32,
             +node: T.Ex) -> Array<T.Ex>:
  match pr:
    case Tuple{a, lb}:
      kput_fin(Array.set(T.Ex, a, i, node), (i + hb : U32),
               U32.max(m, klb_dec(lb)), hb)

def kput_lt2(pr: Array<T.Ex> & U32, +lt: U32, +b: U32, +hb: U32,
             +i: U32, +node: T.Ex) -> Array<T.Ex>:
  match pr:
    case Tuple{a, lv}:
      kput_lt3(klb_get(a, b, hb), U32.max(lt, lv), hb, i, node)

def kput_lt(pr: Array<T.Ex> & U32, +v: U32, +b: U32, +hb: U32, +i: U32,
            +node: T.Ex) -> Array<T.Ex>:
  match pr:
    case Tuple{a, lt}:
      kput_lt2(klb_get(a, v, hb), lt, b, hb, i, node)

def kput_pj(pr: Array<T.Ex> & U32, +hb: U32, +i: U32,
            +node: T.Ex) -> Array<T.Ex>:
  match pr:
    case Tuple{a, ls}:
      kput_fin(Array.set(T.Ex, a, i, node), (i + hb : U32), ls, hb)

# write node at i and its lbr at i + hb
# A write past the usable capacity is DROPPED: index i + hb (its lbr slot)
# would wrap around the 2*hb array onto the export's own nodes, corrupting
# every later declaration. Allocation past capacity is still caught (nx >= cap
# at the declaration's end, or at a KRb rollback), and declines that one
# declaration; its reads of dropped slots only feed its own declined verdict.
def kput_g(+ok: Bool, +hb: U32, a: Array<T.Ex>, +i: U32,
           +node: T.Ex) -> Array<T.Ex>:
  match ok node:
    case False{} _:
      a
    case True{} T.EBVar{j}:
      kput_fin(Array.set(T.Ex, a, i, T.EBVar{j}), (i + hb : U32),
               (j + 1 : U32), hb)
    case True{} T.EApp{f, g}:
      kput_ap(klb_get(a, f, hb), g, hb, i, T.EApp{f, g})
    case True{} T.ELam{n, t, b, bi}:
      kput_bd(klb_get(a, t, hb), b, hb, i, T.ELam{n, t, b, bi})
    case True{} T.EAll{n, t, b, bi}:
      kput_bd(klb_get(a, t, hb), b, hb, i, T.EAll{n, t, b, bi})
    case True{} T.ELet{n, t, v, b}:
      kput_lt(klb_get(a, t, hb), v, b, hb, i, T.ELet{n, t, v, b})
    case True{} T.EProj{tn, j, sx}:
      kput_pj(klb_get(a, sx, hb), hb, i, T.EProj{tn, j, sx})
    case True{} T.EBad{}:
      kput_fin(Array.set(T.Ex, a, i, T.EBad{}), (i + hb : U32), 4294967295, hb)
    case True{} x:
      kput_fin(Array.set(T.Ex, a, i, x), (i + hb : U32), 0, hb)

def kput(+hb: U32, a: Array<T.Ex>, +i: U32, +node: T.Ex) -> Array<T.Ex>:
  kput_g(U32.is_lt(i, (hb - 2 : U32)), hb, a, i, node)

# --- the whnf memo in the shadow slots ----------------------------------
def kwm4(pr: Array<T.Ex> & T.Ex, +nx: U32, +ok: Bool, +r: U32, +gc: U32,
         +gd: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match pr:
    case Tuple{a, e}:
      (((a, nx), MN{}),
       S.pick(ok && U32.is_le(kst(e), gc) && U32.is_ge(gc, gd), r,
              4294967295))

def kwm3(pr: Array<T.Ex> & T.Ex, +nx: U32, +ok: Bool, +r: U32, +gc: U32,
         +hb: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match pr:
    case Tuple{a, gde}:
      kwm4(Array.get(T.Ex, a, (S.pick(ok, r, 0) + hb : U32)), nx, ok, r, gc,
           kg_v(gde))

def kwm2(pr: Array<T.Ex> & T.Ex, +nx: U32,
         +hb: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match pr:
    case Tuple{a, T.ELet{l, st, r, gc}}:
      +r2 : U32 = r
      # below the allocation pointer: a rollback frees a result before its
      # slot is reused (and restamped), and a freed index is reallocated
      +ok : Bool = U32.is_lt(r2, (hb - 2 : U32)) && U32.is_lt(r2, nx)
      kwm3(Array.get(T.Ex, a, kgd_slot(hb)), nx, ok, r2, gc, hb)
    case Tuple{a, e}:
      (((a, nx), MN{}), 4294967295)

# the memoised whnf of node i, or none, as the register
def kwm_tin(fs: Array<T.Ex> & U32, +i: U32,
            +hb: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fs:
    case Tuple{ex, nx}:
      kwm2(Array.get(T.Ex, ex, (S.pick(U32.is_lt(i, (hb - 2 : U32)), i, 0)
                                + hb : U32)), nx, hb)

def kws3(pr: Array<T.Ex> & T.Ex, +i: U32, +r: U32, +l: U32, +st: U32,
         +hb: U32) -> Array<T.Ex>:
  match pr:
    case Tuple{a, g}:
      Array.set(T.Ex, a, (i + hb : U32), T.ELet{l, st, r, kg_v(g)})

def kws2(pr: Array<T.Ex> & T.Ex, +i: U32, +r: U32,
         +hb: U32) -> Array<T.Ex>:
  match pr:
    case Tuple{a, e}:
      +e2 : T.Ex = e
      kws3(Array.get(T.Ex, a, kg_slot(hb)), i, r, klb_l(e2), kst(e2), hb)

def kws_go(+go: Bool, a: Array<T.Ex>, +i: U32, +r: U32,
           +hb: U32) -> Array<T.Ex>:
  match go:
    case True{}:
      kws2(Array.get(T.Ex, a, (i + hb : U32)), i, r, hb)
    case False{}:
      a

# memoise whnf(i) = r (both allocated nodes), at the current generation
def kwm_set(fs: Array<T.Ex> & U32, +i: U32, +r: U32,
            +hb: U32) -> Array<T.Ex> & U32:
  match fs:
    case Tuple{ex, nx}:
      (kws_go(U32.is_lt(i, (hb - 2 : U32)) && U32.is_lt(r, (hb - 2 : U32)),
              ex, i, r, hb), nx)

# fetch a subterm a lift/instantiate walk is about to enter -- or, when its
# recorded lbr is at most the walk's cutoff, answer MKeep (keep it as is).
# lsubst (op 2) does not depend on bound variables and always fetches.
def kfc3(+skip: Bool, a: Array<T.Ex>, +x: U32, +nx: U32,
         +ri: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match skip:
    case True{}:
      (((a, nx), MKeep{}), ri)
    case False{}:
      kfetch2(Array.get(T.Ex, a, x), nx, ri)

def kfc2(pr: Array<T.Ex> & U32, +x: U32, +nx: U32, +ri: U32,
         +c: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match pr:
    case Tuple{a, l}:
      kfc3(U32.is_le(l, c), a, x, nx, ri)

def kfc1(+lb: Bool, fs: Array<T.Ex> & U32, +x: U32, +ri: U32, +c: U32,
         +base: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match lb fs:
    case True{} Tuple{ex, nx}:
      +x2 : U32 = x
      kfc2(klb_get(ex, x2, khalf(base)), x2, nx, ri, c)
    case False{} Tuple{ex, nx}:
      kfetch2(Array.get(T.Ex, ex, x), nx, ri)

def kfetch_w(fs: Array<T.Ex> & U32, +x: U32, +ri: U32, +w: WP,
             +base: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  +w2 : WP = w
  kfc1(Bool.not(U32.is_eq(wp_op(w2), 2)), fs, x, ri, wp_c(w2), base)

# record the lbr of every export node, in index order (an export lists a
# term's children before it; a child not yet recorded reads as unknown)
# --- compaction at a rollback region's end ------------------------------
# A whnf region whose result is a NEW node cannot simply drop back to its
# mark. When it allocated a lot, its result's new part (the nodes at or
# above the mark reachable from it) is copied down to the mark instead:
# post-order, each node written to a scratch slot above nx with its
# children already relocated to their final indices, then the block moved
# down (kput, so the loose-bvar ranges are recomputed in place). Pointers
# the hash table holds into the old range are checked structurally on use,
# so they only cost sharing. A step machine (one non-recursive step, a
# fuel-driven loop) because Bend forbids mutual recursion.
type CSd is Data:
  CSd{done: Bool, stack: List<&2, U32>, k: U32, map: R.Tr<U32>, nx: U32,
      mark: U32, base: U32}

def kchildren(+x: T.Ex) -> List<&2, U32>:
  match x:
    case T.EApp{f, a}:
      [f, a]
    case T.ELam{n, t, b, bi}:
      [t, b]
    case T.EAll{n, t, b, bi}:
      [t, b]
    case T.ELet{n, t, v, b}:
      [t, v, b]
    case T.EProj{tn, i, sx}:
      [sx]
    case _:
      []

# first child at/above mark that is not yet mapped (sentinel if none)
def kunmapped(cs: List<&2, U32>, +mark: U32, +m: R.Tr<U32>) -> U32:
  match cs:
    case Nil{}:
      4294967295
    case Con{c, t}:
      +c2 : U32 = c
      +m2 : R.Tr<U32> = m
      S.pick(U32.is_ge(c2, mark)
             && U32.is_eq(R.get(U32, 64n, m2, c2, 4294967295), 4294967295),
             c2, kunmapped(t, mark, m2))

def kmapc(+c: U32, +mark: U32, +m: R.Tr<U32>) -> U32:
  S.pick(U32.is_lt(c, mark), c, R.get(U32, 64n, m, c, 4294967295))

def kreloc(+x: T.Ex, +mark: U32, +m: R.Tr<U32>) -> T.Ex:
  match x:
    case T.EApp{f, a}:
      T.EApp{kmapc(f, mark, m), kmapc(a, mark, m)}
    case T.ELam{n, t, b, bi}:
      T.ELam{n, kmapc(t, mark, m), kmapc(b, mark, m), bi}
    case T.EAll{n, t, b, bi}:
      T.EAll{n, kmapc(t, mark, m), kmapc(b, mark, m), bi}
    case T.ELet{n, t, v, b}:
      T.ELet{n, kmapc(t, mark, m), kmapc(v, mark, m), kmapc(b, mark, m)}
    case T.EProj{tn, i, sx}:
      T.EProj{tn, i, kmapc(sx, mark, m)}
    case y:
      y

# one step on the top of the stack, whose node is `nd`
# place a relocated node: an equal OLDER node (below mark) found through the
# hash table is reused; otherwise it takes the next final slot, written to
# scratch, and its pointer goes into the table (pointers at or above mark
# are tombstones here, so such a slot is reused)
def kcs8b(pr: Array<T.Ex> & U32, +fe: U32, +fin: U32,
          +rn: T.Ex) -> Array<T.Ex>:
  match pr:
    case Tuple{a, ep}:
      Array.set(T.Ex, a, fe, T.EProj{ep, fin, kfp(rn)})

def kcs8(+haveslot: Bool, +fe: U32, a: Array<T.Ex>, +fin: U32,
         +rn: T.Ex, +base: U32) -> Array<T.Ex>:
  match haveslot:
    case True{}:
      kcs8b(kep2(Array.get(T.Ex, a, kep_slot(base))), fe, fin, rn)
    case False{}:
      a

def kcs7(+miss: Bool, +haveslot: Bool, +found: U32, +fe: U32, a: Array<T.Ex>,
         +top: U32, +rest: List<&2, U32>, +rn: T.Ex, +k: U32, +m: R.Tr<U32>,
         +nx: U32, +mark: U32, +base: U32) -> Array<T.Ex> & CSd:
  match miss:
    case True{}:
      +fin : U32 = (mark + k : U32)
      (Array.set(T.Ex, kcs8(haveslot, fe, a, fin, rn, base), (nx + k : U32), rn),
       CSd{False{}, rest, (k + 1 : U32),
           R.set(U32, 64n, m, top, fin, 4294967295), nx, mark, base})
    case False{}:
      (a, CSd{False{}, rest, k, R.set(U32, 64n, m, top, found, 4294967295),
              nx, mark, base})

def kcs6(r: Array<T.Ex> & (U32 & U32), +top: U32, +rest: List<&2, U32>,
         +rn: T.Ex, +k: U32, +m: R.Tr<U32>, +nx: U32, +mark: U32,
         +base: U32) -> Array<T.Ex> & CSd:
  match r:
    case Tuple{a, Tuple{found, fempty}}:
      +f2 : U32 = found
      +fe : U32 = fempty
      kcs7(U32.is_eq(f2, 4294967295), U32.is_ne(fe, 4294967295), f2, fe, a,
           top, rest, rn, k, m, nx, mark, base)

def kcs4(+leaf: Bool, +c: U32, +top: U32, +rest: List<&2, U32>, +nd: T.Ex,
         +k: U32, +m: R.Tr<U32>, a: Array<T.Ex>, +nx: U32,
         +mark: U32, +base: U32) -> Array<T.Ex> & CSd:
  match leaf:
    case True{}:
      # every child placed: relocate, then share or place it
      +rn : T.Ex = kreloc(nd, mark, m)
      +fp : U32 = kfp(rn)
      +s0 : U32 = (base + U32.and(fp, kmask()) : U32)
      kcs6(kscan(24n, False{}, base, rn, s0, 4294967295, 4294967295, False{}, mark, fp,
                 kprobe_slot(a, s0, mark, fp, True{}, rn, base)),
           top, rest, rn, k, m, nx, mark, base)
    case False{}:
      (a, CSd{False{}, Con{c, Con{top, rest}}, k, m, nx, mark, base})

def kcs3(+top: U32, +rest: List<&2, U32>, +nd: T.Ex, +k: U32,
         +m: R.Tr<U32>, a: Array<T.Ex>, +nx: U32,
         +mark: U32, +base: U32) -> Array<T.Ex> & CSd:
  +n2 : T.Ex = nd
  +c : U32 = kunmapped(kchildren(n2), mark, m)
  kcs4(U32.is_eq(c, 4294967295), c, top, rest, n2, k, m, a, nx, mark, base)

def kcs2(pr: Array<T.Ex> & T.Ex, +top: U32, +rest: List<&2, U32>, +k: U32,
         +m: R.Tr<U32>, +nx: U32, +mark: U32,
         +base: U32) -> Array<T.Ex> & CSd:
  match pr:
    case Tuple{a, nd}:
      kcs3(top, rest, nd, k, m, a, nx, mark, base)

def kcs_step2(+skip: Bool, +top: U32, +rest: List<&2, U32>, +k: U32,
              +m: R.Tr<U32>, a: Array<T.Ex>, +nx: U32,
              +mark: U32, +base: U32) -> Array<T.Ex> & CSd:
  match skip:
    case True{}:
      (a, CSd{False{}, rest, k, m, nx, mark, base})
    case False{}:
      kcs2(Array.get(T.Ex, a, top), top, rest, k, m, nx, mark, base)

def kcs_step(a: Array<T.Ex>, st: CSd) -> Array<T.Ex> & CSd:
  match st:
    case CSd{done, Nil{}, k, m, nx, mark, base}:
      (a, CSd{True{}, Nil{}, k, m, nx, mark, base})
    case CSd{done, Con{top, rest}, k, m, nx, mark, base}:
      +t2 : U32 = top
      +m2 : R.Tr<U32> = m
      +mk : U32 = mark
      kcs_step2(U32.is_lt(t2, mk)
                || Bool.not(U32.is_eq(R.get(U32, 64n, m2, t2, 4294967295),
                                      4294967295)),
                t2, rest, k, m2, a, nx, mk, base)

def kcs_loop(fuel: Nat, st: Array<T.Ex> & CSd) -> Array<T.Ex> & CSd:
  match fuel st:
    case 0n _:
      st
    case 1n+p Tuple{a, CSd{True{}, stack, k, m, nx, mark, base}}:
      (a, CSd{True{}, stack, k, m, nx, mark, base})
    case 1n+p Tuple{a, CSd{False{}, stack, k, m, nx, mark, base}}:
      kcs_loop(p, kcs_step(a, CSd{False{}, stack, k, m, nx, mark, base}))

# move the scratch block [nx, nx+k) down to [mark, mark+k)
def kmove2(pr: Array<T.Ex> & T.Ex, +j: U32, +mark: U32,
           +hb: U32) -> Array<T.Ex>:
  match pr:
    case Tuple{a, nd}:
      kput(hb, a, (mark + j : U32), nd)

def kmove(n: Nat, +j: U32, +nx: U32, +mark: U32, +hb: U32,
          a: Array<T.Ex>) -> Array<T.Ex>:
  match n:
    case 0n:
      a
    case 1n+p:
      kmove(p, (j + 1 : U32), nx, mark, hb,
            kmove2(Array.get(T.Ex, a, (nx + j : U32)), j, mark, hb))

# --- verification of a compaction copy (before the move) ----------------
# A pairwise deep comparison of the old subgraph (old indices) with the copy
# (final indices: below mark the node itself, from mark the scratch slot
# nx + (i - mark)). Any mismatch keeps the region as it was.
type CVd is Data:
  CVd{done: Bool, ok: Bool, stack: List<&2, U32>, seen: R.Tr<U32>, nx: U32,
      mark: U32}

def kcv_new(+i: U32, +nx: U32, +mark: U32) -> U32:
  S.pick(U32.is_lt(i, mark), i, (nx + (i - mark : U32) : U32))

# same tag and payload; push the child pairs (old, new) onto the stack
def kcv_cmp(+x: T.Ex, +y: T.Ex, st: List<&2, U32>) -> Bool & List<&2, U32>:
  match x y:
    case T.EApp{f, a} T.EApp{g, b}:
      (True{}, Con{f, Con{g, Con{a, Con{b, st}}}})
    case T.ELam{n, t, b, bi} T.ELam{m, u, c, b2}:
      (True{}, Con{t, Con{u, Con{b, Con{c, st}}}})
    case T.EAll{n, t, b, bi} T.EAll{m, u, c, b2}:
      (True{}, Con{t, Con{u, Con{b, Con{c, st}}}})
    case T.ELet{n, t, v, b} T.ELet{m, u, w, c}:
      (True{}, Con{t, Con{u, Con{v, Con{w, Con{b, Con{c, st}}}}}})
    case T.EProj{tn, i, sx} T.EProj{t2, j, s2}:
      (U32.is_eq(tn, t2) && U32.is_eq(i, j), Con{sx, Con{s2, st}})
    case xx yy:
      (kexeq(xx, yy), st)

def kcv4(r: Bool & List<&2, U32>, a: Array<T.Ex>, +sn: R.Tr<U32>,
         +nx: U32, +mark: U32) -> Array<T.Ex> & CVd:
  match r:
    case Tuple{good, st}:
      (a, CVd{False{}, good, st, sn, nx, mark})

def kcv3(pr: Array<T.Ex> & T.Ex, +x: T.Ex, +rest: List<&2, U32>,
         +sn: R.Tr<U32>, +nx: U32, +mark: U32) -> Array<T.Ex> & CVd:
  match pr:
    case Tuple{a, y}:
      kcv4(kcv_cmp(x, y, rest), a, sn, nx, mark)

def kcv2(pr: Array<T.Ex> & T.Ex, +nw: U32, +rest: List<&2, U32>,
         +sn: R.Tr<U32>, +nx: U32, +mark: U32) -> Array<T.Ex> & CVd:
  match pr:
    case Tuple{a, x}:
      kcv3(Array.get(T.Ex, a, kcv_new(nw, nx, mark)), x, rest, sn, nx, mark)

# an old node already compared (the copy maps each old node to one new
# node, so its subgraph need not be walked again), or unchanged
def kcv_pair(+skip: Bool, +o: U32, +nw: U32, +rest: List<&2, U32>,
             +sn: R.Tr<U32>, a: Array<T.Ex>, +nx: U32,
             +mark: U32) -> Array<T.Ex> & CVd:
  match skip:
    case True{}:
      (a, CVd{False{}, True{}, rest, sn, nx, mark})
    case False{}:
      kcv2(Array.get(T.Ex, a, o), nw, rest,
           R.set(U32, 64n, sn, o, 1, 4294967295), nx, mark)

def kcv_step(a: Array<T.Ex>, st: CVd) -> Array<T.Ex> & CVd:
  match st:
    case CVd{done, ok, Con{o, Con{nw, rest}}, sn, nx, mark}:
      +o2 : U32 = o
      +n3 : U32 = nw
      +s2 : R.Tr<U32> = sn
      kcv_pair(U32.is_eq(o2, n3)
               || Bool.not(U32.is_eq(R.get(U32, 64n, s2, o2, 4294967295),
                                     4294967295)),
               o2, n3, rest, s2, a, nx, mark)
    case CVd{done, ok, stack, sn, nx, mark}:
      (a, CVd{True{}, ok, Nil{}, sn, nx, mark})

def kcv_loop(fuel: Nat, st: Array<T.Ex> & CVd) -> Array<T.Ex> & CVd:
  match fuel st:
    case 0n Tuple{a, CVd{done, ok, stack, sn, nx, mark}}:
      (a, CVd{True{}, False{}, stack, sn, nx, mark})
    case 1n+p Tuple{a, CVd{True{}, ok, stack, sn, nx, mark}}:
      (a, CVd{True{}, ok, stack, sn, nx, mark})
    case 1n+p Tuple{a, CVd{False{}, False{}, stack, sn, nx, mark}}:
      (a, CVd{True{}, False{}, stack, sn, nx, mark})
    case 1n+p Tuple{a, CVd{False{}, True{}, stack, sn, nx, mark}}:
      kcv_loop(p, kcv_step(a, CVd{False{}, True{}, stack, sn, nx, mark}))

# copy the result's new part down to mark: (store, new nx, new result);
# a stack left non-empty (fuel short) keeps the region as it was
def kcomp_fin2(+ok: Bool, a: Array<T.Ex>, +nnx: U32, +nroot: U32,
               +root: U32, +nx0: U32) -> ((Array<T.Ex> & U32) & U32):
  match ok:
    case True{}:
      ((a, nnx), nroot)
    case False{}:
      ((a, nx0), root)

def kcomp_ver(+done: Bool, r: Array<T.Ex> & CVd, +k: U32, +nr: U32,
              +root: U32, +nx0: U32, +hb: U32) -> ((Array<T.Ex> & U32) & U32):
  match r:
    case Tuple{a, CVd{vdone, ok, stack, sn, nx, mark}}:
      +good : Bool = done && ok
      +k2 : U32 = k
      +mk : U32 = mark
      kcomp_fin2(good, kmove(U32.to_nat(S.pick(good, k2, 0)), 0, nx, mk, hb, a),
                 (mk + k2 : U32), nr, root, nx0)

def kcomp_fin(st: Array<T.Ex> & CSd, +root: U32, +hb: U32,
              +nx0: U32) -> ((Array<T.Ex> & U32) & U32):
  match st:
    case Tuple{a, CSd{done0, stack, k, m, nx, mark, base}}:
      +done : Bool = done0
      +k2 : U32 = k
      +mk : U32 = mark
      +nr : U32 = kmapc(root, mk, m)
      +n3 : U32 = nx
      kcomp_ver(done, kcv_loop(U32.to_nat(S.pick(done, (16 * (n3 - mk) + 64 : U32), 0)),
                               (a, CVd{False{}, True{}, [root, nr], R.TNil{}, n3,
                                       mk})),
                k2, nr, root, nx0, hb)

def kcompact(a: Array<T.Ex>, +nx: U32, +mark: U32, +root: U32,
             +base: U32) -> ((Array<T.Ex> & U32) & U32):
  +n2 : U32 = nx
  kcomp_fin(kcs_loop(U32.to_nat((16 * (n2 - mark) + 64 : U32)),
                     (a, CSd{False{}, [root], 0, R.TNil{}, n2, mark, base})),
            root, khalf(base), n2)

# the same with a short scan: a result that is a large part of the region
# runs it out (not done), and the region stays as it is
def kcompact_s(a: Array<T.Ex>, +nx: U32, +mark: U32, +root: U32,
               +base: U32) -> ((Array<T.Ex> & U32) & U32):
  +n2 : U32 = nx
  kcomp_fin(kcs_loop(U32.to_nat((2 * (n2 - mark) + 64 : U32)),
                     (a, CSd{False{}, [root], 0, R.TNil{}, n2, mark, base})),
            root, khalf(base), n2)

# record the lbr of every export node, in index order (an export lists a
# term's children before it; a child not yet recorded reads as unknown)
def klb_init2(pr: Array<T.Ex> & T.Ex, +i: U32, +hb: U32) -> Array<T.Ex>:
  match pr:
    case Tuple{a, nd}:
      kput(hb, a, i, nd)

def klb_init(n: Nat, +i: U32, +hb: U32, a: Array<T.Ex>) -> Array<T.Ex>:
  match n:
    case 0n:
      a
    case 1n+p:
      klb_init(p, (i + 1 : U32), hb, klb_init2(Array.get(T.Ex, a, i), i, hb))

# a miss: append the node at nx and point the free slot (if any) at it
def kfin2b(+hb: U32, +haveslot: Bool, +fempty: U32, ex: Array<T.Ex>,
           +node: T.Ex, +nx: U32, +ep: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match haveslot:
    case True{}:
      +n : U32 = nx
      +nd : T.Ex = node
      (((Array.set(T.Ex, kput(hb, ex, n, nd), fempty, T.EProj{ep, n, kfp(nd)}),
         (n + 1 : U32)), MN{}), n)
    case False{}:
      +n : U32 = nx
      (((kput(hb, ex, n, node), (n + 1 : U32)), MN{}), n)

def kfin1b(+hb: U32, +miss: Bool, +found: U32, +fempty: U32, ex: Array<T.Ex>,
           +node: T.Ex, +nx: U32, +ep: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match miss:
    case False{}:
      (((ex, nx), MN{}), found)
    case True{}:
      kfin2b(hb, U32.is_ne(fempty, 4294967295), fempty, ex, node, nx, ep)

def kfinE(pr: Array<T.Ex> & U32, +found: U32, +fempty: U32, +node: T.Ex,
          +nx: U32, +base: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match pr:
    case Tuple{ex, ep}:
      +fd : U32 = found
      kfin1b(khalf(base), U32.is_eq(fd, 4294967295), fd, fempty, ex, node, nx,
             ep)

def kfin(r: Array<T.Ex> & (U32 & U32), +node: T.Ex, +nx: U32,
         +base: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match r:
    case Tuple{ex, Tuple{found, fempty}}:
      kfinE(kep2(Array.get(T.Ex, ex, kep_slot(base))), found, fempty, node,
            nx, base)

# a new declaration: retire every table pointer the previous ones left
def kbump2(pr: Array<T.Ex> & T.Ex, +base: U32) -> Array<T.Ex>:
  match pr:
    case Tuple{a, e}:
      Array.set(T.Ex, a, kep_slot(base), T.EBVar{(kep_of(e) + 1 : U32)})

def kbump(a: Array<T.Ex>, +base: U32) -> Array<T.Ex>:
  kg_decl(kfl_clear(kbump2(Array.get(T.Ex, a, kep_slot(base)), base), base),
          khalf(base))

def kalloc(fs: Array<T.Ex> & U32, +node: T.Ex,
           +base: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fs:
    case Tuple{ex, nx}:
      +nd : T.Ex = node
      +n2 : U32 = nx
      +fp : U32 = kfp(nd)
      +s0 : U32 = (base + U32.and(fp, kmask()) : U32)
      kfin(kscan(24n, False{}, base, nd, s0, 4294967295, 4294967295, False{}, n2, fp,
                 kprobe_slot(ex, s0, n2, fp, True{}, nd, base)),
           nd, n2, base)

# no allocation, result register = existing index
def kkeep(fs: Array<T.Ex> & U32,
          +e: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  ((fs, MN{}), e)

# allocate if changed, else keep e
def kalloc_if(+chg: Bool, fs: Array<T.Ex> & U32, +node: T.Ex,
              +e: U32, +base: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match chg:
    case True{}:
      kalloc(fs, node, base)
    case False{}:
      kkeep(fs, e)

# lift's bvar leaf: shift a free index, keep a bound one
def kbv_lift(fs: Array<T.Ex> & U32, +i: U32, +e: U32, +c: U32,
             +d: U32, +base: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  kalloc_if(U32.is_ge(i, c), fs, T.EBVar{(i + d : U32)}, e, base)

# inst's bvar leaf, after the sentinel walk
def kbv_fin(+iseq: Bool, +isgt: Bool, fs: Array<T.Ex> & U32, +ri: U32,
            +i: U32, +e: U32, +base: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match iseq:
    case True{}:
      kkeep(fs, ri)
    case False{}:
      kalloc_if(isgt, fs, T.EBVar{(i - 1 : U32)}, e, base)

def kbv_finm(+inr: Bool, +isgt: Bool, fs: Array<T.Ex> & U32, +ri: U32,
             +i: U32, +m: U32, +e: U32,
             +base: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match inr:
    case True{}:
      kkeep(fs, ri)
    case False{}:
      kalloc_if(isgt, fs, T.EBVar{(i - m : U32)}, e, base)

# lsubst's sort leaf, decided
def ksort3(+same: Bool, fs: Array<T.Ex> & U32, +nlx: U32,
           +e: U32, +base: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match same:
    case True{}:
      kkeep(fs, e)
    case False{}:
      kalloc(fs, T.ESort{nlx}, base)

# lsubst's const leaf: allocate the constant over fresh level indices
def ksconst(fs: Array<T.Ex> & U32, +n: U32,
            +xs: List<&2, U32>, +base: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  kalloc(fs, T.EConst{n, xs}, base)

# rebuild the leftover arg spine over head h (infer.bend's rebuild)
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

# the spine with the head's INDEX as the register (is_def_eq_app compares
# the heads by DSub, which takes indices)
def kspine_i(fuel: Nat, acc: List<&2, U32>, +cur: U32, +nx: U32,
             pr: Array<T.Ex> & T.Ex) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fuel pr:
    case 0n Tuple{a, nd}:
      (((a, nx), MSP{nd, acc}), cur)
    case 1n+p Tuple{a, nd}:
      match nd:
        case T.EApp{f, g}:
          +f2 : U32 = f
          kspine_i(p, Con{g, acc}, f2, nx, Array.get(T.Ex, a, f2))
        case y:
          (((a, nx), MSP{y, acc}), cur)

def kspine_itin(fs: Array<T.Ex> & U32,
                +i: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fs:
    case Tuple{ex, nx}:
      +i2 : U32 = i
      kspine_i(256n, Nil{}, i2, nx, Array.get(T.Ex, ex, i2))

# the three literal operations on decimal digits (infer.bend's lit_op)
def klit(fs: Array<T.Ex> & U32, +aw: U32, +da: List<&2, U32>,
         +db: List<&2, U32>, +tn: U32,
         +fn2: U32, +base: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match aw:
    case 0:
      kalloc(fs, T.ENat{I.dec_add(da, db)}, base)
    case 1:
      kalloc(fs, T.ENat{I.dec_sub(da, db)}, base)
    case 2:
      kalloc(fs, T.EConst{S.pick(I.dec_le(da, db), tn, fn2), Nil{}}, base)
    case 3:
      kalloc(fs, T.ENat{I.dec_mul(da, db)}, base)
    case 4:
      kalloc(fs, T.ENat{I.dec_pow(da, db)}, base)
    case 5:
      kalloc(fs, T.ENat{I.dec_div(da, db)}, base)
    case 6:
      kalloc(fs, T.ENat{I.dec_mod(da, db)}, base)
    case 7:
      kalloc(fs, T.EConst{S.pick(I.dec_eq(da, db), tn, fn2), Nil{}}, base)
    case 8:
      kalloc(fs, T.ENat{I.dec_bitop(0, da, db)}, base)
    case 9:
      kalloc(fs, T.ENat{I.dec_bitop(1, da, db)}, base)
    case 10:
      kalloc(fs, T.ENat{I.dec_bitop(2, da, db)}, base)
    case 11:
      kalloc(fs, T.ENat{I.dec_shl(da, db)}, base)
    case 12:
      kalloc(fs, T.ENat{I.dec_shr(da, db)}, base)
    case _:
      kalloc(fs, T.ENat{I.dec_gcd(da, db)}, base)

# --- iota reduct construction (infer.bend's build_ihs tail + nat_expand) ---
def kwith_msg(r: (Array<T.Ex> & U32) & U32,
              +m: MG) -> ((Array<T.Ex> & U32) & MG) & U32:
  match r:
    case Tuple{fs, i}:
      ((fs, m), i)

def ktin_of(r: (Array<T.Ex> & U32) & U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match r:
    case Tuple{fs, x}:
      ((fs, MN{}), x)

def kdrop1(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

# ri = 1 when both terms are closed (lbr 0)
def kcl3(pr: Array<T.Ex> & U32, +lx: U32,
         +nx: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match pr:
    case Tuple{a, ly}:
      (((a, nx), MN{}), S.pick(U32.is_eq(lx, 0) && U32.is_eq(ly, 0), 1, 0))

def kcl2(pr: Array<T.Ex> & U32, +y: U32, +nx: U32,
         +hb: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match pr:
    case Tuple{a, lx}:
      kcl3(klb_get(a, y, hb), lx, nx)

def kclosed(fs: Array<T.Ex> & U32, +x: U32, +y: U32,
            +base: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fs:
    case Tuple{ex, nx}:
      +hb : U32 = khalf(base)
      kcl2(klb_get(ex, x, hb), y, nx, hb)

# the larger loose-bvar range of two nodes as the register (0: closed): the
# success cache for open pairs is keyed on the binder context's PREFIX of
# that length only -- the binders the pair can see -- so a pair met again
# deeper, under more binders, still hits
def kcl3m(pr: Array<T.Ex> & U32, +lx: U32,
          +nx: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match pr:
    case Tuple{a, ly}:
      (((a, nx), MN{}), U32.max(lx, ly))

def kcl2m(pr: Array<T.Ex> & U32, +y: U32, +nx: U32,
          +hb: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match pr:
    case Tuple{a, lx}:
      kcl3m(klb_get(a, y, hb), lx, nx)

def kclmax(fs: Array<T.Ex> & U32, +x: U32, +y: U32,
           +base: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fs:
    case Tuple{ex, nx}:
      +hb : U32 = khalf(base)
      kcl2m(klb_get(ex, x, hb), y, nx, hb)

def kctxh_n(n: Nat, xs: List<&2, U32>, +h: U32) -> U32:
  match n xs:
    case 0n _:
      h
    case 1n+p Nil{}:
      h
    case 1n+p Con{head, tail}:
      kctxh_n(p, tail, (((h * 31 : U32) + head : U32) + 1 : U32))

# hash-consed allocation, store and index only
def kstrip(t: ((Array<T.Ex> & U32) & MG) & U32) -> (Array<T.Ex> & U32) & U32:
  match t:
    case Tuple{Tuple{fs, m}, i}:
      (fs, i)

def khc(fs: Array<T.Ex> & U32, +node: T.Ex,
        +base: U32) -> (Array<T.Ex> & U32) & U32:
  kstrip(kalloc(fs, node, base))

# structure eta for iota (Lean's to_cnstr_when_structure): the fields of a
# major premise x of a structure-like inductive are its projections
# x.0 .. x.(nf-1), returned as an MSP's argument list
# --- string literals (Lean's string_lit_to_constructor) ---------------
# A literal is its UTF-8 bytes; its constructor form is
#   String.ofList [Char.ofNat c0, .., Char.ofNat cn]
# over the code points (List.{0} Char). Lean expands a literal only where a
# projection meets one (reduce_proj_core) and against a String.ofList
# application in defeq (try_string_lit_expansion).
# decimal digits (ASCII, most significant first) of n; the fuel bounds the
# digit count (S.pick evaluates the recursive branch too: 12 levels at most)
# the first n entries of xs, reversed (a Bool match: S.pick_l would walk
# the whole context and rebuild the prefix at every step)
def kpre_rev2(xs: List<&2, U32>, +stop: Bool, +n: U32,
              acc: List<&2, U32>) -> List<&2, U32>:
  match xs stop:
    case _ True{}:
      acc
    case Nil{} False{}:
      acc
    case Con{h, t} False{}:
      kpre_rev2(t, U32.is_eq(n, 1), (n - 1 : U32), Con{h, acc})

def kpre_rev(+n: U32, xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  kpre_rev2(xs, U32.is_eq(n, 0), n, acc)

# the canonical node of a context prefix (outermost first): EApp{t, rest}
# chains over root 0, hash-consed
def kctxid(xs: List<&2, U32>, r: (Array<T.Ex> & U32) & U32,
           +base: U32) -> (Array<T.Ex> & U32) & U32:
  match xs r:
    case Nil{} _:
      r
    case Con{t, rest} Tuple{fs, acc}:
      kctxid(rest, khc(fs, T.EApp{t, acc}, base), base)

def kdec(fuel: Nat, +n: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match fuel:
    case 0n:
      acc
    case 1n+p:
      +d : U32 = (48 + (n % 10 : U32) : U32)
      +a2 : List<&2, U32> = Con{d, acc}
      S.pick_l(U32.is_lt(n, 10), a2, kdec(p, (n / 10 : U32), a2))

def kpush_if(+go: Bool, +x: U32, xs: List<&2, U32>) -> List<&2, U32>:
  match go:
    case True{}:
      Con{x, xs}
    case False{}:
      xs

# UTF-8 bytes -> code points, reversed (need: continuation bytes pending)
def kutf8(xs: List<&2, U32>, +cp: U32, +need: U32,
          acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{b, t}:
      +b2 : U32 = b
      +lead : Bool = U32.is_eq(need, 0)
      +cp1 : U32 = S.pick(U32.is_lt(b2, 128), b2,
                     S.pick(U32.is_lt(b2, 224), U32.and(b2, 31),
                       S.pick(U32.is_lt(b2, 240), U32.and(b2, 15),
                              U32.and(b2, 7))))
      +nd1 : U32 = S.pick(U32.is_lt(b2, 128), 0,
                     S.pick(U32.is_lt(b2, 224), 1,
                       S.pick(U32.is_lt(b2, 240), 2, 3)))
      +cp2 : U32 = ((cp * 64 : U32) + U32.and(b2, 63) : U32)
      +cpn : U32 = S.pick(lead, cp1, cp2)
      +ndn : U32 = S.pick(lead, nd1, (need - 1 : U32))
      kutf8(t, cpn, ndn, kpush_if(U32.is_eq(ndn, 0), cpn, acc))

def kstr_cons2(r: (Array<T.Ex> & U32) & U32, +rest: U32,
               +base: U32) -> (Array<T.Ex> & U32) & U32:
  match r:
    case Tuple{fs, hd}:
      khc(fs, T.EApp{hd, rest}, base)


def kstr_cons(r: (Array<T.Ex> & U32) & U32, +lit: U32, +rest: U32,
              +consc: U32, +ofn: U32,
              +base: U32) -> (Array<T.Ex> & U32) & U32:
  match r:
    case Tuple{fs, chv}:
      kstr_cons2(khc(fs, T.EApp{consc, chv}, base), rest, base)

def kstr_lit(r: (Array<T.Ex> & U32) & U32, +ofn: U32,
             +base: U32) -> (Array<T.Ex> & U32) & U32:
  match r:
    case Tuple{fs, li}:
      khc(fs, T.EApp{ofn, li}, base)

# fold the reversed code points onto `rest` (the list built so far)
def kstr_go(cps: List<&2, U32>, r: (Array<T.Ex> & U32) & U32, +consc: U32,
            +ofn: U32, +base: U32) -> (Array<T.Ex> & U32) & U32:
  match cps r:
    case Nil{} _:
      r
    case Con{c, t} Tuple{fs, rest}:
      +rs2 : U32 = rest
      kstr_go(t,
              kstr_cons(kstr_lit(khc(fs, T.ENat{kdec(12n, c, Nil{})}, base),
                                 ofn, base),
                        0, rs2, consc, ofn, base),
              consc, ofn, base)

def kstr_fin(r: (Array<T.Ex> & U32) & U32, +ofl: U32,
             +base: U32) -> (Array<T.Ex> & U32) & U32:
  match r:
    case Tuple{fs, li}:
      khc(fs, T.EApp{ofl, li}, base)

def kstr_nil(r: (Array<T.Ex> & U32) & U32, +ch: U32,
             +base: U32) -> (Array<T.Ex> & U32) & U32:
  match r:
    case Tuple{fs, nl}:
      khc(fs, T.EApp{nl, ch}, base)


def kstr_b3(r: (Array<T.Ex> & U32) & U32, +ch: U32, +cps: List<&2, U32>,
            +ofn: U32, +ofl: U32, +niln: U32,
            +base: U32) -> (Array<T.Ex> & U32) & U32:
  match r:
    case Tuple{fs, consc}:
      +cc : U32 = consc
      kstr_fin(kstr_go(cps, kstr_nil(khc(fs, T.EConst{niln, [0]}, base), ch,
                                     base), cc, ofn, base), ofl, base)

def kstr_b2(r: (Array<T.Ex> & U32) & U32, +ch: U32, +cps: List<&2, U32>,
            +ofn: U32, +ofl: U32, +niln: U32,
            +base: U32) -> (Array<T.Ex> & U32) & U32:
  match r:
    case Tuple{fs, cons0}:
      kstr_b3(khc(fs, T.EApp{cons0, ch}, base), ch, cps, ofn, ofl, niln, base)

def kstr_b1(r: (Array<T.Ex> & U32) & U32, +cps: List<&2, U32>,
            +ofn: U32, +ofl: U32, +niln: U32, +consn: U32,
            +base: U32) -> (Array<T.Ex> & U32) & U32:
  match r:
    case Tuple{fs, ch}:
      +c2 : U32 = ch
      kstr_b2(khc(fs, T.EConst{consn, [0]}, base), c2, cps, ofn, ofl, niln,
              base)

def kstr_b0(r: (Array<T.Ex> & U32) & U32, +cps: List<&2, U32>,
            +ofl: U32, +niln: U32, +consn: U32, +charn: U32,
            +base: U32) -> (Array<T.Ex> & U32) & U32:
  match r:
    case Tuple{fs, ofn}:
      +o2 : U32 = ofn
      kstr_b1(khc(fs, T.EConst{charn, Nil{}}, base), cps, o2, ofl, niln,
              consn, base)

# the constructor form of a string literal with bytes d (none of the names
# missing: the caller checks qtt keys 21..25)
def kstr_b0b(r: (Array<T.Ex> & U32) & U32, +d: List<&2, U32>,
             +qtt: R.Tr<U32>, +base: U32) -> (Array<T.Ex> & U32) & U32:
  match r:
    case Tuple{fs, ofl}:
      +q : R.Tr<U32> = qtt
      +o2 : U32 = ofl
      kstr_b0(khc(fs, T.EConst{R.get(U32, 64n, q, 24, 4294967295), Nil{}},
                  base),
              kutf8(d, 0, 0, Nil{}), o2, R.get(U32, 64n, q, 22, 4294967295),
              R.get(U32, 64n, q, 23, 4294967295),
              R.get(U32, 64n, q, 25, 4294967295), base)

# all five names known (an export without them has no string literals
# worth expanding)

def kstrexp(fs: Array<T.Ex> & U32, +d: List<&2, U32>, +qtt: R.Tr<U32>,
            +base: U32) -> (Array<T.Ex> & U32) & U32:
  +q : R.Tr<U32> = qtt
  +ofl0 : U32 = R.get(U32, 64n, q, 21, 4294967295)
  kstr_b0b(khc(fs, T.EConst{ofl0, Nil{}}, base), d, q, base)

def kstr_ok(+qtt: R.Tr<U32>) -> Bool:
  +q : R.Tr<U32> = qtt
  Bool.not(U32.is_eq(R.get(U32, 64n, q, 21, 4294967295), 4294967295))
  && Bool.not(U32.is_eq(R.get(U32, 64n, q, 22, 4294967295), 4294967295))
  && Bool.not(U32.is_eq(R.get(U32, 64n, q, 23, 4294967295), 4294967295))
  && Bool.not(U32.is_eq(R.get(U32, 64n, q, 24, 4294967295), 4294967295))
  && Bool.not(U32.is_eq(R.get(U32, 64n, q, 25, 4294967295), 4294967295))

def kis_str(+x: T.Ex) -> Bool:
  match x:
    case T.EStr{d}:
      True{}
    case _:
      False{}

def kstr_bytes(+x: T.Ex) -> List<&2, U32>:
  match x:
    case T.EStr{d}:
      d
    case _:
      Nil{}

# the lazy probe's last pair, as a node EApp{x, y} (only the innermost
# unsettled iteration makes one: the register is 0 until then)
def klzpair(+mk: Bool, fs: Array<T.Ex> & U32, +x: U32, +y: U32, +r: U32,
            +base: U32) -> (Array<T.Ex> & U32) & U32:
  match mk:
    case True{}:
      khc(fs, T.EApp{x, y}, base)
    case False{}:
      (fs, r)

def kprojs_cons(r: (Array<T.Ex> & U32) & U32,
                acc: List<&2, U32>) -> (Array<T.Ex> & U32) & List<&2, U32>:
  match r:
    case Tuple{fs, j}:
      (fs, Con{j, acc})

def kprojs_go(fuel: Nat, +i: U32, +ind: U32, +maj: U32, +base: U32,
              r: (Array<T.Ex> & U32) & List<&2, U32>)
              -> (Array<T.Ex> & U32) & List<&2, U32>:
  match fuel r:
    case 0n Tuple{fs, acc}:
      (fs, acc)
    case 1n+p Tuple{fs, acc}:
      kprojs_go(p, (i + 1 : U32), ind, maj, base,
                kprojs_cons(khc(fs, T.EProj{ind, i, maj}, base), acc))

def kprojs_tin(r: (Array<T.Ex> & U32) & List<&2, U32>)
               -> ((Array<T.Ex> & U32) & MG) & U32:
  match r:
    case Tuple{fs, acc}:
      ((fs, MSP{T.EBad{}, I.rev_u(acc, Nil{})}), 0)

# struct eta is allowed for `ind` (check.bend records it under ind + 2^30:
# structure-like, not recursive, definitely not a Prop)
def kse_ok(+mt: R.Tr<I.Meta>, +ind: U32) -> Bool:
  U32.is_eq(I.meta_ver(R.get(I.Meta, 64n, mt, (ind + 1073741824 : U32),
                             I.MNone{})), 1)

# wrap a body in lambdas; doms arrive INNERMOST FIRST (the raw collection
# order), which is exactly the allocation order wrap_lams uses
def kwrapl(+base: U32, doms: List<&2, U32>,
           r: (Array<T.Ex> & U32) & U32) -> (Array<T.Ex> & U32) & U32:
  match doms r:
    case Nil{} Tuple{fs, b}:
      (fs, b)
    case Con{h, t} Tuple{fs, b}:
      kwrapl(base, t, khc(fs, T.ELam{0, h, b, 0}, base))

# fold an argument list onto a head (infer.bend's app_args)
def kapargs(+base: U32, xs: List<&2, U32>,
            r: (Array<T.Ex> & U32) & U32) -> (Array<T.Ex> & U32) & U32:
  match xs r:
    case Nil{} Tuple{fs, h}:
      (fs, h)
    case Con{x, t} Tuple{fs, h}:
      kapargs(base, t, khc(fs, T.EApp{h, x}, base))

def krebuild(+base: U32, args: List<&2, U32>, fs: Array<T.Ex> & U32,
             +h: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  ktin_of(kapargs(base, args, (fs, h)))

# a literal operation the machine computes (qtt keys 5-7, 11-15) on two
# arguments
def klitop(+n: U32, +la: U32, +q: R.Tr<U32>) -> Bool:
  U32.is_eq(la, 2) && Bool.not(U32.is_eq(n, 4294967295))
  && (U32.is_eq(n, R.get(U32, 64n, q, 5, 4294967295))
      || U32.is_eq(n, R.get(U32, 64n, q, 6, 4294967295))
      || U32.is_eq(n, R.get(U32, 64n, q, 7, 4294967295))
      || U32.is_eq(n, R.get(U32, 64n, q, 11, 4294967295))
      || U32.is_eq(n, R.get(U32, 64n, q, 12, 4294967295))
      || U32.is_eq(n, R.get(U32, 64n, q, 13, 4294967295))
      || U32.is_eq(n, R.get(U32, 64n, q, 14, 4294967295))
      || U32.is_eq(n, R.get(U32, 64n, q, 15, 4294967295))
      || U32.is_eq(n, R.get(U32, 64n, q, 26, 4294967295))
      || U32.is_eq(n, R.get(U32, 64n, q, 27, 4294967295))
      || U32.is_eq(n, R.get(U32, 64n, q, 28, 4294967295))
      || U32.is_eq(n, R.get(U32, 64n, q, 29, 4294967295))
      || U32.is_eq(n, R.get(U32, 64n, q, 30, 4294967295))
      || U32.is_eq(n, R.get(U32, 64n, q, 31, 4294967295)))

# the probe failure cache's key (0xC0000000..0xFFFFFF00: clear of node
# indices, the x + 2^31 YES cache and the flags) and fingerprint
def klzkey(+x: U32, +y: U32) -> U32:
  (3221225472 + U32.and(((x * 2654435761 : U32) + (y * 40503 : U32) : U32),
                        1073741568) : U32)

def klzfp(+x: U32, +y: U32) -> U32:
  (((x * 65599 : U32) + y : U32) + 1 : U32)

# the success cache for OPEN pairs (Lean caches every is_def_eq success;
# km's closed-pair cache is exact, keyed by x alone). Three slots at a
# hashed key (0xA0000000..0xBFFFFFFF) hold x, y and a hash of the binder
# context -- all three verified on a hit, since a YES between open terms
# may rest on the binders' types (proof irrelevance, unit eta)
def kctxh(xs: List<&2, U32>, +h: U32) -> U32:
  match xs:
    case Nil{}:
      h
    case Con{head, tail}:
      kctxh(tail, (((h * 31 : U32) + head : U32) + 1 : U32))

def kokey(+x: U32, +y: U32, +ch: U32) -> U32:
  (2684354560
   + U32.and((((x * 2654435761 : U32) + (y * 40503 : U32) : U32)
              + (ch * 97 : U32) : U32), 536870904) : U32)

def kohit(+w: R.Tr<U32>, +x: U32, +y: U32, +ch: U32) -> Bool:
  +k : U32 = kokey(x, y, ch)
  +w2 : R.Tr<U32> = w
  U32.is_eq(R.get(U32, 64n, w2, k, 4294967295), x)
  && U32.is_eq(R.get(U32, 64n, w2, (k + 1 : U32), 4294967295), y)
  && U32.is_eq(R.get(U32, 64n, w2, (k + 2 : U32), 4294967295), ch)

def koset(+go: Bool, w: R.Tr<U32>, +x: U32, +y: U32, +ch: U32) -> R.Tr<U32>:
  match go:
    case True{}:
      +k : U32 = kokey(x, y, ch)
      R.set(U32, 64n,
            R.set(U32, 64n, R.set(U32, 64n, w, k, x, 4294967295),
                  (k + 1 : U32), y, 4294967295),
            (k + 2 : U32), ch, 4294967295)
    case False{}:
      w

def kbv(+h: T.Ex) -> U32:
  match h:
    case T.EBVar{i}:
      i
    case _:
      4294967295

def kis_proj(+h: T.Ex) -> Bool:
  match h:
    case T.EProj{tn, i, s}:
      True{}
    case _:
      False{}

# `s.i args` for the lazy probe's projection step
def klzpj(+base: U32, args: List<&2, U32>,
          r: (Array<T.Ex> & U32) & U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match r:
    case Tuple{fs, h}:
      ktin_of(kapargs(base, args, (fs, h)))

def kb3(+base: U32, r: (Array<T.Ex> & U32) & U32, items: List<&2, U32>, +rc: U32,
        doms: List<&2, U32>) -> ((Array<T.Ex> & U32) & MG) & U32:
  match r:
    case Tuple{fs, fz}:
      ktin_of(kwrapl(base, doms,
                     kapargs(base, List.append(&2, U32, items, Con{fz, Nil{}}),
                             (fs, rc))))

def kb2(+base: U32, r: (Array<T.Ex> & U32) & List<&2, U32>, +rc: U32, +fldL: U32,
        items: List<&2, U32>,
        doms: List<&2, U32>) -> ((Array<T.Ex> & U32) & MG) & U32:
  match r:
    case Tuple{fs, zs}:
      kb3(base, kapargs(base, zs, (fs, fldL)), items, rc, doms)

# allocate the q bound variables of the IH's lambda telescope, descending
def kbvs(+base: U32, cnt: Nat, +i: U32, acc: List<&2, U32>,
         r: (Array<T.Ex> & U32) & U32) -> (Array<T.Ex> & U32) & List<&2, U32>:
  match cnt r:
    case 0n Tuple{fs, last}:
      (fs, kdrop1(I.rev_u(Con{last, acc}, Nil{})))
    case 1n+p2 Tuple{fs, last}:
      kbvs(base, p2, (i - 1 : U32), Con{last, acc},
           khc(fs, T.EBVar{i}, base))

def kalloc2p(+base: U32, fs: Array<T.Ex> & U32,
             +node: T.Ex) -> (Array<T.Ex> & U32) & U32:
  khc(fs, node, base)

def kb1(+base: U32, r: (Array<T.Ex> & U32) & U32, +q: U32, +fldL: U32,
        items: List<&2, U32>,
        doms: List<&2, U32>) -> ((Array<T.Ex> & U32) & MG) & U32:
  match r:
    case Tuple{fs, rc}:
      +r2 : U32 = rc
      kb2(base, kbvs(base, U32.to_nat(q), (q - 1 : U32), Nil{},
                     (fs, 4294967295)), r2, fldL, items,
          doms)

# one inductive hypothesis, given the already-lifted outer terms: allocate
# the recursor constant, the z binders, `f z-bar`, the full application,
# and the wrapping lambdas -- in exactly the old allocation order
def kih_build(+base: U32, fs: Array<T.Ex> & U32, lifted: List<&2, U32>,
              ebni: List<&2, U32>, doms: List<&2, U32>, +q: U32, +cn: U32,
              +us: List<&2, U32>) -> ((Array<T.Ex> & U32) & MG) & U32:
  +lf : List<&2, U32> = lifted
  kb1(base, kalloc2p(base, fs, T.EConst{cn, us}), q, I.last_u(lf, 4294967295),
      List.append(&2, U32, I.drop_last(lf, Nil{}), ebni), doms)

# a nat literal expanded one constructor step (infer.bend's nat_expand)
def knat4(r: (Array<T.Ex> & U32) & U32, +i1: U32,
         +base: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match r:
    case Tuple{fs, i2}:
      kalloc(fs, T.EApp{i1, i2}, base)

def knat3(r: (Array<T.Ex> & U32) & U32, +d: List<&2, U32>,
         +base: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match r:
    case Tuple{fs, i1}:
      knat4(khc(fs, T.ENat{I.dec_sub1(I.rev_u(d, Nil{}), True{}, Nil{})},
                base), i1, base)

def knatexp2(+base: U32, z: Bool, fs: Array<T.Ex> & U32, +d: List<&2, U32>,
             +zn: U32, +sn: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match z:
    case True{}:
      kalloc(fs, T.EConst{zn, Nil{}}, base)
    case False{}:
      knat3(khc(fs, T.EConst{sn, Nil{}}, base), d, base)

def knatexp(+base: U32, fs: Array<T.Ex> & U32, +d: List<&2, U32>, +zn: U32,
            +sn: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  +d2 : List<&2, U32> = d
  knatexp2(base, I.dec_is_zero(d2), fs, d2, zn, sn)

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

# the oracle eval frame, fuel-guarded (the old sl's `case 0n`: unknown)
def kslev(+e: U32, +ctx: List<&2, U32>, +fu: U32) -> KF:
  pick_kf(U32.is_eq(fu, 0), SLUn{}, SLEv{e, ctx, fu})

# answer an inference result
def kmir(fs: Array<T.Ex> & U32, +ty: U32,
         +ok: Bool) -> ((Array<T.Ex> & U32) & MG) & U32:
  ((fs, MIR{ty, ok}), 0)

# a tri verdict with an explicit register
def kmtri_r(r: (Array<T.Ex> & U32) & U32,
            +t: L.Tri) -> ((Array<T.Ex> & U32) & MG) & U32:
  match r:
    case Tuple{fs, i}:
      ((fs, MTri{t}), i)

# answer a tri verdict
def kmtri(fs: Array<T.Ex> & U32,
          +t: L.Tri) -> ((Array<T.Ex> & U32) & MG) & U32:
  ((fs, MTri{t}), 0)

# answer a level normal form
def kmln(fs: Array<T.Ex> & U32,
         +l: L.LN) -> ((Array<T.Ex> & U32) & MG) & U32:
  ((fs, MLn{l}), 0)

# walk n Pi binders and answer the node after them (infer.bend's
# sl_tele_after: a non-Pi before the end answers EBad)
def ktele_go(n: Nat, +nx: U32,
             pr: Array<T.Ex> & T.Ex) -> ((Array<T.Ex> & U32) & MG) & U32:
  match n pr:
    case 0n Tuple{a, nd}:
      (((a, nx), MX{nd}), 0)
    case 1n+q Tuple{a, nd}:
      match nd:
        case T.EAll{nm, t, b, bi}:
          ktele_go(q, nx, Array.get(T.Ex, a, b))
        case y:
          (((a, nx), MX{T.EBad{}}), 0)

def ktele_tin(fs: Array<T.Ex> & U32, +ti: U32,
              +cnt: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fs:
    case Tuple{ex, nx}:
      ktele_go(U32.to_nat(cnt), nx, Array.get(T.Ex, ex, ti))

def pick_us(+z: Bool, +x: List<&2, U32>, +y: List<&2, U32>)
    -> List<&2, U32>:
  match z:
    case True{}:
      x
    case False{}:
      y

def kis_cc(+x: T.Ex, +y: T.Ex) -> Bool:
  match x y:
    case T.EConst{n1, u1} T.EConst{n2, u2}:
      True{}
    case _ _:
      False{}

# structure-eta expansion: `acc (proj 0 yi) .. (proj (n-1) yi)`
def kpjapp(r: (Array<T.Ex> & U32) & U32, +acc: U32,
          +base: U32) -> (Array<T.Ex> & U32) & U32:
  match r:
    case Tuple{fs, pj}:
      khc(fs, T.EApp{acc, pj}, base)

def kprojb(+base: U32, n: Nat, +i: U32, +tn: U32, +yi: U32,
           r: (Array<T.Ex> & U32) & U32) -> (Array<T.Ex> & U32) & U32:
  match n r:
    case 0n Tuple{fs, acc}:
      (fs, acc)
    case 1n+q Tuple{fs, acc}:
      kprojb(base, q, (i + 1 : U32), tn, yi,
             kpjapp(khc(fs, T.EProj{tn, i, yi}, base), acc, base))

def kis_nil_u(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case _:
      False{}

def kpick_tr(+z: Bool, +x: R.Tr<U32>, +y: R.Tr<U32>) -> R.Tr<U32>:
  match z:
    case True{}:
      x
    case False{}:
      y

# the snapshot memo plus the current run's flags (INCOMPLETE, CORRUPT, the
# debug probe keys); CORRUPT also when the store overflowed meanwhile
def kflag1(+cur: R.Tr<U32>, +k: U32, +snap: R.Tr<U32>) -> R.Tr<U32>:
  +c2 : R.Tr<U32> = cur
  +v : U32 = R.get(U32, 64n, c2, k, 4294967295)
  # (set_if, a match: S.pick-style picks evaluate BOTH sides, and the
  # trie version not taken is built and then freed -- most of the
  # runtime's time went to that)
  R.set_if(U32, Bool.not(U32.is_eq(v, 4294967295)), snap, k, v, 4294967295)

def kflags_into(+cur: R.Tr<U32>, +snap: R.Tr<U32>, +ovf: Bool) -> R.Tr<U32>:
  +c2 : R.Tr<U32> = cur
  # the run's flags live in the store (kfl_*); only debug probe keys, when
  # tools/fprobe.sh splices them in here, are carried in the memo
  +s1 : R.Tr<U32> = snap
  s1

# a rollback region's memo afterwards: the snapshot plus the run's flags
# when it is released, else the current memo (CORRUPT on overflow) --
# a match, so only the chosen one is built
def krb_wm(+go: Bool, +ovf: Bool, +wm: R.Tr<U32>,
           +snap: R.Tr<U32>) -> R.Tr<U32>:
  match go:
    case True{}:
      kflags_into(wm, snap, ovf)
    case False{}:
      wm

def khgt(+qtt: R.Tr<U32>, +n: U32) -> U32:
  R.get(U32, 64n, qtt, (n + 2147483648 : U32), 0)

def kpick_us(+z: Bool, xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match z:
    case True{}:
      xs
    case False{}:
      ys

# the rule for constructor c in a flat [ctor, nfields, rhs, ...] list:
# (nfields, rhs), or sentinels
def krule_go(rs: List<&2, U32>, +c: U32, +hit: Bool, +want: U32,
             +res: U32) -> U32:
  match rs hit:
    case _ True{}:
      res
    case Con{ct, Con{nf, Con{rhs, t}}} False{}:
      +c2 : U32 = ct
      krule_go(t, c, U32.is_eq(c2, c), want,
               S.pick(U32.is_eq(want, 0), nf, rhs))
    case _ False{}:
      4294967295

def krule_nf(rs: List<&2, U32>, +c: U32) -> U32:
  krule_go(rs, c, False{}, 0, 4294967295)

def krule_rhs(rs: List<&2, U32>, +c: U32) -> U32:
  krule_go(rs, c, False{}, 1, 4294967295)

# the rhs's arguments: params, motives, minors (the recursor's first `pre`
# arguments), the major's last `nf` arguments (its fields), and whatever
# followed the major
def kri_args(+args: List<&2, U32>, +pre: U32, +mj: U32,
             +sargs: List<&2, U32>, +nf: U32) -> List<&2, U32>:
  +a2 : List<&2, U32> = args
  +s2 : List<&2, U32> = sargs
  List.append(&2, U32, I.take_u(a2, pre, Nil{}),
              List.append(&2, U32,
                          I.skip_u(s2, (I.len_u(s2, 0) - nf : U32)),
                          I.skip_u(a2, (mj + 1 : U32))))

# the shared-argument record (IApR): a reserved store slot right below the
# allocation region, EApp{argument, type | ok << 31}
def krec_slot(+hcb: U32) -> U32:
  (hcb + ktbl() : U32)

def krec_write(fs: Array<T.Ex> & U32, +slot: U32, +a: U32, +t: U32,
               +ok: Bool) -> Array<T.Ex> & U32:
  match fs:
    case Tuple{ex, nx}:
      (Array.set(T.Ex, ex, slot,
                 T.EApp{a, (t + S.pick(ok, 2147483648, 0) : U32)}), nx)

# a fully applied constructor of a structure (Lean's try_eta_struct_core)
def kseta(+h: T.Ex, +n: U32, +mt: R.Tr<I.Meta>) -> Bool:
  +cm : I.Meta = R.get(I.Meta, 64n, mt, I.const_nm2(h), I.MNone{})
  (I.meta_is_ctor(cm) && U32.is_eq(n, (I.meta_p(cm) + I.meta_nf(cm) : U32))
   && I.meta_is_ind(R.get(I.Meta, 64n, mt, I.meta_ind(cm), I.MNone{})))

def krigid(+x: T.Ex, +hd: T.Ex) -> Bool:
  match x:
    case T.ESort{l}:
      True{}
    case T.EAll{n, t, b, bi}:
      True{}
    case T.EBVar{i}:
      True{}
    case T.ENat{d}:
      True{}
    case T.EStr{d}:
      True{}
    case T.EApp{f, a}:
      I.is_bvarx(hd)
    case _:
      False{}

# a bare (nullary) constructor counts only when its inductive is not a
# structure: a structure's nullary constructor is unit-like, and unit eta
# can equate it with anything of its type
def kctor_headed(+x: T.Ex, +hd: T.Ex, +mt: R.Tr<I.Meta>) -> Bool:
  match x:
    case T.EApp{f, a}:
      I.meta_is_ctor(R.get(I.Meta, 64n, mt, I.const_nm2(hd), I.MNone{}))
    case T.EConst{n, us}:
      +m2 : R.Tr<I.Meta> = mt
      +mi : I.Meta = R.get(I.Meta, 64n, m2, n, I.MNone{})
      +mi2 : I.Meta = mi
      I.meta_is_ctor(mi2)
      && Bool.not(I.meta_is_ind(R.get(I.Meta, 64n, m2, I.meta_ind(mi2),
                                      I.MNone{})))
    case _:
      False{}

# spine of a NODE already in hand (the index is not needed)
def kspine_head_tin(fs: Array<T.Ex> & U32, +node: T.Ex,
                    +ri: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fs:
    case Tuple{ex, nx}:
      kspine(256n, Nil{}, ri, nx, (ex, node))

# infer.bend's no_value: a constant with nothing to unfold and no
# reduction rule of its own
def kno_value(+x: T.Ex, +mt: R.Tr<I.Meta>, +vt: R.Tr<U32>,
              +qtt: R.Tr<U32>) -> Bool:
  match x:
    case T.EConst{n, us}:
      +n2 : U32 = n
      U32.is_eq(R.get(U32, 64n, vt, n2, 4294967295), 4294967295)
      && Bool.not(I.meta_is_rec(R.get(I.Meta, 64n, mt, n2, I.MNone{})))
      && Bool.not(U32.is_eq(n2, R.get(U32, 64n, qtt, 0, 4294967295)))
      && Bool.not(U32.is_eq(n2, R.get(U32, 64n, qtt, 1, 4294967295)))
      && Bool.not(U32.is_eq(n2, R.get(U32, 64n, qtt, 5, 4294967295)))
      && Bool.not(U32.is_eq(n2, R.get(U32, 64n, qtt, 6, 4294967295)))
      && Bool.not(U32.is_eq(n2, R.get(U32, 64n, qtt, 7, 4294967295)))
    case _:
      False{}

# infer.bend's never_sort, with the spine head supplied
def knever_sort(+x: T.Ex, +hd: T.Ex, +mt: R.Tr<I.Meta>, +vt: R.Tr<U32>,
                +qtt: R.Tr<U32>) -> Bool:
  match x:
    case T.EAll{n, t, b, bi}:
      True{}
    case T.ELam{n, t, b, bi}:
      True{}
    case T.ENat{d}:
      True{}
    case T.EStr{d}:
      True{}
    case T.EConst{n, us}:
      kno_value(T.EConst{n, us}, mt, vt, qtt)
    case T.EBVar{i}:
      True{}
    case T.EApp{f, a}:
      kno_value(hd, mt, vt, qtt) || I.is_bvarx(hd)
    case _:
      False{}

# `s.0 .. s.(i-1)` as fresh nodes (infer.bend's proj_nodes), answered as a
# spine message so the index list can ride back into a frame
def kprojn_go(+base: U32, n: Nat, +i: U32, +tn: U32, +sx: U32,
              acc: List<&2, U32>,
              r: (Array<T.Ex> & U32) & U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match n r:
    case 0n Tuple{fs, last}:
      ((fs, MSP{T.EBad{}, kdrop1(I.rev_u(Con{last, acc}, Nil{}))}), 0)
    case 1n+q Tuple{fs, last}:
      kprojn_go(base, q, (i + 1 : U32), tn, sx, Con{last, acc},
                khc(fs, T.EProj{tn, i, sx}, base))

def kprojn_tin(+base: U32, fs: Array<T.Ex> & U32, +idx: U32, +tn: U32,
               +sx: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  kprojn_go(base, U32.to_nat(idx), 0, tn, sx, Nil{}, (fs, 4294967295))

def knat_shape(+x: T.Ex) -> U32:
  match x:
    case T.ELam{n, t, b, bi}:
      1
    case T.ENat{d}:
      1
    case T.EStr{d}:
      1
    case T.EConst{n, us}:
      2
    case _:
      0

# head constant name, SENTINEL (not 0) when the node is not a constant --
# I.const_nm2 answers 0 for non-constants, which made two different bound-
# variable heads compare as "the same head"
def kcn(+x: T.Ex) -> U32:
  match x:
    case T.EConst{n, us}:
      n
    case _:
      4294967295

# a constant's universe-level indices (Nil for non-constants)
def kcus(+x: T.Ex) -> List<&2, U32>:
  match x:
    case T.EConst{n, us}:
      us
    case _:
      Nil{}

# list append, for the congruence worklist
# a spine head that delta or projection reduction could still rewrite
# a projection head is NOT counted: the pair reaches the App/App tail
# only after the full-projection whnf_core pass (DPr1-4: each structure
# whnf'd with delta), so a remaining `s.i` is stuck -- Lean's tail answers
# NO on it (`Std.Shrink a =?= a`: `idOpaque.1 a` against a stuck app)
def kunf(+h: T.Ex, +vt: R.Tr<U32>) -> Bool:
  +n : U32 = kcn(h)
  Bool.not(U32.is_eq(n, 4294967295))
  && Bool.not(U32.is_eq(R.get(U32, 64n, vt, n, 4294967295), 4294967295))

def kapp_u(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      ys
    case Con{head, tail}:
      Con{head, kapp_u(tail, ys)}

# the structure argument index of a projection node (sentinel if not EProj)
def kproj_s(+x: T.Ex) -> U32:
  match x:
    case T.EProj{tn, idx, s}:
      s
    case _:
      4294967295

# a transition that touches no store: pass the store through, message MN
def knoop(fs: Array<T.Ex> & U32,
          +ri: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  ((fs, MN{}), ri)

# --- the machine -------------------------------------------------------------
# Data-kinded context rides as plain parameters: the level trie (lnt, nlx),
# the recursor Meta table mt, the lparams table lp, the value table vt.
# Returns ((store & result) & levels).
# --- is_def_eq_offset support --------------------------------------------
# predecessor of a node: 4294967295 = neither zero nor a successor form,
# 4294967294 = zero (literal 0 or Nat.zero), otherwise the predecessor's
# index (a literal's predecessor is allocated at base)
def koff_fs(r: ((Array<T.Ex> & U32) & MG) & U32) -> (Array<T.Ex> & U32) & U32:
  match r:
    case Tuple{fm, i}:
      match fm:
        case Tuple{fs, mg}:
          (fs, i)

def koff_lit(+z: Bool, fs: Array<T.Ex> & U32, +d: List<&2, U32>,
             +base: U32) -> (Array<T.Ex> & U32) & U32:
  match z:
    case True{}:
      (fs, 4294967294)
    case False{}:
      koff_fs(kalloc(fs, T.ENat{I.dec_norm(I.dec_sub(d, [49]))}, base))

def koff_app2(pr: Array<T.Ex> & T.Ex, +nx: U32, +a: U32,
              +sn: U32) -> (Array<T.Ex> & U32) & U32:
  match pr:
    case Tuple{ex, fn}:
      match fn:
        case T.EConst{n, us}:
          ((ex, nx), S.pick(U32.is_eq(n, sn), a, 4294967295))
        case _:
          ((ex, nx), 4294967295)

def koff_app(fs: Array<T.Ex> & U32, +f: U32, +a: U32,
             +sn: U32) -> (Array<T.Ex> & U32) & U32:
  match fs:
    case Tuple{ex, nx}:
      koff_app2(Array.get(T.Ex, ex, f), nx, a, sn)

def koff_node(fs: Array<T.Ex> & U32, +node: T.Ex, +zn: U32, +sn: U32,
              +base: U32) -> (Array<T.Ex> & U32) & U32:
  match node:
    case T.ENat{d}:
      +d2 : List<&2, U32> = d
      koff_lit(I.dec_is_zero(d2), fs, d2, base)
    case T.EConst{n, us}:
      (fs, S.pick(U32.is_eq(n, zn), 4294967294, 4294967295))
    case T.EApp{f, a}:
      koff_app(fs, f, a, sn)
    case _:
      (fs, 4294967295)

# 0 = no offset form on at least one side; 1 = both zero; 2 = both succ
def koff_code(+px: U32, +py: U32) -> U32:
  +zx : Bool = U32.is_eq(px, 4294967294)
  +zy : Bool = U32.is_eq(py, 4294967294)
  +sx : Bool = U32.is_lt(px, 4294967294)
  +sy : Bool = U32.is_lt(py, 4294967294)
  S.pick(zx && zy, 1, S.pick(sx && sy, 2, 0))

def koff_fetch(r: (Array<T.Ex> & U32) & U32,
               +y: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match r:
    case Tuple{fs, px}:
      kfetch(fs, y, px)

def koff_noop(r: (Array<T.Ex> & U32) & U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match r:
    case Tuple{fs, py}:
      knoop(fs, py)

def km(fuel: Nat, +stk: KS, +lnt: R.Tr<L.LN>, +nlx: U32,
       +mt: R.Tr<I.Meta>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
       +qtt: R.Tr<U32>, +natn: U32, +wm: R.Tr<U32>, +nt: R.Tr<U32>,
       +hcb: U32, tin: ((Array<T.Ex> & U32) & MG) & U32)
    -> ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>):
  match fuel stk tin:
    case 0n _ Tuple{Tuple{fs, msg}, ri}:
      ((fs, 4294967295), ((lnt, nlx), wm))
    case 1n+p KNil{} Tuple{Tuple{fs, msg}, ri}:
      ((fs, ri), ((lnt, nlx), wm))
    case 1n+p KCon{KKp{e}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, e))
    # ---- lazy delta probe (see LZ0) ----
    # one probe budget per DECLARATION (store flag 0, steps used, not rolled
    # back): nested probes never restart their fuel, so
    # a probe that recurses through the full defeq stays bounded
    case 1n+p KCon{LZ0{x, y, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{LZ0u{x, y, fu, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm,
         nt, hcb, kfl_tin(fs, hcb, 0))
    case 1n+p KCon{LZ0u{x, y, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      +y2 : U32 = y
      +w2 : R.Tr<U32> = wm
      +used : U32 = ri
      # no failure cache at the loop's entry: a stall is not a failure (the
      # tail may still prove the pair), and Lean caches only is_def_eq_args
      # failures (LZF5)
      km(p, KCon{LZ0g{U32.is_ge(used, 1000000), x2, y2, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, w2, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{LZ0g{True{}, x, y, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TUnk{}))
    # the decisive entry: Lean's lazy_delta_reduction has no failure cache
    # at this level (only inside the args-first step), so a pair met again
    # runs the loop again; the per-declaration budget still applies
    case 1n+p KCon{LZ0d{x, y, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{LZ0du{x, y, fu, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm,
         nt, hcb, kfl_tin(fs, hcb, 0))
    case 1n+p KCon{LZ0du{x, y, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      +y2 : U32 = y
      +used : U32 = ri
      km(p, KCon{LZ0g{U32.is_ge(used, 1000000), x2, y2, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{LZ0g{False{}, x, y, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +x2 : U32 = x
      +y2 : U32 = y
      +f2 : U32 = fu
      km(p, KCon{LZ0b{U32.is_eq(f2, 0), U32.is_eq(x2, y2), x2, y2, f2, cx9},
                 KCon{LZC{klzkey(x2, y2), klzfp(x2, y2), x2, y2, cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{LZC{key, fp, x, y, ctx}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      +t2 : L.Tri = t
      km(p, KCon{LZC2{L.tri_is_yes(t2), key, fp, t2, x, y, ctx}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{LZC2{True{}, key, fp, t, x, y, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, t))
    # not settled: record the failure; the innermost iteration also leaves
    # its pair (the furthest-unfolded terms) in the register as a node
    # EApp{x, y}, from where a decisive caller (LD) continues eagerly
    case 1n+p KCon{LZC2{False{}, key, fp, t, x, y, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri_r(klzpair(U32.is_eq(r2, 0), fs, x, y, r2, hcb), t))
    # fuel out: the same node is still equal
    case 1n+p KCon{LZ0b{True{}, same, x, y, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.pick_tri(same, L.TYes{}, L.TUnk{})))
    case 1n+p KCon{LZ0b{False{}, True{}, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{LZ0b{False{}, False{}, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +x2 : U32 = x
      km(p, KCon{kwev(False{}, x2, Nil{}, 256, cx9), KCon{LZ1{y, fu, cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, x2, ri))
    case 1n+p KCon{LZ1{y, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +y2 : U32 = y
      +r2 : U32 = ri
      km(p, KCon{kwev(False{}, y2, Nil{}, 256, cx9), KCon{LZ2{r2, fu, cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, y2, r2))
    case 1n+p KCon{LZ2{x, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      +r2 : U32 = ri
      km(p, KCon{LZ3{U32.is_eq(x2, r2), x2, r2, fu, ctx}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, r2))
    case 1n+p KCon{LZ3{True{}, x, y, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{LZ3{False{}, x, y, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      km(p, KCon{LZOx{x2, y, fu, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm,
         nt, hcb, kfetch(fs, x2, 0))
    case 1n+p KCon{LZOx{x, y, fu, ctx}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +y2 : U32 = y
      +q2 : R.Tr<U32> = qtt
      +nd : T.Ex = node
      km(p, KCon{LZOy{x, y2, I.is_nat_lit(nd), I.nat_digits(nd), fu, ctx}, k},
         lnt, nlx, mt, lp, vt, q2, natn, wm, nt, hcb,
         koff_fetch(koff_node(fs, nd, R.get(U32, 64n, q2, 3, 4294967295),
                              R.get(U32, 64n, q2, 4, 4294967295), hcb), y2))
    case 1n+p KCon{LZOy{x, y, lx, dx, fu, ctx}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +q2 : R.Tr<U32> = qtt
      +nd : T.Ex = node
      +ly : Bool = I.is_nat_lit(nd)
      km(p, KCon{LZOy2{x, y, ri, lx && ly, ly && I.eq_u32s(dx, I.nat_digits(nd)),
                       fu, ctx}, k},
         lnt, nlx, mt, lp, vt, q2, natn, wm, nt, hcb,
         koff_noop(koff_node(fs, nd, R.get(U32, 64n, q2, 3, 4294967295),
                             R.get(U32, 64n, q2, 4, 4294967295), hcb)))
    case 1n+p KCon{LZOy2{x, y, px, both, eqd, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +px2 : U32 = px
      +py2 : U32 = ri
      km(p, KCon{LZOz{S.pick(both, S.pick(eqd, 1, 3), koff_code(px2, py2)),
                      x, y, px2, py2, fu, ctx}, k}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    # no offset form: the ordinary step (spines, then the delta choice)
    case 1n+p KCon{LZOz{0, x, y, px, py, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      km(p, KCon{LZ4{x2, y, fu, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm,
         nt, hcb, kspine_tin(fs, x2, 0))
    case 1n+p KCon{LZOz{1, x, y, px, py, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, L.TYes{}))
    # two different literals (both in whnf): NO, as Lean's quick_is_def_eq
    case 1n+p KCon{LZOz{3, x, y, px, py, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, L.TNo{}))
    case 1n+p KCon{LZOz{c, x, y, px, py, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +px2 : U32 = px
      +py2 : U32 = py
      km(p, KCon{DSub{False{}, U32.is_eq(px2, py2), px2, py2, ctx, 4096},
                 KCon{LZOr{}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    # the predecessors' verdict is the loop's verdict (Lean: to_lbool)
    case 1n+p KCon{LZOr{}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, t))
    case 1n+p KCon{LZ4{x, y, fu, ctx}, k} Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +y2 : U32 = y
      km(p, KCon{LZ5{x, y2, hd, sargs, fu, ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kspine_tin(fs, y2, ri))
    case 1n+p KCon{LZ5{x, y, hx, sx, fu, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +ha : T.Ex = hx
      +hb : T.Ex = hd
      +na : U32 = kcn(ha)
      +nb : U32 = kcn(hb)
      +sa : List<&2, U32> = sx
      +sb : List<&2, U32> = sargs
      +q2 : R.Tr<U32> = qtt
      +v2 : R.Tr<U32> = vt
      +cx : Bool = Bool.not(U32.is_eq(na, 4294967295))
                   && Bool.not(U32.is_eq(R.get(U32, 64n, v2, na, 4294967295),
                                         4294967295))
      +cy : Bool = Bool.not(U32.is_eq(nb, 4294967295))
                   && Bool.not(U32.is_eq(R.get(U32, 64n, v2, nb, 4294967295),
                                         4294967295))
      +hxh : U32 = khgt(q2, na)
      +hyh : U32 = khgt(q2, nb)
      # same head: the same constant at the same levels, or the same bound
      # variable (two nodes can spell one `#i`) -- then the arguments
      # pairwise, as Lean's is_def_eq_app after lazy delta stalls
      # Lean's lazy_delta_reduction_step tries the arguments first ONLY for
      # the same DEFINITION with regular hints on both sides (is_delta on
      # both, equal heights, is_eqp); constructor, recursor, axiom or
      # variable heads stall and the tail (is_def_eq_app, or the projected
      # fields under a projection) compares the arguments
      +samehd : Bool = Bool.not(U32.is_eq(na, 4294967295))
                       && U32.is_eq(na, nb) && cx && cy
                       && U32.is_eq(hxh, hyh) && U32.is_ne(hxh, 4294967294)
                       && I.eq_u32s(kcus(ha), kcus(hb))
                       && U32.is_eq(I.len_u(sa, 0), I.len_u(sb, 0))
      +opx : Bool = klitop(na, I.len_u(sa, 0), q2)
      +opy : Bool = klitop(nb, I.len_u(sb, 0), q2)
      +x2 : U32 = x
      +y2 : U32 = y
      +f2 : U32 = fu
      # Lean's lazy_delta_reduction_step: a side headed by a projection is
      # reduced (its structure whnf'd in full) only when the OTHER side is
      # a definition that could be unfolded instead (try_unfold_proj_app);
      # two projection sides stall, and the tail decides (proj/proj
      # structures by lazy delta, then the full-projection whnf_core pass)
      +px : Bool = kis_proj(ha) && cy && Bool.not(cx)
      +py : Bool = kis_proj(hb) && cx && Bool.not(cy)
      km(p, KCon{LZPj{px || py, px,
                      LZR0{opx || opy, opx, opy,
                           I.nth_u(sa, 0, 4294967295), I.nth_u(sa, 1, 4294967295),
                           I.nth_u(sb, 0, 4294967295), I.nth_u(sb, 1, 4294967295),
                           LZ6{samehd, sa, sb,
                               cx && (Bool.not(cy) || U32.is_ge(hxh, hyh)),
                               cy && (Bool.not(cx) || U32.is_ge(hyh, hxh)),
                               x2, y2, f2, cx9}, x2, y2, f2, cx9}, x2, y2, f2, cx9}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{LZPj{False{}, px, nxt, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{nxt, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         knoop(fs, ri))
    case 1n+p KCon{LZPj{True{}, True{}, nxt, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      km(p, KCon{LZQ1{True{}, x2, y, fu, nxt, ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kspine_tin(fs, x2, ri))
    case 1n+p KCon{LZPj{True{}, False{}, nxt, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +y2 : U32 = y
      km(p, KCon{LZQ1{False{}, x, y2, fu, nxt, ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kspine_tin(fs, y2, ri))
    case 1n+p KCon{LZR0{False{}, opx, opy, ax1, ax2, ay1, ay2, nxt, x, y, fu, ctx},
                   k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{nxt, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         knoop(fs, ri))
    # Lean's reduce_bin_nat_op: the two ARGUMENTS are whnf'd and the
    # operation is computed only when both are literals -- never a full
    # whnf of the operation itself (`a - 2^64` with `a` a variable
    # descended through the literal by unary recursion until fuel ran out)
    case 1n+p KCon{LZR0{True{}, opx, opy, ax1, ax2, ay1, ay2, nxt, x, y,
                        fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      +y2 : U32 = y
      km(p, KCon{LZR0z{opx, opy, ax1, ax2, ay1, ay2, nxt, x2, y2, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kclosed(fs, x2, y2, hcb))
    case 1n+p KCon{LZR0z{opx, opy, ax1, ax2, ay1, ay2, nxt, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{LZR0y{U32.is_eq(ri, 1), opx, opy, ax1, ax2, ay1, ay2, nxt,
                       x, y, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{LZR0y{True{}, opx, opy, ax1, ax2, ay1, ay2, nxt, x, y, fu,
                         ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{LZR0c{opx, opy, ax1, ax2, ay1, ay2, nxt, x, y, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{LZR0y{False{}, opx, opy, ax1, ax2, ay1, ay2, nxt, x, y, fu,
                         ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{nxt, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         knoop(fs, ri))
    case 1n+p KCon{LZR0c{True{}, opy, ax1, ax2, ay1, ay2, nxt, x, y,
                         fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      km(p, KCon{KLit2{ax1, ax2, cx9}, KCon{LZRg{opy, ay1, ay2, nxt, x, y, fu, cx9},
                                       k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{LZR0c{False{}, opy, ax1, ax2, ay1, ay2, nxt, x, y,
                         fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      km(p, KCon{LZR1{opy, ay1, ay2, nxt, x2, y, fu, ctx}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, x2))
    case 1n+p KCon{LZRg{opy, ay1, ay2, nxt, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{LZRg2{L.tri_is_yes(t), opy, ay1, ay2, nxt, x, y, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{LZRg2{True{}, opy, ay1, ay2, nxt, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +x2 : U32 = x
      km(p, KCon{DWhd{x2, cx9}, KCon{LZR1{opy, ay1, ay2, nxt, x2, y, fu, cx9}, k}}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{LZRg2{False{}, opy, ay1, ay2, nxt, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      km(p, KCon{LZR1{opy, ay1, ay2, nxt, x2, y, fu, ctx}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, x2))
    case 1n+p KCon{LZR1{True{}, ay1, ay2, nxt, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +wx : U32 = ri
      km(p, KCon{KLit2{ay1, ay2, cx9}, KCon{LZRh{wx, nxt, x, y, fu, cx9}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, wx))
    case 1n+p KCon{LZR1{False{}, ay1, ay2, nxt, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +y2 : U32 = y
      +wx : U32 = ri
      km(p, KCon{LZR2{wx, nxt, x, y2, fu, ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, y2))
    case 1n+p KCon{LZRh{wx, nxt, x, y, fu, ctx}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{LZRh2{L.tri_is_yes(t), wx, nxt, x, y, fu, ctx}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{LZRh2{True{}, wx, nxt, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +y2 : U32 = y
      km(p, KCon{DWhd{y2, cx9}, KCon{LZR2{wx, nxt, x, y2, fu, cx9}, k}}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{LZRh2{False{}, wx, nxt, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +y2 : U32 = y
      km(p, KCon{LZR2{wx, nxt, x, y2, fu, cx9}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, y2))
    # KLit2{a, b, cx9}: YES iff whnf(a) and whnf(b) are both Nat literals
    case 1n+p KCon{KLit2{a, b, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +a2 : U32 = a
      km(p, KCon{DWhd{a2, cx9}, KCon{KLit2b{b, cx9}, k}}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{KLit2b{b, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +wa : U32 = ri
      km(p, KCon{KLit2c{b, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kfetch(fs, wa, 0))
    case 1n+p KCon{KLit2c{b, ctx}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +b2 : U32 = b
      km(p, KCon{DWhd{b2, cx9}, KCon{KLit2d{node, cx9}, k}}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{KLit2d{na, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +wb : U32 = ri
      km(p, KCon{KLit2e{na, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kfetch(fs, wb, 0))
    case 1n+p KCon{KLit2e{na, ctx}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.tri_of(I.is_nat_lit(na) && I.is_nat_lit(node))))
    case 1n+p KCon{LZR2{wx, nxt, x, y, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +wy : U32 = ri
      +wx2 : U32 = wx
      km(p, KCon{LZR3{(U32.is_eq(wx2, x) && U32.is_eq(wy, y))
                      || U32.is_eq(fu, 0), wx2, wy, nxt, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, wy))
    case 1n+p KCon{LZR3{True{}, wx, wy, nxt, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{nxt, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         knoop(fs, ri))
    case 1n+p KCon{LZR3{False{}, wx, wy, nxt, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{LZ0{wx, wy, (fu - 1 : U32), ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{LZ6{True{}, sx, sy, ux, uy, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{LZA{sx, sy, ux, uy, x, y, fu, ctx}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{LZ6{False{}, sx, sy, ux, uy, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{LZU{ux, uy, x, y, fu, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, knoop(fs, ri))
    # same head: the arguments pairwise, each a smaller probe
    case 1n+p KCon{LZA{Nil{}, Nil{}, ux, uy, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    # Lean's is_def_eq_args: each pair by the full defeq (DSub runs the
    # lazy loop itself now), guarded by the failure cache
    case 1n+p KCon{LZA{Con{a, at}, Con{b, bt}, ux, uy, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +f2 : U32 = fu
      +a2 : U32 = a
      +b2 : U32 = b
      km(p, KCon{LZF2u{a2, b2, cx9}, KCon{LZA3{at, bt, ux, uy, x, y, f2, cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfl_tin(fs, hcb, 0))
    case 1n+p KCon{LZA{xs, ys, ux, uy, x, y, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{LZU{ux, uy, x, y, fu, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{LZF{a, b, ctx}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{LZF2{L.tri_is_yes(t), a, b, ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{LZF2{True{}, a, b, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{LZF2{False{}, a, b, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{LZF2u{a, b, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt,
         hcb, kfl_tin(fs, hcb, 0))
    case 1n+p KCon{LZF2u{a, b, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +used : U32 = ri
      +a2 : U32 = a
      +b2 : U32 = b
      +w2 : R.Tr<U32> = wm
      +seen : Bool = U32.is_eq(R.get(U32, 64n, w2, klzkey(b2, a2), 4294967295),
                               klzfp(b2, a2))
                     || U32.is_ge(used, 1000000)
      km(p, KCon{LZF6{seen, a2, b2, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn, w2,
         nt, hcb, knoop(fs, 0))
    case 1n+p KCon{LZF6{True{}, a, b, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TUnk{}))
    case 1n+p KCon{LZF6{False{}, a, b, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +a2 : U32 = a
      +b2 : U32 = b
      km(p, KCon{DSub{False{}, U32.is_eq(a2, b2), a2, b2, cx9, 4096},
                 KCon{LZF5{a2, b2, cx9}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{LZF3{b, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +b2 : U32 = b
      +wa : U32 = ri
      km(p, KCon{kwev(False{}, b2, Nil{}, 256, cx9), KCon{LZF4{wa, cx9}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, b2, wa))
    case 1n+p KCon{LZF4{wa, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +wb : U32 = ri
      +wa2 : U32 = wa
      km(p, KCon{DSub{False{}, U32.is_eq(wa2, wb), wa2, wb, ctx, 4096}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{LZF5{a, b, ctx}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      +t2 : L.Tri = t
      +a2 : U32 = a
      +b2 : U32 = b
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn,
         R.set_if(U32, Bool.not(L.tri_is_yes(t2)), wm, klzkey(b2, a2),
                  klzfp(b2, a2), 4294967295),
         nt, hcb, kmtri(fs, t2))
    case 1n+p KCon{LZA3{xs, ys, ux, uy, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{LZA2{L.tri_is_yes(t), xs, ys, ux, uy, x, y, fu, ctx}, k}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{LZA2{True{}, xs, ys, ux, uy, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{LZA{xs, ys, ux, uy, x, y, fu, ctx}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # an argument did not settle: unfold (both, on a tie) as Lean does
    case 1n+p KCon{LZA2{False{}, xs, ys, ux, uy, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{LZU{ux, uy, x, y, fu, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, knoop(fs, ri))
    # unfold step
    case 1n+p KCon{LZU{False{}, False{}, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TUnk{}))
    case 1n+p KCon{LZQ1{True{}, x, y, fu, nxt, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      match hd:
        case T.EProj{tn, i, sx}:
          +s2 : U32 = sx
          km(p, KCon{DWhd{s2, ctx}, KCon{LZQ2{True{}, tn, i, s2, sargs, y, fu,
                                         nxt, ctx}, k}},
             lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
        case _:
          km(p, KCon{nxt, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
             knoop(fs, ri))
    case 1n+p KCon{LZQ1{False{}, x, y, fu, nxt, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      match hd:
        case T.EProj{tn, i, sx}:
          +s2 : U32 = sx
          km(p, KCon{DWhd{s2, ctx}, KCon{LZQ2{False{}, tn, i, s2, sargs, x, fu,
                                         nxt, ctx}, k}},
             lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
        case _:
          km(p, KCon{nxt, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
             knoop(fs, ri))
    case 1n+p KCon{LZQ2{left, tn, i, s, sargs, other, fu, nxt, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      +s2 : U32 = s
      km(p, KCon{LZQ3{U32.is_eq(r2, s2) || U32.is_eq(fu, 0), left, tn, i,
                      r2, sargs, other, fu, nxt, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, r2))
    # the structure did not reduce: carry on with the unfold decision
    case 1n+p KCon{LZQ3{True{}, left, tn, i, s, sargs, other, fu, nxt, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{nxt, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         knoop(fs, ri))
    case 1n+p KCon{LZQ3{False{}, left, tn, i, s, sargs, other, fu, nxt, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{LZQ4{left, other, fu, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, klzpj(hcb, sargs, khc(fs, T.EProj{tn, i, s}, hcb)))
    case 1n+p KCon{LZQ4{True{}, other, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{LZ0{r2, other, (fu - 1 : U32), ctx}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, knoop(fs, r2))
    case 1n+p KCon{LZQ4{False{}, other, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{LZ0{other, r2, (fu - 1 : U32), ctx}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, knoop(fs, r2))
    case 1n+p KCon{LZU{True{}, uy, x, y, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +x2 : U32 = x
      km(p, KCon{LZUn{x2, cx9}, KCon{LZU2{uy, y, fu, cx9}, k}}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kspine_tin(fs, x2, ri))
    case 1n+p KCon{LZU{False{}, True{}, x, y, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{LZU2{True{}, y, fu, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, kkeep(fs, x))
    case 1n+p KCon{LZU2{True{}, y, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +y2 : U32 = y
      +r2 : U32 = ri
      km(p, KCon{LZUn{y2, cx9}, KCon{LZU3{r2, fu, cx9}, k}}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kspine_tin(fs, y2, r2))
    case 1n+p KCon{LZU2{False{}, y, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{LZ0{r2, y, (fu - 1 : U32), ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, r2))
    case 1n+p KCon{LZU3{x, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{LZ0{x, r2, (fu - 1 : U32), ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, r2))
    # one delta step of a constant-headed spine, then whnf_core
    # the per-declaration budget counts UNFOLD steps (Lean bounds nothing;
    # the budget exists for runaway delta chains), never defeq entries: the
    # structural traversal of a huge constructor term (grind-ring-5's
    # polynomials, 2 real unfolds) must not exhaust it
    case 1n+p KCon{LZUn{x, ctx}, k} Tuple{Tuple{fs, MSP{T.EConst{n, us}, sargs}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +n2 : U32 = n
      +u2 : List<&2, U32> = us
      km(p, KCon{LZUn1{WDelGo{True{}, False{},
                              R.get(U32, 64n, vt, n2, 4294967295),
                              R.get(List<&2, U32>, 64n, lp, n2, Nil{}),
                              klns_of(u2, lnt), x, sargs, 256, cx9}, cx9}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfl_tin(fs, hcb, 0))
    case 1n+p KCon{LZUn1{go, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +used : U32 = ri
      km(p, KCon{go, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         knoop(kfl_set(fs, hcb, 0, (used + 1 : U32)), 0))
    case 1n+p KCon{LZUn{x, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, x))
    # ---- hooks ----
    case 1n+p KCon{DAqLz{a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{DAqLz2{L.tri_is_yes(t), a1, a2, xi, yi, ctx, fu}, k}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DAqLz2{True{}, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{DAqLz2{False{}, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      km(p, KCon{DWhd{a1, cx9}, KCon{DAq4{L.TYes{}, a1, a2, xi, yi, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DCgLz{xt, yt, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{DCgLz2{L.tri_is_yes(t), xt, yt, a1, a2, xi, yi, ctx, fu},
                 k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         knoop(fs, ri))
    case 1n+p KCon{DCgLz2{True{}, xt, yt, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DCgL{xt, yt, a1, a2, xi, yi, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DCgLz2{False{}, xt, yt, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      km(p, KCon{DWhd{a1, cx9}, KCon{DAq4{L.TYes{}, a1, a2, xi, yi, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ---- eval: lift ----
    case 1n+p KCon{KEvL{c, d, e, fu}, k} Tuple{Tuple{fs, MKeep{}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, e))
    case 1n+p KCon{KEvL{c, d, e, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      match node:
        case T.EBVar{i}:
          km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kbv_lift(fs, i, e, c, d, hcb))
        case T.EApp{f, a}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +f2 : U32 = f
          km(p, KCon{kev(w, f2), KCon{KAp2{w, e, f2, a}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, f2, ri, w, hcb))
        case T.ELam{n, t, b, bi}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLm2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, t2, ri, w, hcb))
        case T.EAll{n, t, b, bi}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KAl2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, t2, ri, w, hcb))
        case T.ELet{n, t, v, b}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLt2{w, e, n, t2, v, b}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, t2, ri, w, hcb))
        case T.EProj{tn, i, s}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +s2 : U32 = s
          km(p, KCon{kev(w, s2), KCon{KPj2{e, tn, i, s2}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, s2, ri, w, hcb))
        case _:
          km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, e))
    # ---- eval: inst ----
    case 1n+p KCon{KEvI{c, v, e, fu}, k} Tuple{Tuple{fs, MKeep{}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, e))
    case 1n+p KCon{KEvI{c, v, e, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      match node:
        case T.EBVar{i}:
          +c2 : U32 = c
          +i2 : U32 = i
          +v2 : U32 = v
          +iseq : Bool = U32.is_eq(i2, c2)
          +tgt : U32 = S.pick(iseq, v2, 4294967295)
          km(p, KCon{kev(WP{0, 0, c2, 0, Nil{}, Nil{}, 2000000}, tgt),
                     KCon{KBvI{iseq, U32.is_gt(i2, c2), i2, e}, k}},
             lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, tgt, ri))
        case T.EApp{f, a}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +f2 : U32 = f
          km(p, KCon{kev(w, f2), KCon{KAp2{w, e, f2, a}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, f2, ri, w, hcb))
        case T.ELam{n, t, b, bi}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLm2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, t2, ri, w, hcb))
        case T.EAll{n, t, b, bi}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KAl2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, t2, ri, w, hcb))
        case T.ELet{n, t, vv, b}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLt2{w, e, n, t2, vv, b}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, t2, ri, w, hcb))
        case T.EProj{tn, i, s}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +s2 : U32 = s
          km(p, KCon{kev(w, s2), KCon{KPj2{e, tn, i, s2}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, s2, ri, w, hcb))
        case _:
          km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, e))
    # ---- eval: instantiate several (op 3) ----
    case 1n+p KCon{KEvM{c, vs, e, fu}, k} Tuple{Tuple{fs, MKeep{}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, e))
    case 1n+p KCon{KEvM{c, vs, e, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      match node:
        case T.EBVar{i}:
          +c2 : U32 = c
          +i2 : U32 = i
          +v2 : List<&2, U32> = vs
          +m : U32 = I.len_u(v2, 0)
          +inr : Bool = U32.is_ge(i2, c2) && U32.is_lt((i2 - c2 : U32), m)
          +tgt : U32 = S.pick(inr, I.nth_u(v2, (i2 - c2 : U32), 4294967295),
                              4294967295)
          km(p, KCon{kev(WP{0, 0, c2, 0, Nil{}, Nil{}, 2000000}, tgt),
                     KCon{KBvM{inr, U32.is_ge(i2, (c2 + m : U32)), i2, m, e},
                          k}},
             lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, tgt, ri))
        case T.EApp{f, a}:
          +w : WP = WP{3, c, 0, 0, vs, Nil{}, (fu - 1 : U32)}
          +f2 : U32 = f
          km(p, KCon{kev(w, f2), KCon{KAp2{w, e, f2, a}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, f2, ri, w, hcb))
        case T.ELam{n, t, b, bi}:
          +w : WP = WP{3, c, 0, 0, vs, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLm2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, t2, ri, w, hcb))
        case T.EAll{n, t, b, bi}:
          +w : WP = WP{3, c, 0, 0, vs, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KAl2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, t2, ri, w, hcb))
        case T.ELet{n, t, vv, b}:
          +w : WP = WP{3, c, 0, 0, vs, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLt2{w, e, n, t2, vv, b}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, t2, ri, w, hcb))
        case T.EProj{tn, i, s}:
          +w : WP = WP{3, c, 0, 0, vs, Nil{}, (fu - 1 : U32)}
          +s2 : U32 = s
          km(p, KCon{kev(w, s2), KCon{KPj2{e, tn, i, s2}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, s2, ri, w, hcb))
        case _:
          km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, e))
    case 1n+p KCon{KBvM{inr, isgt, i, m, e}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kbv_finm(inr, isgt, fs, ri, i, m, e, hcb))
    # ---- eval: lsubst ----
    case 1n+p KCon{KEvS{ps, qs, e, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      match node:
        case T.ESort{l}:
          +old : L.LN = R.get(L.LN, 64n, lnt, l, L.LNun{})
          +u : L.LN = L.ln_subst(old, ps, qs)
          +same : Bool = L.tri_is_yes(L.ln_cmp(old, u))
          +nl : U32 = nlx
          +i : U32 = klv_find(lnt, nl, u)
          +fresh : Bool = Bool.not(same) && U32.is_eq(i, nl)
          km(p, k,
             kpick_lta(same, lnt, nl, i, u),
             S.pick(fresh, (nl + 1 : U32), nl), mt, lp, vt, qtt, natn, wm, nt,
             hcb, ksort3(same, fs, i, e, hcb))
        case T.EConst{n, us}:
          +r : LVS = klsub_lvls(us, lnt, nlx, ps, qs)
          km(p, k, lvs_t(r), lvs_nx(r), mt, lp, vt, qtt, natn, wm, nt, hcb,
             ksconst(fs, n, lvs_xs(r), hcb))
        case T.EApp{f, a}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +f2 : U32 = f
          km(p, KCon{kev(w, f2), KCon{KAp2{w, e, f2, a}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, f2, ri, w, hcb))
        case T.ELam{n, t, b, bi}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLm2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, t2, ri, w, hcb))
        case T.EAll{n, t, b, bi}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KAl2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, t2, ri, w, hcb))
        case T.ELet{n, t, v, b}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLt2{w, e, n, t2, v, b}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, t2, ri, w, hcb))
        case T.EProj{tn, i, s}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +s2 : U32 = s
          km(p, KCon{kev(w, s2), KCon{KPj2{e, tn, i, s2}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, s2, ri, w, hcb))
        case _:
          km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, e))
    # ---- whnf: rebuild on exhausted fuel ----
    # whnf fuel ran out: the rebuilt term is only PARTIALLY reduced. It is
    # still definitionally equal to the input (so YES answers built on it are
    # sound) but it is not a normal form, so a NO built on it is not. Flag the
    # declaration INCOMPLETE (store flag 3): fcheck turns a reject into
    # a decline. This is what made magma-list-deep-n21 reject a true theorem.
    case 1n+p KCon{WRbP{e, args, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         krebuild(hcb, args, fs, e))
    case 1n+p KCon{WRb{e, args, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         krebuild(hcb, args, kfl_set(fs, hcb, 3, 1), e))
    case 1n+p KCon{KKpF{e}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kkeep(kfl_set(fs, hcb, 2, 1), e))
    # ---- whnf: eval (entry-level node dispatch; first match wins) ----
    case 1n+p KCon{WEv{delta, e, args, fu, ctx}, k}
         Tuple{Tuple{fs, MX{T.EApp{f, a}}}, ri}:
      +f2 : U32 = f
      km(p, KCon{kwev(delta, f2, Con{a, args}, (fu - 1 : U32), ctx), k}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, f2, ri))
    # beta: take every leading lambda an argument is there for, then ONE
    # instantiation of the body (Lean's whnf_core app case)
    case 1n+p KCon{WEv{delta, e, Con{a, rest}, fu, ctx}, k}
         Tuple{Tuple{fs, MX{T.ELam{n, t, b, bi}}}, ri}:
      +b2 : U32 = b
      km(p, KCon{WBt{[a], rest, delta, fu, b2, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, b2, ri))
    case 1n+p KCon{WBt{taken, Con{a, rest}, delta, fu, cur, ctx}, k}
         Tuple{Tuple{fs, MX{T.ELam{n, t, b, bi}}}, ri}:
      +b2 : U32 = b
      km(p, KCon{WBt{Con{a, taken}, rest, delta, fu, b2, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, b2, ri))
    case 1n+p KCon{WBt{taken, rest, delta, fu, cur, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = cur
      km(p, KCon{kev(WP{3, 0, 0, 0, taken, Nil{}, 2000000}, r2),
                 KCon{WCont{delta, rest, (fu - 1 : U32), ctx}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, r2))
    case 1n+p KCon{WEv{delta, e, args, fu, ctx}, k}
         Tuple{Tuple{fs, MX{T.ELet{n, t, v, b}}}, ri}:
      +b2 : U32 = b
      km(p, KCon{kev(WP{1, 0, 0, v, Nil{}, Nil{}, 2000000}, b2),
                 KCon{WCont{delta, args, (fu - 1 : U32), ctx}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, b2, ri))
    case 1n+p KCon{WEv{delta, e, args, fu, ctx}, k}
         Tuple{Tuple{fs, MX{T.EConst{n, us}}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +n2 : U32 = n
      +a2 : List<&2, U32> = args
      +vi : U32 = R.get(U32, 64n, vt, n2, 4294967295)
      +d2 : Bool = delta
      +can : Bool = Bool.and(d2, U32.is_ne(vi, 4294967295))
      +mi : I.Meta = R.get(I.Meta, 64n, mt, n2, I.MNone{})
      +pp : U32 = I.meta_p(mi)
      +mn : U32 = I.meta_n(mi)
      +mk : U32 = I.meta_k(mi)
      +la : U32 = I.len_u(a2, 0)
      +iskr : Bool = U32.is_eq(I.meta_kf(mi), 1)
                     && U32.is_gt(la, (pp + 1 + mn + mk : U32))
      +uind : I.Meta = R.get(I.Meta, 64n, mt, I.meta_ind(mi), I.MNone{})
      +isue : Bool = I.meta_is_rec(mi) && I.meta_is_ind(uind)
                     && U32.is_eq(I.meta_nf(uind), 0)
                     && U32.is_eq(mk, 0)
                     && U32.is_gt(la, (pp + 1 + mn : U32))
      +need : U32 = (pp + 1 + mn + mk : U32)
      +u2 : List<&2, U32> = us
      +mi2 : I.Meta = mi
      +rrj : U32 = I.meta_rr_major(mi2)
      +isrr : Bool = I.meta_is_recr(mi2) && U32.is_gt(la, rrj)
      km(p, KCon{pick_kf(isrr,
                         RI0{d2, e, a2, fu, rrj, I.meta_rr_pre(mi2),
                             I.meta_rr_rules(mi2),
                             R.get(List<&2, U32>, 64n, lp, n2, Nil{}),
                             klns_of(u2, lnt), cx9},
                         WPh1{iskr, isue, can, d2, vi,
                              R.get(List<&2, U32>, 64n, lp, n2, Nil{}),
                              klns_of(u2, lnt), e, a2, fu, pp, mn, mk,
                              I.meta_rcty(mi2), n2,
                              P5{I.meta_is_rec(mi2) && U32.is_gt(la, need),
                                 need, I.meta_ind(mi2), pp, mk, n2, u2}, cx9}),
                 k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WEv{delta, e, args, fu, ctx}, k}
         Tuple{Tuple{fs, MX{T.EProj{tn, idx, sx}}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +s2 : U32 = sx
      +f2 : U32 = (fu - 1 : U32)
      km(p, KCon{kwev(delta, s2, Nil{}, f2, cx9),
                 KCon{WPrj{delta, e, tn, idx, args, f2, cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, s2, ri))
    case 1n+p KCon{WEv{delta, e, args, fu, ctx}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, krebuild(hcb, args, fs, e))
    # ---- rule-based iota (RI0) ----
    case 1n+p KCon{RI0{delta, e, args, fu, mj, pre, rules, ps, qs, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +a2 : List<&2, U32> = args
      +m2 : U32 = mj
      +maj : U32 = I.nth_u(a2, m2, 4294967295)
      km(p, KCon{pick_kf(delta, kwev(True{}, maj, Nil{}, (fu - 1 : U32), cx9),
                         DWhd{maj, cx9}),
                 KCon{RI1{delta, e, a2, fu, m2, pre, rules, ps, qs, cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, maj, ri))
    case 1n+p KCon{RI1{delta, e, args, fu, mj, pre, rules, ps, qs, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{RI2{delta, e, args, fu, mj, pre, rules, ps, qs, ctx}, k}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, r2, r2))
    case 1n+p KCon{RI2{delta, e, args, fu, mj, pre, rules, ps, qs, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +c : U32 = kcn(hd)
      +rs : List<&2, U32> = rules
      +nf : U32 = krule_nf(rs, c)
      +rhs : U32 = krule_rhs(rs, c)
      +s2 : List<&2, U32> = sargs
      +hit : Bool = Bool.not(U32.is_eq(rhs, 4294967295))
                    && U32.is_ge(I.len_u(s2, 0), nf)
      km(p, KCon{RI3{hit, rhs, delta, e,
                     kri_args(args, pre, mj, s2, S.pick(hit, nf, 0)), fu, ps,
                     qs, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{RI3{True{}, rhs, delta, e, args, fu, ps, qs, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WDelGo{True{}, delta, rhs, ps, qs, e, args, fu, ctx}, k}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # no rule for the major's head: stuck (the original application)
    case 1n+p KCon{RI3{False{}, rhs, delta, e, args, fu, ps, qs, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         krebuild(hcb, args, fs, e))
    # ---- whnf: continue on a substitution result ----
    case 1n+p KCon{WCont{delta, args, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{kwev(delta, r2, args, fu, ctx), k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kfetch(fs, r2, 0))
    # ---- EConst pipeline: phase 1, K-like reduction ----
    case 1n+p KCon{WPh1{True{}, isue, can, delta, vi, ps, qs, e, args, fu,
                        pp, mn, mk, rcty, cn, p5, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +p2 : U32 = pp
      +r2 : U32 = rcty
      +a2 : List<&2, U32> = args
      km(p, KCon{WPlE{r2, I.take_u(a2, p2, Nil{}), cx9},
                 KCon{WK2{isue, can, delta, vi, ps, qs, e, a2, fu, p2, mn,
                          mk, cn, p5, cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, ri))
    case 1n+p KCon{WPh1{False{}, isue, can, delta, vi, ps, qs, e, args, fu,
                        pp, mn, mk, rcty, cn, p5, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WPh2{isue, can, delta, vi, ps, qs, e, args, fu, pp, mn,
                      cn, p5, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ---- telescope peel (ordered: the Pi case must precede the stuck one)
    case 1n+p KCon{WPlE{tyi, Nil{}, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, tyi))
    case 1n+p KCon{WPlE{tyi, Con{v, rest}, ctx}, k}
         Tuple{Tuple{fs, MX{T.EAll{n, t, b, bi}}}, ri}:
      +b2 : U32 = b
      km(p, KCon{WPlB{[v], rest, b2, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, b2, ri))
    case 1n+p KCon{WPlB{taken, Con{v, rest}, cur, ctx}, k}
         Tuple{Tuple{fs, MX{T.EAll{n, t, b, bi}}}, ri}:
      +b2 : U32 = b
      km(p, KCon{WPlB{Con{v, taken}, rest, b2, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, b2, ri))
    case 1n+p KCon{WPlB{taken, rest, cur, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +c2 : U32 = cur
      km(p, KCon{kev(WP{3, 0, 0, 0, taken, Nil{}, 2000000}, c2),
                 KCon{WPlC{rest, ctx}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, c2, ri))
    case 1n+p KCon{WPlE{tyi, Con{v, rest}, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, 4294967295))
    case 1n+p KCon{WPlC{vals, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WPlE{r2, vals, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kfetch(fs, r2, 0))
    # ---- K: peel done -> spine of the peeled type ----
    case 1n+p KCon{WK2{isue, can, delta, vi, ps, qs, e, args, fu, pp, mn,
                       mk, cn, p5, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WK3{U32.is_ne(r2, 4294967295), isue, can, delta, vi, ps,
                     qs, e, args, fu, pp, mn, mk, cn, p5, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kspine_tin(fs, S.pick(U32.is_ne(r2, 4294967295), r2, 0), 0))
    # ---- K: spine done -> compare expected and given indices ----
    case 1n+p KCon{WK3{pok, isue, can, delta, vi, ps, qs, e, args, fu, pp,
                       mn, mk, cn, p5, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +a2 : List<&2, U32> = args
      +p2 : U32 = pp
      +m2 : U32 = mn
      +k2 : U32 = mk
      +xs : List<&2, U32> = I.skip_u(sargs, p2)
      +ys : List<&2, U32> = I.take_u(I.skip_u(a2, (p2 + 1 + m2 : U32)), k2,
                                     Nil{})
      km(p, KCon{WK4{pok, isue, can, delta, vi, ps, qs, e, a2, fu, p2, m2,
                     k2, cn, p5, xs, ys, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         keq_lists_tin(fs, xs, ys, lnt))
    # ---- K: verdict arrived ----
    case 1n+p KCon{WK4{pok, isue, can, delta, vi, ps, qs, e, args, fu, pp,
                       mn, mk, cn, p5, xs, ys, ctx}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      +t2 : L.Tri = t
      +pk : Bool = pok
      km(p, KCon{WK4b{pk && Bool.not(L.tri_is_yes(t2)), t2, pk, isue, can,
                      delta, vi, ps, qs, e, args, fu, pp, mn, mk, cn, p5, xs,
                      ys, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WK4b{False{}, t, pok, isue, can, delta, vi, ps, qs, e,
                        args, fu, pp, mn, mk, cn, p5, xs, ys, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WKGo{Bool.and(pok, L.tri_is_yes(t)), isue, can, delta, vi,
                      ps, qs, e, args, fu, pp, mn, mk, cn, p5, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # the indices are not syntactically equal: Lean's to_cnstr_when_K checks
    # the major's type against the constructor's by is_def_eq, so compare
    # each index pair by defeq (`motive (castSucc i)` vs `motive ⟨i, h⟩`)
    case 1n+p KCon{WK4b{True{}, t, pok, isue, can, delta, vi, ps, qs, e,
                        args, fu, pp, mn, mk, cn, p5, xs, ys, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      km(p, KCon{DLs{xs, ys, cx9}, KCon{WK5{pok, isue, can, delta, vi, ps, qs, e,
                                       args, fu, pp, mn, mk, cn, p5, cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WK5{pok, isue, can, delta, vi, ps, qs, e, args, fu, pp,
                       mn, mk, cn, p5, ctx}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{WKGo{Bool.and(pok, L.tri_is_yes(t)), isue, can, delta, vi,
                      ps, qs, e, args, fu, pp, mn, mk, cn, p5, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ---- defeq of two lists, pairwise (whnf each side first) ----
    case 1n+p KCon{DLs{Nil{}, Nil{}, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    # (Lean: is_def_eq(e_type, expected_type) under the recursor's binder
    # context; each index pair goes through the full defeq entry, which
    # does its own whnf_core / lazy delta, so no eager whnf here)
    case 1n+p KCon{DLs{Con{x, xt}, Con{y, yt}, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +x2 : U32 = x
      +y2 : U32 = y
      km(p, KCon{DSub{False{}, U32.is_eq(x2, y2), x2, y2, cx9, 4096},
                 KCon{DLs3{xt, yt, cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DLs{xs, ys, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TUnk{}))
    case 1n+p KCon{DLs1{y, xt, yt, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +wx : U32 = ri
      km(p, KCon{DWhd{y, cx9}, KCon{DLs2{wx, xt, yt, cx9}, k}}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DLs2{wx, xt, yt, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +wy : U32 = ri
      +wx2 : U32 = wx
      km(p, KCon{DSub{False{}, U32.is_eq(wx2, wy), wx2, wy, ctx, 4096},
                 KCon{DLs3{xt, yt, ctx}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DLs3{xt, yt, ctx}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      +t2 : L.Tri = t
      km(p, KCon{DLs4{L.tri_is_yes(t2), t2, xt, yt, ctx}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DLs4{True{}, t, xt, yt, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DLs{xt, yt, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt,
         hcb, knoop(fs, ri))
    case 1n+p KCon{DLs4{False{}, t, xt, yt, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, t))
    case 1n+p KCon{WKGo{True{}, isue, can, delta, vi, ps, qs, e, args, fu,
                        pp, mn, mk, cn, p5, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +p2 : U32 = pp
      +mi2 : U32 = I.nth_u(a2, (p2 + 1 : U32), 4294967295)
      km(p, KCon{kwev(delta, mi2, I.skip_u(a2, (p2 + 1 + mn + mk + 1 : U32)),
                      (fu - 1 : U32), ctx), k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, mi2, ri))
    case 1n+p KCon{WKGo{False{}, isue, can, delta, vi, ps, qs, e, args, fu,
                        pp, mn, mk, cn, p5, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WPh2{isue, can, delta, vi, ps, qs, e, args, fu, pp, mn,
                      cn, p5, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ---- phase 2: unit-like structure eta ----
    case 1n+p KCon{WPh2{True{}, can, delta, vi, ps, qs, e, args, fu, pp,
                        mn, cn, p5, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +p2 : U32 = pp
      +mi2 : U32 = I.nth_u(a2, (p2 + 1 : U32), 4294967295)
      km(p, KCon{kwev(delta, mi2, I.skip_u(a2, (p2 + 1 + mn + 1 : U32)),
                      (fu - 1 : U32), ctx), k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, mi2, ri))
    case 1n+p KCon{WPh2{False{}, can, delta, vi, ps, qs, e, args, fu, pp,
                        mn, cn, p5, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +n2 : U32 = cn
      +a2 : List<&2, U32> = args
      +la : U32 = I.len_u(a2, 0)
      +aw : U32 = S.pick(U32.is_eq(n2, R.get(U32, 64n, qtt, 5,
                                             4294967295)), 0,
                   S.pick(U32.is_eq(n2, R.get(U32, 64n, qtt, 6,
                                              4294967295)), 1,
                    S.pick(U32.is_eq(n2, R.get(U32, 64n, qtt, 7,
                                               4294967295)), 2,
                     S.pick(U32.is_eq(n2, R.get(U32, 64n, qtt, 11,
                                                4294967295)), 3,
                      S.pick(U32.is_eq(n2, R.get(U32, 64n, qtt, 12,
                                                 4294967295)), 4,
                       S.pick(U32.is_eq(n2, R.get(U32, 64n, qtt, 13,
                                                  4294967295)), 5,
                        S.pick(U32.is_eq(n2, R.get(U32, 64n, qtt, 14,
                                                   4294967295)), 6,
                         S.pick(U32.is_eq(n2, R.get(U32, 64n, qtt, 15,
                                                    4294967295)), 7,
                          S.pick(U32.is_eq(n2, R.get(U32, 64n, qtt, 26,
                                                     4294967295)), 8,
                           S.pick(U32.is_eq(n2, R.get(U32, 64n, qtt, 27,
                                                      4294967295)), 9,
                            S.pick(U32.is_eq(n2, R.get(U32, 64n, qtt, 28,
                                                       4294967295)), 10,
                             S.pick(U32.is_eq(n2, R.get(U32, 64n, qtt, 29,
                                                        4294967295)), 11,
                              S.pick(U32.is_eq(n2, R.get(U32, 64n, qtt, 30,
                                                         4294967295)), 12,
                               S.pick(U32.is_eq(n2, R.get(U32, 64n, qtt, 31,
                                                          4294967295)), 13,
                                99))))))))))))))
      +isql : Bool = U32.is_eq(n2, R.get(U32, 64n, qtt, 0, 4294967295))
                     && U32.is_gt(la, 5)
      +isqi : Bool = U32.is_eq(n2, R.get(U32, 64n, qtt, 1, 4294967295))
                     && U32.is_gt(la, 4)
      # Lean's reduce_nat (the successor fold and the literal arithmetic)
      # runs in whnf only, never in whnf_core: with delta off the
      # successor's argument was whnf'd in full here, and a pair
      # `succ (a + 4294967264) =?= succ (b + 4294967264)` under a binder
      # (Char.toUpper._proof_1) descended the literal one successor per
      # whnf_core entry; Lean's is_def_eq_offset settles it by args-first
      +dl : Bool = delta
      +issuc : Bool = dl && U32.is_eq(n2, R.get(U32, 64n, qtt, 4, 4294967295))
                      && U32.is_eq(la, 1)
      km(p, KCon{WScB{issuc, I.nth_u(a2, 0, 4294967295),
                      WPh3{dl && U32.is_lt(aw, 14) && U32.is_gt(la, 1), aw,
                           Bool.or(isql, isqi), S.pick(isql, 5, 4), can,
                           delta, vi, ps, qs, e, a2, fu, p5, cx9}, cx9}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WScB{False{}, a0, w3, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{w3, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         knoop(fs, ri))
    case 1n+p KCon{WScB{True{}, a0, w3, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +a2 : U32 = a0
      km(p, KCon{DWhd{a2, cx9}, KCon{WSc2{w3, cx9}, k}}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WSc2{w3, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WSc3{w3, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kfetch(fs, r2, r2))
    case 1n+p KCon{WSc3{w3, ctx}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +nd : T.Ex = node
      km(p, KCon{WSc4{I.is_nat_lit(nd), I.nat_digits(nd), w3, ctx}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WSc4{True{}, d, w3, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kalloc(fs, T.ENat{I.dec_add(d, [49])}, hcb))
    case 1n+p KCon{WSc4{False{}, d, w3, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{w3, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         knoop(fs, ri))
    # ---- phase 3: literal arithmetic ----
    case 1n+p KCon{WPh3{True{}, aw, isq, qneed, can, delta, vi, ps, qs, e,
                        args, fu, p5, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +a2 : List<&2, U32> = args
      +a0 : U32 = I.nth_u(a2, 0, 4294967295)
      km(p, KCon{kwev(delta, a0, Nil{}, (fu - 1 : U32), cx9),
                 KCon{WLa{aw, isq, qneed, can, delta, vi, ps, qs, e, a2,
                          fu, p5, cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, a0, ri))
    case 1n+p KCon{WPh3{False{}, aw, isq, qneed, can, delta, vi, ps, qs, e,
                        args, fu, p5, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WPh4{isq, qneed, can, delta, vi, ps, qs, e, args, fu, p5, ctx},
                 k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WLa{aw, isq, qneed, can, delta, vi, ps, qs, e, args,
                       fu, p5, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +a2 : List<&2, U32> = args
      +a1 : U32 = I.nth_u(a2, 1, 4294967295)
      km(p, KCon{kwev(delta, a1, Nil{}, (fu - 1 : U32), cx9),
                 KCon{WLb{ri, aw, isq, qneed, can, delta, vi, ps, qs, e,
                          a2, fu, p5, cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, a1, 0))
    case 1n+p KCon{WLb{r0, aw, isq, qneed, can, delta, vi, ps, qs, e, args,
                       fu, p5, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = r0
      km(p, KCon{WLc{ri, aw, isq, qneed, can, delta, vi, ps, qs, e, args,
                     fu, p5, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{WLc{r1, aw, isq, qneed, can, delta, vi, ps, qs, e, args,
                       fu, p5, ctx}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +r2 : U32 = r1
      km(p, KCon{WLd{node, aw, isq, qneed, can, delta, vi, ps, qs, e, args,
                     fu, p5, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{WLd{na, aw, isq, qneed, can, delta, vi, ps, qs, e, args,
                       fu, p5, ctx}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +n1 : T.Ex = na
      +n2x : T.Ex = node
      km(p, KCon{WLGo{I.is_nat_lit(n1) && I.is_nat_lit(n2x)
                      && I.lit_ok(aw, I.nat_digits(n1), I.nat_digits(n2x)), aw,
                      I.nat_digits(n1), I.nat_digits(n2x), isq, qneed, can,
                      delta, vi, ps, qs, e, args, fu, p5, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WLGo{True{}, aw, da, db, isq, qneed, can, delta, vi, ps,
                        qs, e, args, fu, p5, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WCont{delta, I.skip_u(args, 2), (fu - 1 : U32), ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         klit(fs, aw, da, db, R.get(U32, 64n, qtt, 8, 4294967295),
              R.get(U32, 64n, qtt, 9, 4294967295), hcb))
    case 1n+p KCon{WLGo{False{}, aw, da, db, isq, qneed, can, delta, vi,
                        ps, qs, e, args, fu, p5, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WPh4{isq, qneed, can, delta, vi, ps, qs, e, args, fu, p5, ctx},
                 k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ---- phase 4: quotient reduction ----
    case 1n+p KCon{WPh4{True{}, qneed, can, delta, vi, ps, qs, e, args,
                        fu, p5, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +a2 : List<&2, U32> = args
      +q2 : U32 = qneed
      +qm : U32 = I.nth_u(a2, q2, 4294967295)
      # the quotient argument is whnf'd in FULL (Lean's quot_reduce_rec
      # calls whnf), with delta off too: `Quot.lift f h q` must reduce when
      # q unfolds to `Quot.mk`, or the tail denies a true equation
      km(p, KCon{pick_kf(delta, kwev(True{}, qm, Nil{}, (fu - 1 : U32), cx9),
                         DWhd{qm, cx9}),
                 KCon{WQ1{q2, can, delta, vi, ps, qs, e, a2, fu, p5, cx9},
                      k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, qm, ri))
    case 1n+p KCon{WPh4{False{}, qneed, can, delta, vi, ps, qs, e, args,
                        fu, p5, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WPh5{p5, can, delta, vi, ps, qs, e, args, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WQ1{qneed, can, delta, vi, ps, qs, e, args, fu, p5, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WQ2{qneed, can, delta, vi, ps, qs, e, args, fu, p5, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, r2, 0))
    case 1n+p KCon{WQ2{qneed, can, delta, vi, ps, qs, e, args, fu, p5, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +a2 : List<&2, U32> = args
      +sa : List<&2, U32> = sargs
      km(p, KCon{WQGo{U32.is_eq(I.const_nm2(hd),
                                R.get(U32, 64n, qtt, 2, 4294967295))
                      && U32.is_gt(I.len_u(sa, 0), 2),
                      I.nth_u(a2, 3, 4294967295), I.nth_u(sa, 2,
                                                          4294967295),
                      qneed, can, delta, vi, ps, qs, e, a2, fu, p5, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WQGo{True{}, fv, vv, qneed, can, delta, vi, ps, qs, e,
                        args, fu, p5, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WCont{delta, I.skip_u(args, (qneed + 1 : U32)),
                       (fu - 1 : U32), ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kalloc(fs, T.EApp{fv, vv}, hcb))
    case 1n+p KCon{WQGo{False{}, fv, vv, qneed, can, delta, vi, ps, qs, e,
                        args, fu, p5, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WPh5{p5, can, delta, vi, ps, qs, e, args, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ---- whnf: delta branch ----
    case 1n+p KCon{WDelGo{True{}, delta, vi, ps, qs, e, args, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      # keyed by the node e AND checked against the body vi (rule-based
      # iota unfolds a different rhs under the same recursor head); a
      # constant without level parameters is keyed by its body alone, so
      # every unfold of it shares one copy whatever node named it
      +ps2 : List<&2, U32> = ps
      +v2 : U32 = vi
      +e2 : U32 = S.pick(kis_nil_u(ps2), v2, e)
      +w2 : R.Tr<U32> = wm
      +h : U32 = R.get(U32, 64n, w2, (1073741824 + e2 : U32), 4294967295)
      +h2 : U32 = h
      +hv : Bool = U32.is_lt(e2, 268435456)
                   && U32.is_eq(R.get(U32, 64n, w2, (1610612736 + e2 : U32),
                                      4294967295), v2)
      km(p, KCon{WDelH{U32.is_ne(h2, 4294967295) && hv, h2, delta, v2, ps2,
                       qs, e2, args, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WDelH{True{}, h, delta, vi, ps, qs, e, args, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WCont{delta, args, (fu - 1 : U32), ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, h))
    case 1n+p KCon{WDelH{False{}, h, delta, vi, ps, qs, e, args, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +v2 : U32 = vi
      km(p, KCon{kev(WP{2, 0, 0, 0, ps, qs, 2000000}, v2),
                 KCon{WDelSt{e, v2, cx9}, KCon{WCont{delta, args, (fu - 1 : U32), cx9},
                                          k}}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, v2, ri))
    case 1n+p KCon{WDelSt{e, vi, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      +e2 : U32 = e
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn,
         R.set_if(U32, U32.is_lt(e2, 268435456),
                  R.set_if(U32, U32.is_lt(e2, 268435456), wm,
                           (1073741824 + e2 : U32), r2, 4294967295),
                  (1610612736 + e2 : U32), vi, 4294967295),
         nt, hcb, knoop(fs, r2))
    case 1n+p KCon{WDelGo{False{}, delta, vi, ps, qs, e, args, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, krebuild(hcb, args, fs, e))
    # ---- whnf: projection, struct reduced -> collect its spine ----
    case 1n+p KCon{WPrj{delta, e, tn, idx, args, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WPrjS{delta, e, tn, idx, args, fu, ctx}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, r2, r2))
    # ---- whnf: projection, spine collected -> constructor? ----
    case 1n+p KCon{WPrjS{delta, e, tn, idx, args, fu, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +hd2 : T.Ex = hd
      km(p, KCon{WPrjS2{kis_str(hd2) && kstr_ok(qtt), hd2, sargs, delta, e,
                        tn, idx, args, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # a string literal: its constructor form, reduced (reduce_proj_core),
    # then the projection again
    case 1n+p KCon{WPrjS2{True{}, hd, sargs, delta, e, tn, idx, args, fu, ctx},
                   k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WPrjSx{delta, e, tn, idx, args, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         ktin_of(kstrexp(fs, kstr_bytes(hd), qtt, hcb)))
    case 1n+p KCon{WPrjSx{delta, e, tn, idx, args, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +r2 : U32 = ri
      km(p, KCon{kwev(True{}, r2, Nil{}, fu, cx9),
                 KCon{WPrj{delta, e, tn, idx, args, fu, cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, r2))
    case 1n+p KCon{WPrjS2{False{}, hd, sargs, delta, e, tn, idx, args, fu, ctx},
                   k} Tuple{Tuple{fs, msg}, ri}:
      +cmi : I.Meta = R.get(I.Meta, 64n, mt, I.const_nm2(hd), I.MNone{})
      km(p, KCon{WPrjGo{I.meta_is_ctor(cmi), delta, e,
                        I.nth_u(sargs, (I.meta_p(cmi) + idx : U32),
                                4294967295),
                        args, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ---- whnf: projection branch ----
    case 1n+p KCon{WPrjGo{True{}, delta, e, fld, args, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +f2 : U32 = fld
      km(p, KCon{kwev(delta, f2, args, fu, ctx), k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kfetch(fs, f2, ri))
    case 1n+p KCon{WPrjGo{False{}, delta, e, fld, args, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, krebuild(hcb, args, fs, e))
    # ---- phase 5: iota (recursor reduction) ----
    case 1n+p KCon{WPh5{P5{True{}, need, ind, pp, mk, cn, us}, can, delta,
                        vi, ps, qs, e, args, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +a2 : List<&2, U32> = args
      +nd2 : U32 = need
      +maj : U32 = I.nth_u(a2, nd2, 4294967295)
      +d2 : Bool = delta
      +f2 : U32 = fu
      # on the main path (full delta and fuel) the major's whnf goes through
      # the memo: the same major is met again at every iota step over it.
      # Without delta (whnf_core) the major is STILL whnf'd in full, as
      # Lean's inductive_reduce_rec does (cheap_rec is never set in the
      # kernel): a stall of the lazy loop is then a genuine stall
      km(p, KCon{pick_kf(Bool.not(d2), DWhd{maj, cx9},
                         pick_kf(U32.is_gt(f2, 100000),
                                 DWhdF{maj, (f2 - 1 : U32), cx9},
                                 kwev(d2, maj, Nil{}, (f2 - 1 : U32), cx9))),
                 KCon{WI1{nd2, ind, pp, mk, cn, us, can, d2, vi, ps, qs,
                          e, a2, f2, cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, maj, ri))
    case 1n+p KCon{WPh5{P5{False{}, need, ind, pp, mk, cn, us}, can, delta,
                        vi, ps, qs, e, args, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WDelGo{can, delta, vi, ps, qs, e, args, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WI1{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs,
                       e, args, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WI2{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs, e,
                     args, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, r2))
    case 1n+p KCon{WI2{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs,
                       e, args, fu, ctx}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +i2 : U32 = ind
      +nd : T.Ex = node
      km(p, KCon{WI2Go{I.is_nat_lit(nd) && U32.is_eq(i2, natn),
                       I.nat_digits(nd), ri, need, i2, pp, mk, cn, us, can,
                       delta, vi, ps, qs, e, args, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{WI2Go{True{}, d, orig, need, ind, pp, mk, cn, us, can,
                         delta, vi, ps, qs, e, args, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WI2b{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs, e,
                      args, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         knatexp(hcb, fs, d, R.get(U32, 64n, qtt, 3, 4294967295),
                 R.get(U32, 64n, qtt, 4, 4294967295)))
    case 1n+p KCon{WI2Go{False{}, d, orig, need, ind, pp, mk, cn, us, can,
                         delta, vi, ps, qs, e, args, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WI2b{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs, e,
                      args, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, orig))
    case 1n+p KCon{WI2b{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs,
                        e, args, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WI3{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs, e,
                     args, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, r2, 0))
    case 1n+p KCon{WI3{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs,
                       e, args, fu, ctx}, k} Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +p2 : U32 = pp
      +i2 : U32 = ind
      +cmi : I.Meta = R.get(I.Meta, 64n, mt, I.const_nm2(hd), I.MNone{})
      # The major premise IS a constructor application, but of a different
      # inductive: a nested inductive's auxiliary recursor (Lean.Syntax.rec_2
      # on List.nil). Lean reduces it by the recursor rule; this iota does
      # not, so the term is NOT stuck, only beyond us. A NO built on it is
      # unsound (it rejected Lean.Syntax.brecOn.go in init-prelude): flag
      # the declaration INCOMPLETE so a reject becomes a decline.
      +other : Bool = I.meta_is_ctor(cmi)
                      && Bool.not(U32.is_eq(I.meta_ind(cmi), i2))
      # 0: a constructor application of the inductive (iota); 1: not one,
      # but the inductive admits structure eta (iota on the projections);
      # 2: stuck
      +isct : Bool = I.meta_is_ctor(cmi) && U32.is_eq(I.meta_ind(cmi), i2)
      +m2 : R.Tr<I.Meta> = mt
      km(p, KCon{WI3c{isct,
                      Bool.not(I.meta_is_ctor(cmi)) && kse_ok(m2, i2),
                      I.skip_u(sargs, p2), I.meta_recs(cmi),
                      I.meta_ci(cmi), I.meta_ccty(cmi), need, p2, mk, cn,
                      us, can, delta, vi, ps, qs, e, args, fu, i2, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         knoop(kfl_set_if(other, fs, hcb, 3, 1), ri))
    case 1n+p KCon{WI3c{True{}, se, fields, recsl, ci, ccty, need, pp, mk,
                        cn, us, can, delta, vi, ps, qs, e, args, fu, ind, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WIGo{True{}, fields, recsl, ci, ccty, need, pp, mk, cn,
                      us, can, delta, vi, ps, qs, e, args, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WI3c{False{}, True{}, fields, recsl, ci, ccty, need, pp,
                        mk, cn, us, can, delta, vi, ps, qs, e, args, fu,
                        ind, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +n2 : U32 = need
      +i2 : U32 = ind
      +m2 : R.Tr<I.Meta> = mt
      km(p, KCon{WSe{Nil{}, n2, pp, mk, cn, us, can, delta, vi, ps, qs,
                     e, a2, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kprojs_tin(kprojs_go(U32.to_nat(I.meta_nf(R.get(I.Meta, 64n, m2,
                                                          i2, I.MNone{}))),
                              0, i2, I.nth_u(a2, n2, 4294967295), hcb,
                              (fs, Nil{}))))
    case 1n+p KCon{WI3c{False{}, False{}, fields, recsl, ci, ccty, need, pp,
                        mk, cn, us, can, delta, vi, ps, qs, e, args, fu,
                        ind, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WIGo{False{}, fields, recsl, ci, ccty, need, pp, mk, cn,
                      us, can, delta, vi, ps, qs, e, args, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WSe{recsl, need, pp, mk, cn, us, can, delta, vi, ps, qs,
                       e, args, fu, ctx}, k} Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      km(p, KCon{WIGo{True{}, sargs, recsl, 0, 4294967295, need, pp, mk, cn,
                      us, can, delta, vi, ps, qs, e, args, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{WIGo{True{}, fields, recsl, ci, ccty, need, pp, mk, cn,
                        us, can, delta, vi, ps, qs, e, args, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +n2 : U32 = need
      km(p, KCon{WIhNext{IC{recsl, cn, us,
                            I.take_u(a2, (n2 - mk : U32), Nil{}), fields,
                            ccty, pp, mk, Nil{}, ci, n2, can, delta, vi,
                            ps, qs, e, a2, fu}, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WIGo{False{}, fields, recsl, ci, ccty, need, pp, mk, cn,
                        us, can, delta, vi, ps, qs, e, args, fu, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WDelGo{can, delta, vi, ps, qs, e, args, fu, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ---- definitional equality ----
    # depth exhausted: the same node is still trivially equal
    case 1n+p KCon{DSub{True{}, same, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.pick_tri(same, L.TYes{}, L.TUnk{})))
    case 1n+p KCon{DSub{False{}, True{}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{DSub{False{}, False{}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = xi
      +y2 : U32 = yi
      km(p, KCon{DSc0{x2, y2, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, kclmax(fs, x2, y2, hcb))
    case 1n+p KCon{DSc0{xi, yi, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = xi
      +y2 : U32 = yi
      +w0 : R.Tr<U32> = wm
      +c2 : List<&2, U32> = ctx
      +lm : U32 = ri
      +cl : Bool = U32.is_eq(lm, 0)
      +ch : U32 = S.pick(cl, 0, kctxh_n(U32.to_nat(lm), c2, 0))
      +hit0 : Bool = cl
                     && (U32.is_eq(R.get(U32, 64n, w0, (x2 + 2147483648 : U32),
                                         4294967295), y2)
                         || U32.is_eq(R.get(U32, 64n, w0,
                                            (y2 + 2147483648 : U32),
                                            4294967295), x2))
      km(p, KCon{DSc0b{hit0, cl, ch, x2, y2, c2, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, w0, nt, hcb, kyc_tin(fs, hcb, x2, y2, ch))
    case 1n+p KCon{DSc0b{hit0, cl, ch, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DSc1{hit0 || U32.is_eq(ri, 1), cl, ch, xi, yi, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DSc1{True{}, cl, ch, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{DSc1{False{}, cl, ch, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +y2 : U32 = yi
      km(p, KCon{DDc0{cl, ch, xi, y2, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kfetch(fs, y2, 0))
    case 1n+p KCon{DDc0{cl, ch, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
      +q2 : R.Tr<U32> = qtt
      +nd : T.Ex = node
      km(p, KCon{DDc3{cl && U32.is_eq(I.const_nm2(nd),
                                      R.get(U32, 64n, q2, 8, 4294967295))
                         && Bool.not(U32.is_eq(I.const_nm2(nd), 4294967295)),
                      cl, ch, xi, yi, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # Lean's is_def_eq_core tries proof irrelevance before any structural
    # work: when the cheap type oracle says x is a proof, two proofs of
    # defeq types are equal (YES only here; otherwise the structural path,
    # whose own irrelevance step still runs)
    # is_def_eq_core: whnf_core both sides first (no delta, cheap
    # projections, recursor majors whnf'd in full), the YES cache keyed on
    # the originals
    case 1n+p KCon{DDc3{False{}, cl, ch, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +x2 : U32 = xi
      +y2 : U32 = yi
      km(p, KCon{kwev(False{}, x2, Nil{}, 65536, cx9),
                 KCon{DE2{y2, cx9, fu}, KCon{DSRec{cl, ch, x2, y2}, k}}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, x2, 0))
    case 1n+p KCon{DE2{yi, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +wx : U32 = ri
      +y2 : U32 = yi
      km(p, KCon{kwev(False{}, y2, Nil{}, 65536, cx9), KCon{DE3{wx, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, y2, 0))
    case 1n+p KCon{DE3{wx, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +wy : U32 = ri
      +wx2 : U32 = wx
      km(p, KCon{DE3b{U32.is_eq(wx2, wy), wx2, wy, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DE3b{True{}, wx, wy, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    # Lean's quick_is_def_eq `t == s`: structural equality of two distinct
    # nodes (an export node against its rebuilt twin, `Option #37` twice);
    # then proof irrelevance once, on the whnf_core'd pair
    case 1n+p KCon{DE3b{False{}, wx, wy, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = wx
      +y2 : U32 = wy
      km(p, KCon{DE3c{x2, y2, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, keq_lists_tin(fs, Con{x2, Nil{}}, Con{y2, Nil{}}, lnt))
    case 1n+p KCon{DE3c{wx, wy, ctx, fu}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{DE3d{L.tri_is_yes(t), wx, wy, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DE3d{True{}, wx, wy, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{DE3d{False{}, wx, wy, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = wx
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DTy1{c2}, KCon{PI1{False{}, x2, wy, c2, fu}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, x2, 0))
    # the lazy delta loop (decisive entry), then the structural tail on the
    # pair it stalled at (whnf_core'd again: the pair is the last
    # iteration's INPUT), or on the originals when it left no pair
    case 1n+p KCon{DEL{x, y, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +x2 : U32 = x
      +y2 : U32 = y
      km(p, KCon{LZ0d{x2, y2, 1024, cx9}, KCon{DE4{x2, y2, cx9, fu}, k}}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DE4{x, y, ctx, fu}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      +r2 : U32 = ri
      km(p, KCon{DE4b{L.tri_is_yes(t), U32.is_eq(r2, 0), x, y, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, r2))
    case 1n+p KCon{DE4b{True{}, nopair, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{DE4b{False{}, True{}, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DPr0{x, y, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DE4b{False{}, False{}, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{DE5{ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt,
         hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{DE5{ctx, fu}, k} Tuple{Tuple{fs, MX{T.EApp{a, b}}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +a2 : U32 = a
      km(p, KCon{kwev(False{}, a2, Nil{}, 65536, cx9), KCon{DE6{b, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, a2, 0))
    case 1n+p KCon{DE5{ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TUnk{}))
    case 1n+p KCon{DE6{b, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +wa : U32 = ri
      +b2 : U32 = b
      km(p, KCon{kwev(False{}, b2, Nil{}, 65536, cx9), KCon{DE7{wa, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, b2, 0))
    case 1n+p KCon{DE7{wa, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +wb : U32 = ri
      +wa2 : U32 = wa
      km(p, KCon{DE7b{U32.is_eq(wa2, wb), wa2, wb, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DE7b{True{}, wa, wb, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{DE7b{False{}, wa, wb, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DPr0{wa, wb, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, knoop(fs, 0))
    # Lean's `whnf_core(t_n)` with cheap_proj = false, both sides: a side
    # whose spine head is a projection gets its structure whnf'd in full
    # (reduce_proj); `s'.i args` is rebuilt and whnf_core'd. Any change:
    # is_def_eq_core again on the new pair; none: the structural tail
    # first Lean's `t_n.i =?= s_n.i` (lazy_delta_proj_reduction): the two
    # structures by is_def_eq -- `(step (id c) n x).1 =?= (step c n x).1`
    # is settled args-first, before any full whnf of a structure
    case 1n+p KCon{DPr0{x, y, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      km(p, KCon{DPq1{x2, y, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, kfetch(fs, x2, 0))
    case 1n+p KCon{DPq1{x, y, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EProj{tn1, i1, s1}}}, ri}:
      +y2 : U32 = y
      km(p, KCon{DPq2{tn1, i1, s1, x, y2, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kfetch(fs, y2, 0))
    case 1n+p KCon{DPq1{x, y, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      km(p, KCon{DPr1{True{}, False{}, x2, y, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, x2, 0))
    case 1n+p KCon{DPq2{tn1, i1, s1, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EProj{tn2, i2, s2}}}, ri}:
      +s1b : U32 = s1
      +s2b : U32 = s2
      +f2 : U32 = fu
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DPq3{U32.is_eq(tn1, tn2) && U32.is_eq(i1, i2), s1b, s2b, x,
                      y, c2, f2}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DPq2{tn1, i1, s1, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      km(p, KCon{DPr1{True{}, False{}, x2, y, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, x2, 0))
    # Lean's lazy_delta_proj_reduction: the structures through the lazy
    # loop only (YES settles it); at the stall, when both are constructor
    # applications, the projected FIELDS are compared (reduce_proj_core:
    # `(P (slow n)).1 =?= (Q (slow m)).1` compares `0 =?= 0`, never the
    # second fields); otherwise the structures in full
    case 1n+p KCon{DPq3{True{}, s1, s2, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +s1b : U32 = s1
      +s2b : U32 = s2
      km(p, KCon{LZ0d{s1b, s2b, 1024, cx9}, KCon{DPq4{s1b, s2b, x, y, cx9, fu},
                                            k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DPq3{False{}, s1, s2, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      km(p, KCon{DPr1{True{}, False{}, x2, y, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, x2, 0))
    case 1n+p KCon{DPq4{s1, s2, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +r2 : U32 = ri
      km(p, KCon{DPq4b{L.tri_is_yes(t), U32.is_eq(r2, 0), s1, s2, x, y, ctx,
                       fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, r2))
    case 1n+p KCon{DPq4b{True{}, nopair, s1, s2, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{DPq4b{False{}, True{}, s1, s2, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +s1b : U32 = s1
      km(p, KCon{DPq6{s1b, s2, x, y, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kspine_tin(fs, s1b, 0))
    case 1n+p KCon{DPq4b{False{}, False{}, s1, s2, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{DPq5p{x, y, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{DPq5p{x, y, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EApp{a, b}}}, ri}:
      +a2 : U32 = a
      km(p, KCon{DPq6{a2, b, x, y, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kspine_tin(fs, a2, 0))
    case 1n+p KCon{DPq5p{x, y, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      km(p, KCon{DPr1{True{}, False{}, x2, y, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, x2, 0))
    case 1n+p KCon{DPq6{a, b, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +b2 : U32 = b
      km(p, KCon{DPq7{hd, sargs, a, b2, x, y, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, b2, 0))
    case 1n+p KCon{DPq7{ha, sa, a, b, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +ha2 : T.Ex = ha
      +hb2 : T.Ex = hd
      +sa2 : List<&2, U32> = sa
      +sb2 : List<&2, U32> = sargs
      +ma : I.Meta = R.get(I.Meta, 64n, mt, I.const_nm2(ha2), I.MNone{})
      +mb : I.Meta = R.get(I.Meta, 64n, mt, I.const_nm2(hb2), I.MNone{})
      +ca : Bool = I.meta_is_ctor(ma)
                   && U32.is_eq(I.len_u(sa2, 0),
                                (I.meta_p(ma) + I.meta_nf(ma) : U32))
      +cb : Bool = I.meta_is_ctor(mb)
                   && U32.is_eq(I.len_u(sb2, 0),
                                (I.meta_p(mb) + I.meta_nf(mb) : U32))
      +x2 : U32 = x
      km(p, KCon{DPq8{ca && cb, I.meta_p(ma), sa2, I.meta_p(mb), sb2, a, b, x2,
                      y, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, x2, 0))
    # both constructor applications: the projected fields
    case 1n+p KCon{DPq8{True{}, pa, sa, pb, sb, a, b, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EProj{tn, idx, sx}}}, ri}:
      +i2 : U32 = idx
      +fa : U32 = I.nth_u(sa, (pa + i2 : U32), 4294967295)
      +fb : U32 = I.nth_u(sb, (pb + i2 : U32), 4294967295)
      +f2 : U32 = fu
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295),
                      U32.is_eq(fa, fb), fa, fb, c2, (f2 - 1 : U32)},
                 KCon{DPq4x{x, y, c2, f2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    # otherwise the structures in full (Lean's is_def_eq_core(t_n, s_n))
    case 1n+p KCon{DPq8{cc, pa, sa, pb, sb, a, b, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +a2 : U32 = a
      +b2 : U32 = b
      +f2 : U32 = fu
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295),
                      U32.is_eq(a2, b2), a2, b2, c2, (f2 - 1 : U32)},
                 KCon{DPq4x{x, y, c2, f2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DPq4x{x, y, ctx, fu}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      +x2 : U32 = x
      km(p, KCon{DPq5{L.tri_is_yes(t), x2, y, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DPq5{True{}, x, y, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{DPq5{False{}, x, y, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      km(p, KCon{DPr1{True{}, False{}, x2, y, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, x2, 0))
    case 1n+p KCon{DPr1{left, chg, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      match hd:
        case T.EProj{tn, i, sx}:
          +s2 : U32 = sx
          km(p, KCon{DWhd{s2, ctx}, KCon{DPr2{left, chg, tn, i, s2, sargs, x, y,
                                         ctx, fu}, k}},
             lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
        case _:
          km(p, KCon{DPr4{left, chg, x, y, ctx, fu}, k}, lnt, nlx, mt, lp,
             vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DPr2{left, chg, tn, i, s, sargs, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      +s2 : U32 = s
      km(p, KCon{DPr2b{U32.is_eq(r2, s2), left, chg, tn, i, r2, sargs, x, y,
                       ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, r2))
    case 1n+p KCon{DPr2b{True{}, left, chg, tn, i, s, sargs, x, y, ctx, fu},
                   k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DPr4{left, chg, x, y, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DPr2b{False{}, left, chg, tn, i, s, sargs, x, y, ctx, fu},
                   k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DPr3{left, chg, x, y, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb,
         klzpj(hcb, sargs, khc(fs, T.EProj{tn, i, s}, hcb)))
    case 1n+p KCon{DPr3{left, chg, x, y, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +r2 : U32 = ri
      km(p, KCon{kwev(False{}, r2, Nil{}, 65536, cx9),
                 KCon{DPr3b{left, chg, x, y, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{DPr3b{True{}, chg, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{DPr4{True{}, True{}, r2, y, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DPr3b{False{}, chg, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{DPr4{False{}, True{}, x, r2, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    # the left side done: the right side
    case 1n+p KCon{DPr4{True{}, chg, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +y2 : U32 = y
      km(p, KCon{DPr1{False{}, chg, x, y2, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, y2, 0))
    case 1n+p KCon{DPr4{False{}, True{}, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      +y2 : U32 = y
      +f2 : U32 = fu
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295),
                      U32.is_eq(x2, y2), x2, y2, ctx, (f2 - 1 : U32)}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DPr4{False{}, False{}, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      km(p, KCon{DEx{x2, y, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, kfetch(fs, x2, 0))
    case 1n+p KCon{PI1{cl, x, y, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +t2 : U32 = ri
      km(p, KCon{PI1g{U32.is_ne(t2, 4294967295), t2, cl, x, y, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, t2))
    case 1n+p KCon{PI1g{True{}, tx, cl, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +t2 : U32 = tx
      +c2 : List<&2, U32> = ctx
      km(p, KCon{kslev(t2, c2, 2000000), KCon{PI2{t2, cl, x, y, c2, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, t2))
    case 1n+p KCon{PI2{tx, cl, x, y, ctx, fu}, k} Tuple{Tuple{fs, MLn{u}}, ri}:
      km(p, KCon{PI2g{L.tri_is_yes(L.ln_is_zero(u)), tx, cl, x, y, ctx, fu},
                 k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{PI2g{True{}, tx, cl, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +y2 : U32 = y
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DTy1{c2}, KCon{PI3{tx, cl, x, y2, c2, fu}, k}}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, y2, 0))
    case 1n+p KCon{PI3{tx, cl, x, y, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +t2 : U32 = ri
      km(p, KCon{PI3g{U32.is_ne(t2, 4294967295), tx, t2, cl, x, y, ctx, fu},
                 k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, t2))
    # the types compared lazily (the probe: whnf_core and lazy delta, never a
    # full whnf -- a proof's type can unfold into a long evaluation)
    # the types by the full defeq (is_def_eq, lazy inside), in a rollback
    # region; a NO is kept conservative (the lazy loop and the tail still
    # get the pair) until the oracle's typing is validated on a full run
    case 1n+p KCon{PI3g{True{}, tx, ty, cl, x, y, ctx, fu}, k}
         Tuple{Tuple{Tuple{ex, nx}, msg}, ri}:
      +n2 : U32 = nx
      +f2 : U32 = fu
      +tx2 : U32 = tx
      +ty2 : U32 = ty
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295),
                      U32.is_eq(tx2, ty2), tx2, ty2, c2, (f2 - 1 : U32)},
                 KCon{KZr{}, KCon{KRb{n2, wm}, KCon{PI6{cl, x, y, c2, f2},
                                                     k}}}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop((ex, n2), ri))
    case 1n+p KCon{PI6{cl, x, y, ctx, fu}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{PI6g{L.tri_is_yes(t), cl, x, y, ctx, fu}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{PI6g{True{}, cl, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    # not (known to be) proofs of one type: the lazy delta loop
    case 1n+p KCon{PI1g{False{}, tx, cl, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DEL{x, y, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm,
         nt, hcb, knoop(fs, 0))
    case 1n+p KCon{PI2g{False{}, tx, cl, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DEL{x, y, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm,
         nt, hcb, knoop(fs, 0))
    case 1n+p KCon{PI3g{False{}, tx, ty, cl, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DEL{x, y, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm,
         nt, hcb, knoop(fs, 0))
    case 1n+p KCon{PI6g{False{}, cl, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DEL{x, y, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm,
         nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DDc3{True{}, cl, ch, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +x2 : U32 = xi
      km(p, KCon{DWhd{x2, cx9}, KCon{DDc1{x2, yi, cx9, fu}, k}}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DDc1{xi, yi, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{DDc2{xi, yi, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{DDc2{xi, yi, ctx, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +q2 : R.Tr<U32> = qtt
      +nd : T.Ex = node
      +tru : Bool = U32.is_eq(I.const_nm2(nd),
                              R.get(U32, 64n, q2, 8, 4294967295))
      +x2 : U32 = xi
      +y2 : U32 = yi
      km(p, KCon{DDc3x{tru, x2, y2, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DDc3x{True{}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{DDc3x{False{}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = xi
      +y2 : U32 = yi
      km(p, KCon{DEx{x2, y2, ctx, fu}, KCon{DSRec{True{}, 0, x2, y2}, k}}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, x2, 0))
    case 1n+p KCon{DSRec{cl, ch, xi, yi}, k}
         Tuple{Tuple{Tuple{ex, nx}, MTri{t}}, ri}:
      +t2 : L.Tri = t
      +w0 : R.Tr<U32> = wm
      +c3 : Bool = cl
      +yes : Bool = L.tri_is_yes(t2)
      +x2 : U32 = xi
      +y2 : U32 = yi
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn,
         R.set_if(U32, c3 && yes, w0, (x2 + 2147483648 : U32), y2,
                  4294967295),
         nt, hcb, kmtri((kyc_set(yes, ex, hcb, x2, y2, S.pick(c3, 0, ch)), nx),
                        t2))
    case 1n+p KCon{DEx{xi, yi, ctx, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +y2 : U32 = yi
      km(p, KCon{DEy{node, xi, y2, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kfetch(fs, y2, ri))
    # -- Sort/Sort --
    case 1n+p KCon{DEy{T.ESort{a}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.ESort{b}}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.ln_cmp(R.get(L.LN, 64n, lnt, a, L.LNun{}),
                            R.get(L.LN, 64n, lnt, b, L.LNun{}))))
    # -- BVar/BVar: equal indices are equal; otherwise decide from the
    #    (lifted, reduced) types: proof irrelevance, unit eta, or denial --
    case 1n+p KCon{DEy{T.EBVar{a}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EBVar{b}}}, ri}:
      +a2 : U32 = a
      +b2 : U32 = b
      +c2 : List<&2, U32> = ctx
      +ta : U32 = I.nth_u(c2, a2, 4294967295)
      +tb : U32 = I.nth_u(c2, b2, 4294967295)
      +t2 : U32 = ta
      km(p, KCon{kev(WP{0, 0, (a2 + 1 : U32), 0, Nil{}, Nil{}, 2000000}, t2),
                 KCon{DBv1{a2, b2, tb, Bool.not(U32.is_eq(t2,
                                                          4294967295)),
                           Bool.not(U32.is_eq(tb, 4294967295)), c2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
    case 1n+p KCon{DBv1{a, b, tb, taok, tbok, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +t2 : U32 = tb
      +b2 : U32 = b
      km(p, KCon{kev(WP{0, 0, (b2 + 1 : U32), 0, Nil{}, Nil{}, 2000000}, t2),
                 KCon{DBv2{a, b2, ri, taok, tbok, ctx}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, 0))
    case 1n+p KCon{DBv2{a, b, la, taok, tbok, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +l2 : U32 = la
      km(p, KCon{DWhd{l2, cx9}, KCon{DBv3{a, b, ri, taok, tbok, cx9}, k}}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DBv3{a, b, lb, taok, tbok, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +l2 : U32 = lb
      km(p, KCon{DWhd{l2, cx9}, KCon{DBv4{a, b, ri, taok, tbok, cx9}, k}}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DBv4{a, b, wa, taok, tbok, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +w2 : U32 = wa
      +r2 : U32 = ri
      km(p, KCon{DBv5{a, b, w2, r2, taok, tbok, ctx}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb,
         keq_lists_tin(fs, Con{w2, Nil{}}, Con{r2, Nil{}}, lnt))
    case 1n+p KCon{DBv5{a, b, wa, wb, taok, tbok, ctx}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +w2 : U32 = wa
      +c2 : List<&2, U32> = ctx
      +wb2 : U32 = wb
      km(p, KCon{DTy1{c2},
                 KCon{DBv6{a, b, w2, wb2, L.tri_is_yes(t),
                           Bool.and(taok, tbok), c2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, w2, ri))
    case 1n+p KCon{DBv6{a, b, wa, wb, samety, both, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +r2 : U32 = ri
      km(p, KCon{DWhd{r2, cx9}, KCon{DBv7{a, b, wa, wb, samety, both,
                                     Bool.not(U32.is_eq(r2, 4294967295)),
                                     cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DBv7{a, b, wa, wb, samety, both, rtok, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{DBv8{a, b, wa, wb, samety, both, rtok, ctx}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{DBv8{a, b, wa, wb, samety, both, rtok, ctx}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +ks : T.Ex = node
      +w2 : U32 = wa
      +rk : Bool = rtok && I.is_sortx(ks)
      +lz : L.Tri = L.ln_is_zero(R.get(L.LN, 64n, lnt, I.sort_lvl_of(ks),
                                       L.LNun{}))
      km(p, KCon{kslev(w2, cx9, 2000000),
                 KCon{DBv9{a, b, w2, wb, samety, both,
                           rk && L.tri_is_yes(lz), rk && L.tri_is_no(lz),
                           cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, w2, ri))
    case 1n+p KCon{DBv9{a, b, wa, wb, samety, both, part1, part1n, ctx}, k}
         Tuple{Tuple{fs, MLn{u}}, ri}:
      +w2 : U32 = wa
      +u2 : L.LN = u
      km(p, KCon{DBv10{a, b, w2, wb, samety, both,
                       Bool.or(part1, L.tri_is_yes(L.ln_is_zero(u2))),
                       Bool.or(part1n, L.tri_is_no(L.ln_is_zero(u2))),
                       ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, w2, ri))
    # two distinct bound variables: equal only by proof irrelevance (their
    # types are Props and DEFINITIONALLY equal -- `samety` is merely the
    # structural test after whnf, so a Prop pair it misses is compared in
    # full) or unit eta; two non-proofs are never equal. A Prop pair whose
    # types are not shown equal is UNKNOWN, never NO
    case 1n+p KCon{DBv10{a, b, wa, wb, samety, both, isprop, notprop, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +smi : I.Meta = R.get(I.Meta, 64n, mt, I.const_nm2(hd), I.MNone{})
      +isunit : Bool = I.meta_is_ind(smi)
                       && U32.is_eq(I.meta_nf(smi), 0)
      +b3 : Bool = both
      +sm : Bool = samety
      +ip : Bool = isprop
      +same : Bool = U32.is_eq(a, b)
      +yes : Bool = same || (b3 && sm && (ip || isunit))
      +deep : Bool = Bool.not(yes) && b3 && ip
      +wa2 : U32 = wa
      +wb2 : U32 = wb
      km(p, KCon{DBvGo{deep, yes,
                       L.pick_tri(yes, L.TYes{},
                                  # NO only for types KNOWN not to be
                                  # Props, and not unit-like
                                  L.pick_tri(b3 && notprop
                                             && Bool.not(isunit),
                                             L.TNo{}, L.TUnk{})),
                       wa2, wb2, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DBvGo{False{}, yes, t, wa, wb, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, t))
    case 1n+p KCon{DBvGo{True{}, yes, t, wa, wb, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +w1 : U32 = wa
      +w2 : U32 = wb
      km(p, KCon{DSub{False{}, U32.is_eq(w1, w2), w1, w2, ctx, 4096},
                 KCon{DBvT{}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DBvT{}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.pick_tri(L.tri_is_yes(t), L.TYes{}, L.TUnk{})))
    # -- Const/Const --
    case 1n+p KCon{DEy{T.EConst{a, us}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EConst{b, vs}}}, ri}:
      +a2 : U32 = a
      +b2 : U32 = b
      +ta : U32 = R.get(U32, 64n, nt, a2, 4294967295)
      +tb : U32 = R.get(U32, 64n, nt, b2, 4294967295)
      km(p, KCon{DCn2{a2, us, b2, vs, ta, tb, ctx}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb,
         keq_lists_tin(fs, Con{ta, Nil{}}, Con{tb, Nil{}}, lnt))
    case 1n+p KCon{DCn2{a, us, b, vs, ta, tb, ctx}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +t2 : U32 = ta
      km(p, KCon{DCn3x{a, us, b, vs, t2, tb, L.tri_is_yes(t), ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
    case 1n+p KCon{DCn3x{a, us, b, vs, ta, tb, samety, ctx}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
      # the fetched node is ta's; its universe comes from the oracle, under
      # the comparison's own context
      +t2 : U32 = ta
      km(p, KCon{kslev(t2, ctx, 2000000),
                 KCon{DCn4{a, us, b, vs, t2, tb, samety}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
    case 1n+p KCon{DCn4{a, us, b, vs, ta, tb, samety}, k}
         Tuple{Tuple{fs, MLn{u}}, ri}:
      +a2 : U32 = a
      +b2 : U32 = b
      +u2 : L.LN = u
      +known : Bool = Bool.not(U32.is_eq(ta, 4294967295))
                      && Bool.not(U32.is_eq(tb, 4294967295))
      +isprop : Bool = L.tri_is_yes(L.ln_is_zero(u2))
      +notprop : Bool = L.tri_is_no(L.ln_is_zero(u2))
      +novals : Bool = U32.is_eq(R.get(U32, 64n, vt, a2, 4294967295),
                                 4294967295)
                       && U32.is_eq(R.get(U32, 64n, vt, b2, 4294967295),
                                    4294967295)
      +hasval : Bool = Bool.not(U32.is_eq(R.get(U32, 64n, vt, a2,
                                                4294967295), 4294967295))
      +lv3 : L.Tri = I.eq_lvls(us, vs, lnt)
      +sm : Bool = samety
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs,
               L.pick_tri(U32.is_eq(a2, b2),
                          L.pick_tri(L.tri_is_no(lv3) && hasval, L.TUnk{},
                                     lv3),
                          L.pick_tri(known && sm && isprop, L.TYes{},
                                     L.pick_tri(known && sm && novals
                                                && notprop,
                                                L.TNo{}, L.TUnk{})))))
    # -- Pi/Pi --
    # Lean's is_def_eq_binding: the domains by is_def_eq (never a whnf),
    # then the bodies under the binder; shared by Pi/Pi and Lam/Lam
    case 1n+p KCon{DEy{T.EAll{n1, t1, b1, i1}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EAll{n2, t2, b2, i2}}}, ri}:
      +t12 : U32 = t1
      +t22 : U32 = t2
      +f2 : U32 = fu
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295),
                      U32.is_eq(t12, t22), t12, t22, c2, (f2 - 1 : U32)},
                 KCon{DAl3{b1, b2, t12, c2, f2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DAl2{w1, t1, t2, b1, b2, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +t22 : U32 = t2
      km(p, KCon{DWhd{t22, cx9}, KCon{DAl2b{ri, t1, t22, b1, b2, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DAl2b{w1, t1, t2, b1, b2, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +f2 : U32 = fu
      +c2 : List<&2, U32> = ctx
      +w1b : U32 = w1
      +r2 : U32 = ri
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295),
                      U32.is_eq(t1, t2), w1b, r2, c2, (f2 - 1 : U32)},
                 KCon{DAl3{b1, b2, t1, c2, f2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DAl3{b1, b2, t1, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +t2 : L.Tri = t
      km(p, KCon{DAl3g{L.tri_is_no(t2), t2, b1, b2, t1, ctx, fu}, k}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DAl3g{True{}, d1, b1, b2, t1, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, d1))
    case 1n+p KCon{DAl3g{False{}, d1, b1, b2, t1, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +b12 : U32 = b1
      km(p, KCon{DBd1{b12, b2, Con{t1, ctx}, fu}, KCon{DAl6{d1}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, b12, 0))
    case 1n+p KCon{DBd1{b1, b2, ctx, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +b22 : U32 = b2
      km(p, KCon{DBd2{node, b1, b22, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kfetch(fs, b22, 0))
    # both bodies lambdas, or both Pis: the next binder of the pass (Lean's
    # do-while in is_def_eq_binding); otherwise the bodies by is_def_eq
    case 1n+p KCon{DBd2{T.ELam{n1, t1, c1, i1}, b1, b2, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.ELam{n2, t2, c2, i2}}}, ri}:
      +t12 : U32 = t1
      +t22 : U32 = t2
      +f2 : U32 = fu
      +c9 : List<&2, U32> = ctx
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295),
                      U32.is_eq(t12, t22), t12, t22, c9, (f2 - 1 : U32)},
                 KCon{DAl3{c1, c2, t12, c9, f2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DBd2{T.EAll{n1, t1, c1, i1}, b1, b2, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EAll{n2, t2, c2, i2}}}, ri}:
      +t12 : U32 = t1
      +t22 : U32 = t2
      +f2 : U32 = fu
      +c9 : List<&2, U32> = ctx
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295),
                      U32.is_eq(t12, t22), t12, t22, c9, (f2 - 1 : U32)},
                 KCon{DAl3{c1, c2, t12, c9, f2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DBd2{xn, b1, b2, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +b12 : U32 = b1
      +b22 : U32 = b2
      +f2 : U32 = fu
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295),
                      U32.is_eq(b12, b22), b12, b22, ctx, (f2 - 1 : U32)}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DAl4{d1, b1, b2, t1, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +b22 : U32 = b2
      km(p, KCon{DWhd{b22, cx9}, KCon{DAl5{d1, ri, b1, b22, t1, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DAl5{d1, w3, b1, b2, t1, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +f2 : U32 = fu
      +w3b : U32 = w3
      +r2 : U32 = ri
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295),
                      U32.is_eq(b1, b2), w3b, r2, Con{t1, ctx},
                      (f2 - 1 : U32)},
                 KCon{DAl6{d1}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DAl6{d1}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, I.tri_and(d1, t)))
    # -- Lam/Lam --
    case 1n+p KCon{DEy{T.ELam{n1, t1, b1, i1}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.ELam{n2, t2, b2, i2}}}, ri}:
      +t12 : U32 = t1
      +t22 : U32 = t2
      +f2 : U32 = fu
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295),
                      U32.is_eq(t12, t22), t12, t22, c2, (f2 - 1 : U32)},
                 KCon{DAl3{b1, b2, t12, c2, f2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DLm3{w3, b1, b2, t1, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +b22 : U32 = b2
      km(p, KCon{DWhd{b22, cx9}, KCon{DLm3b{ri, b1, b22, t1, cx9, fu}, k}}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DLm3b{w3, b1, b2, t1, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +f2 : U32 = fu
      +w3b : U32 = w3
      +r2 : U32 = ri
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295),
                      U32.is_eq(b1, b2), w3b, r2, Con{t1, ctx},
                      (f2 - 1 : U32)},
                 KCon{DLm4{}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DLm4{}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, t))
    # -- App/App --
    # Lean's is_def_eq_app, after the lazy loop stalled: the functions by
    # is_def_eq, then the arguments; otherwise eta, structure eta, the
    # denial and proof irrelevance (DC1)
    case 1n+p KCon{DEy{T.EApp{f1, a1}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EApp{f2, a2}}}, ri}:
      +x2 : U32 = xi
      km(p, KCon{DAs1{x2, yi, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, kspine_itin(fs, x2))
    case 1n+p KCon{DAs1{xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +y2 : U32 = yi
      km(p, KCon{DAs2{ri, sargs, xi, y2, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kspine_itin(fs, y2))
    case 1n+p KCon{DAs2{hx, sx, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +hy : U32 = ri
      +hx2 : U32 = hx
      +sx2 : List<&2, U32> = sx
      +sy2 : List<&2, U32> = sargs
      +f9 : U32 = fu
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DAs3{U32.is_eq(I.len_u(sx2, 0), I.len_u(sy2, 0)), hx2, hy,
                      sx2, sy2, xi, yi, c2, f9}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    # different arity: not equal as applications (the tail decides)
    case 1n+p KCon{DAs3{False{}, hx, hy, sx, sy, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = xi
      km(p, KCon{DApN1{L.TNo{}, x2, yi, ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kspine_tin(fs, x2, ri))
    case 1n+p KCon{DAs3{True{}, hx, hy, sx, sy, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +hx2 : U32 = hx
      +hy2 : U32 = hy
      +f9 : U32 = fu
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DSub{U32.is_eq((f9 - 1 : U32), 4294967295),
                      U32.is_eq(hx2, hy2), hx2, hy2, c2, (f9 - 1 : U32)},
                 KCon{DAs4{sx, sy, xi, yi, c2, f9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DAs4{sx, sy, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +t2 : L.Tri = t
      km(p, KCon{DAs5{L.tri_is_yes(t2), sx, sy, xi, yi, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, t2))
    case 1n+p KCon{DAs5{False{}, sx, sy, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +x2 : U32 = xi
      km(p, KCon{DApN1{t, x2, yi, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, kspine_tin(fs, x2, ri))
    # the arguments, first to last
    case 1n+p KCon{DAs5{True{}, Nil{}, sy, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{DAs5{True{}, Con{a, at}, Con{b, bt}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +a2 : U32 = a
      +b2 : U32 = b
      +f9 : U32 = fu
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DSub{U32.is_eq((f9 - 1 : U32), 4294967295),
                      U32.is_eq(a2, b2), a2, b2, c2, (f9 - 1 : U32)},
                 KCon{DAs4{at, bt, xi, yi, c2, f9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DAs5{True{}, sx, sy, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = xi
      km(p, KCon{DApN1{L.TNo{}, x2, yi, ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kspine_tin(fs, x2, ri))
    case 1n+p KCon{DAp1{f1, a1, f2, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +t2 : L.Tri = t
      km(p, KCon{DAp2{L.tri_is_yes(t2), f1, a1, f2, a2, xi, yi, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, t2))
    case 1n+p KCon{DAp2{True{}, f1, a1, f2, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +a12 : U32 = a1
      +a22 : U32 = a2
      +f9 : U32 = fu
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DSub{U32.is_eq((f9 - 1 : U32), 4294967295),
                      U32.is_eq(a12, a22), a12, a22, c2, (f9 - 1 : U32)},
                 KCon{DAp3{f1, a12, f2, a22, xi, yi, c2, f9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DAp3{f1, a1, f2, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +t2 : L.Tri = t
      km(p, KCon{DAp4{L.tri_is_yes(t2), f1, a1, f2, a2, xi, yi, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, t2))
    case 1n+p KCon{DAp4{True{}, f1, a1, f2, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    # the applications do not match structurally: the old DAq6 tail --
    # proof irrelevance with its guarded structure eta (ONE ctor side; the
    # catch-all's eta on two ctor applications rebuilt `mk (mk p.0 ..).0`
    # until the depth budget ran out), the tri propagated (an UNK on an
    # argument pair stays UNK: the rigid denial would be unsound)
    case 1n+p KCon{DAp4{False{}, f1, a1, f2, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +x2 : U32 = xi
      km(p, KCon{DApN1{t, x2, yi, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, kspine_tin(fs, x2, ri))
    case 1n+p KCon{DAp2{False{}, f1, a1, f2, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +x2 : U32 = xi
      km(p, KCon{DApN1{t, x2, yi, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, kspine_tin(fs, x2, ri))
    # a structural NO is final only when the pair is in whnf: a side whose
    # head is a definition with a value, or a projection, could still unfold
    # (the lazy loop stopped on its budget, not on a stall) -- then UNK
    case 1n+p KCon{DApN1{t, xi, yi, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +y2 : U32 = yi
      km(p, KCon{DApN2{t, kunf(hd, vt), xi, y2, ctx}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, y2, ri))
    case 1n+p KCon{DApN2{t, cx, xi, yi, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +t2 : L.Tri = t
      +x2 : U32 = xi
      +open : Bool = cx || kunf(hd, vt)
      km(p, KCon{DIr1{L.pick_tri(L.tri_is_no(t2) && open, L.TUnk{}, t2), x2,
                      yi, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, x2, ri))
    case 1n+p KCon{DLz1{f1, f2, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +hx2 : T.Ex = hd
      +sx2 : List<&2, U32> = sargs
      +yi2 : U32 = yi
      km(p, KCon{DLz2{hx2, sx2, f1, f2, a1, a2, xi, yi, ctx, fu}, k}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, yi2, ri))
    case 1n+p KCon{DLz2{hx, sx, f1, f2, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +hx2 : T.Ex = hx
      +hy2 : T.Ex = hd
      +nmx : U32 = kcn(hx2)
      +nmy : U32 = kcn(hy2)
      +sx2 : List<&2, U32> = sx
      +sy2 : List<&2, U32> = sargs
      # same head = the SAME constant with the SAME universe levels (Lean's
      # lazy_delta step also requires is_def_eq on the levels); index-equal
      # level lists is a conservative sufficient test
      +samehd : Bool = Bool.not(U32.is_eq(nmx, 4294967295))
                       && U32.is_eq(nmx, nmy)
                       && I.eq_u32s(kcus(hx2), kcus(hy2))
                       && U32.is_eq(I.len_u(sx2, 0), I.len_u(sy2, 0))
      +f12 : U32 = f1
      +f22 : U32 = f2
      km(p, KCon{DLz2b{samehd, sx2, sy2, f12, f22, a1, a2, xi, yi, ctx,
                       fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DLz2b{True{}, sx, sy, f1, f2, a1, a2, xi, yi, ctx, fu},
                   k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DLzA{sx, sy, f1, f2, a1, a2, xi, yi, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DLz2b{False{}, sx, sy, f1, f2, a1, a2, xi, yi, ctx, fu},
                   k} Tuple{Tuple{Tuple{ex, nx}, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      # not the same spine head: Lean's lazy_delta_reduction unfolds the
      # taller definition one step at a time (cancel p q vs cancelAux fuel
      # p q [] [] is one unfold of cancel); the yes-only probe does that
      # before both sides are evaluated
      +n2 : U32 = nx
      +x2 : U32 = xi
      +y2 : U32 = yi
      km(p, KCon{LZ0{x2, y2, 256, cx9},
                 KCon{KZr{}, KCon{KRb{n2, wm},
                      KCon{DLzD{f1, f2, a1, a2, x2, y2, cx9, fu}, k}}}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop((ex, n2), ri))
    case 1n+p KCon{DLzD{f1, f2, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{DLzD2{L.tri_is_yes(t), f1, f2, a1, a2, xi, yi, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DLzD2{True{}, f1, f2, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{DLzD2{False{}, f1, f2, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      km(p, KCon{DWhd{f1, cx9}, KCon{DAq2{f1, f2, a1, a2, xi, yi, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # args-first loop: walk both argument lists, defeq each pair
    case 1n+p KCon{DLzA{Nil{}, Nil{}, f1, f2, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{DLzA{Con{xh, xt}, Con{yh, yt}, f1, f2, a1, a2, xi, yi,
                        ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +xh2 : U32 = xh
      +yh2 : U32 = yh
      km(p, KCon{DLzA0{U32.is_eq(xh2, yh2), xh2, yh2, xt, yt, f1, f2, a1, a2,
                       xi, yi, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # the same node: equal (Lean's quick_is_def_eq), nothing to evaluate
    case 1n+p KCon{DLzA0{True{}, xh, yh, xt, yt, f1, f2, a1, a2, xi, yi,
                         ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DLzA{xt, yt, f1, f2, a1, a2, xi, yi, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # Lean compares an argument pair lazily (is_def_eq: whnf_core, then
    # lazy delta): LD, which evaluates only what the lazy steps leave open
    case 1n+p KCon{DLzA0{False{}, xh, yh, xt, yt, f1, f2, a1, a2, xi, yi,
                         ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +c2 : List<&2, U32> = ctx
      +f9 : U32 = fu
      km(p, KCon{LD{xh, yh, c2, f9},
                 KCon{DLzAk{xt, yt, f1, f2, a1, a2, xi, yi, c2, f9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DLzAx{xt, yt, yh, f1, f2, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +wx : U32 = ri
      +yh2 : U32 = yh
      km(p, KCon{DWhd{yh2, cx9},
                 KCon{DLzAy{xt, yt, wx, f1, f2, a1, a2, xi, yi, cx9, fu},
                      k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DLzAy{xt, yt, wx, f1, f2, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +wy : U32 = ri
      +wx2 : U32 = wx
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DSub{U32.is_eq((fu - 1 : U32), 4294967295),
                      U32.is_eq(wx2, wy), wx2, wy, c2, (fu - 1 : U32)},
                 KCon{DLzAk{xt, yt, f1, f2, a1, a2, xi, yi, c2, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DLzAk{xt, yt, f1, f2, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +r2 : U32 = ri
      km(p, KCon{DLzAk2{L.tri_is_yes(t), xt, yt, f1, f2, a1, a2, xi, yi,
                        ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, r2))
    case 1n+p KCon{DLzAk2{True{}, xt, yt, f1, f2, a1, a2, xi, yi, ctx, fu},
                   k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DLzA{xt, yt, f1, f2, a1, a2, xi, yi, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DLzAk2{False{}, xt, yt, f1, f2, a1, a2, xi, yi, ctx, fu},
                   k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      # an argument did not settle -> unchanged "whnf the functions" path
      km(p, KCon{DWhd{f1, cx9}, KCon{DAq2{f1, f2, a1, a2, xi, yi, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DAq1{f1, f2, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +f12 : U32 = f1
      +f22 : U32 = f2
      km(p, KCon{DAqGo{U32.is_eq(f12, f22) || L.tri_is_yes(t), f12, f22,
                       a1, a2, xi, yi, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DAqGo{True{}, f1, f2, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +a12 : U32 = a1
      km(p, KCon{DAqH1{a12, a2, xi, yi, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kspine_tin(fs, a12, ri))
    case 1n+p KCon{DAqH1{a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +a22 : U32 = a2
      km(p, KCon{DAqH2{hd, sargs, a1, a22, xi, yi, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, a22, ri))
    case 1n+p KCon{DAqH2{h1, s1, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +ha : T.Ex = h1
      +hb : T.Ex = hd
      +sa : List<&2, U32> = s1
      +sb : List<&2, U32> = sargs
      +gate : Bool = Bool.not(U32.is_eq(kcn(ha), 4294967295))
                     && U32.is_eq(kcn(ha), kcn(hb))
                     && L.tri_is_yes(I.eq_lvls(kcus(ha), kcus(hb), lnt))
                     && U32.is_eq(I.len_u(sa, 0), I.len_u(sb, 0))
      km(p, KCon{DAqH3{gate, sa, sb, a1, a2, xi, yi, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DAqH3{True{}, s1, s2, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DCgL{s1, s2, a1, a2, xi, yi, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DAqH3{False{}, s1, s2, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      # the functions agree, the last arguments differ in head: compare
      # them lazily (LD), then as the argument of this application
      km(p, KCon{LD{a1, a2, cx9, fu}, KCon{DAq6{L.TYes{}, xi, yi, cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # congruence worklist
    case 1n+p KCon{DCgL{Nil{}, Nil{}, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DAq6{L.TYes{}, xi, yi, ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kmtri(fs, L.TYes{}))
    case 1n+p KCon{DCgL{Con{x, xt}, Con{y, yt}, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      km(p, KCon{DCgS1{x2, y, xt, yt, a1, a2, xi, yi, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, x2, ri))
    case 1n+p KCon{DCgL{xs, ys, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      km(p, KCon{DWhd{a1, cx9}, KCon{DAq4{L.TYes{}, a1, a2, xi, yi, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DCgS1{x, y, xt, yt, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +y2 : U32 = y
      km(p, KCon{DCgS2{hd, sargs, x, y2, xt, yt, a1, a2, xi, yi, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, y2, ri))
    case 1n+p KCon{DCgS2{h1, s1, x, y, xt, yt, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +ha : T.Ex = h1
      +hb : T.Ex = hd
      +sa : List<&2, U32> = s1
      +sb : List<&2, U32> = sargs
      +gate : Bool = Bool.not(U32.is_eq(kcn(ha), 4294967295))
                     && U32.is_eq(kcn(ha), kcn(hb))
                     && L.tri_is_yes(I.eq_lvls(kcus(ha), kcus(hb), lnt))
                     && U32.is_eq(I.len_u(sa, 0), I.len_u(sb, 0))
      # bail (abandon) when both are applications and NEITHER head is a
      # constructor: comparing would need unfolding two defined functions
      +nb : Bool = U32.is_gt(I.len_u(sa, 0), 0) && U32.is_gt(I.len_u(sb, 0), 0)
                   && Bool.not(I.meta_is_ctor(R.get(I.Meta, 64n, mt, kcn(ha),
                                                    I.MNone{})))
                   && Bool.not(I.meta_is_ctor(R.get(I.Meta, 64n, mt, kcn(hb),
                                                    I.MNone{})))
      km(p, KCon{DCgS3{gate, nb, sa, sb, x, y, xt, yt, a1, a2, xi, yi, ctx,
                       fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # same head: expand the argument pairs onto the worklist
    case 1n+p KCon{DCgS3{True{}, nb, s1, s2, x, y, xt, yt, a1, a2, xi, yi,
                         ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DCgL{kapp_u(s1, xt), kapp_u(s2, yt), a1, a2, xi, yi, ctx,
                      fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # different heads. Two APPLICATIONS with different heads would need
    # unfolding to compare -- possibly evaluating their arguments (e.g.
    # `P (slow n) =?= Q (slow m)`) -- so abandon the attempt and let the
    # unchanged path decide. Otherwise it is an atomic-ish leaf.
    case 1n+p KCon{DCgS3{False{}, nb, s1, s2, x, y, xt, yt, a1, a2, xi, yi,
                         ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DCgS4{nb, x, y, xt, yt, a1, a2, xi, yi, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DCgS4{True{}, x, y, xt, yt, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{Tuple{ex, nx}, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      # two applications with different non-constructor heads: the lazy
      # delta probe first, the full path if it does not settle
      +n2 : U32 = nx
      km(p, KCon{LZ0{x, y, 256, cx9},
                 KCon{KZr{}, KCon{KRb{n2, wm},
                                  KCon{DCgLz{xt, yt, a1, a2, xi, yi, cx9,
                                             fu}, k}}}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop((ex, n2), ri))
    # leaf: full whnf both sides (defeq's precondition), then defeq
    case 1n+p KCon{DCgS4{False{}, x, y, xt, yt, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +x2 : U32 = x
      km(p, KCon{DWhd{x2, cx9}, KCon{DCgW1{y, xt, yt, a1, a2, xi, yi, cx9, fu},
                                k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DCgW1{y, xt, yt, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +wx : U32 = ri
      +y2 : U32 = y
      km(p, KCon{DWhd{y2, cx9}, KCon{DCgW2{wx, xt, yt, a1, a2, xi, yi, cx9, fu},
                                k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DCgW2{wx, xt, yt, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +wy : U32 = ri
      +wx2 : U32 = wx
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DSub{U32.is_eq((fu - 1 : U32), 4294967295),
                      U32.is_eq(wx2, wy), wx2, wy, c2, (fu - 1 : U32)},
                 KCon{DCgK{xt, yt, a1, a2, xi, yi, c2, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DCgK{xt, yt, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{DCgK2{L.tri_is_yes(t), xt, yt, a1, a2, xi, yi, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DCgK2{True{}, xt, yt, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DCgL{xt, yt, a1, a2, xi, yi, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DCgK2{False{}, xt, yt, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      km(p, KCon{DWhd{a1, cx9}, KCon{DAq4{L.TYes{}, a1, a2, xi, yi, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # immediate functions differ: try args-first (same spine-head constant,
    # arguments convertible) BEFORE unfolding. Collect both spines; if that
    # does not settle it, fall back to the unchanged "whnf the functions"
    # path. Confined to this branch so the common deep comparisons (functions
    # structurally equal -> DAqGo{True}) pay no spine-collection overhead.
    case 1n+p KCon{DAqGo{False{}, f1, f2, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +xi2 : U32 = xi
      km(p, KCon{DLz1{f1, f2, a1, a2, xi, yi, ctx, fu}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, xi2, ri))
    case 1n+p KCon{DAq2{f1, f2, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +f22 : U32 = f2
      km(p, KCon{DWhd{f22, cx9}, KCon{DAq3{ri, f1, f22, a1, a2, xi, yi, cx9,
                                      fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DAq3{w1, f1, f2, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +f3 : U32 = fu
      +w1b : U32 = w1
      +r2 : U32 = ri
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DSub{U32.is_eq((f3 - 1 : U32), 4294967295),
                      U32.is_eq(f1, f2), w1b, r2, c2, (f3 - 1 : U32)},
                 KCon{DAq3b{a1, a2, xi, yi, c2, f3}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DAq3b{a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +a12 : U32 = a1
      km(p, KCon{DWhd{a12, cx9}, KCon{DAq4{t, a12, a2, xi, yi, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DAq4{d1, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +a22 : U32 = a2
      km(p, KCon{DWhd{a22, cx9}, KCon{DAq5{d1, ri, a1, a22, xi, yi, cx9, fu},
                                 k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DAq5{d1, w3, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +f2 : U32 = fu
      +w3b : U32 = w3
      +r2 : U32 = ri
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295),
                      U32.is_eq(a1, a2), w3b, r2, c2, (f2 - 1 : U32)},
                 KCon{DAq6{d1, xi, yi, c2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DAq6{d1, xi, yi, ctx}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      +x2 : U32 = xi
      km(p, KCon{DIr1{I.tri_and(d1, t), x2, yi, ctx}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, x2, ri))
    # -- Nat/Nat, Str/Str --
    case 1n+p KCon{DEy{T.ENat{d1}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.ENat{d2}}}, ri}:
      +da : List<&2, U32> = d1
      +db : List<&2, U32> = d2
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.pick_tri(I.dec_le(da, db) && I.dec_le(db, da),
                              L.TYes{}, L.TNo{})))
    case 1n+p KCon{DEy{T.EStr{d1}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EStr{d2}}}, ri}:
      # different literals are different strings (Lean's quick_is_def_eq)
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.pick_tri(I.eq_u32s(d1, d2), L.TYes{}, L.TNo{})))
    # -- function eta, lambda on the left --
    case 1n+p KCon{DEy{T.ELam{n1, t1, b1, i1}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +y2 : U32 = yi
      +c2 : List<&2, U32> = ctx
      km(p, KCon{kev(WP{0, 0, 1, 0, Nil{}, Nil{}, 2000000}, y2),
                 KCon{DEtL1{t1, b1, c2, fu}, KCon{DEtX{xi, y2, c2}, k}}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, y2, ri))
    case 1n+p KCon{DEtL1{t1, b1, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DEtL2{ri, t1, b1, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kalloc(fs, T.EBVar{0}, hcb))
    case 1n+p KCon{DEtL2{ly, t1, b1, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DEtL3{t1, b1, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kalloc(fs, T.EApp{ly, ri}, hcb))
    # the body against `y #0` by is_def_eq (lazy), as Lean's
    # try_eta_expansion_core compares t with the eta-expanded s
    case 1n+p KCon{DEtL3{t1, b1, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +b12 : U32 = b1
      +r2 : U32 = ri
      +f2 : U32 = fu
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295),
                      U32.is_eq(b12, r2), b12, r2, Con{t1, ctx},
                      (f2 - 1 : U32)},
                 KCon{DEtL6{}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DEtL4{ap, t1, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +a2 : U32 = ap
      km(p, KCon{DWhd{a2, cx9}, KCon{DEtL5{ri, t1, cx9, fu}, k}}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DEtL5{w1, t1, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +f2 : U32 = fu
      +w2 : U32 = w1
      +r2 : U32 = ri
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295), False{}, w2,
                      r2, Con{t1, ctx}, (f2 - 1 : U32)},
                 KCon{DEtL6{}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DEtL6{}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, t))
    # -- function eta, lambda on the right --
    case 1n+p KCon{DEy{xn, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.ELam{n2, t2, b2, i2}}}, ri}:
      +x2 : U32 = xi
      +c2 : List<&2, U32> = ctx
      km(p, KCon{kev(WP{0, 0, 1, 0, Nil{}, Nil{}, 2000000}, x2),
                 KCon{DEtR1{t2, b2, c2, fu}, KCon{DEtX{x2, yi, c2}, k}}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, x2, ri))
    case 1n+p KCon{DEtR1{t2, b2, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DEtR2{ri, t2, b2, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kalloc(fs, T.EBVar{0}, hcb))
    case 1n+p KCon{DEtR2{lx, t2, b2, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DEtR3{t2, b2, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kalloc(fs, T.EApp{lx, ri}, hcb))
    case 1n+p KCon{DEtR3{t2, b2, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +a2 : U32 = ri
      +b22 : U32 = b2
      +f2 : U32 = fu
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295),
                      U32.is_eq(a2, b22), a2, b22, Con{t2, ctx},
                      (f2 - 1 : U32)},
                 KCon{DEtL6{}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DEtR4{ap, t2, b2, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +b22 : U32 = b2
      km(p, KCon{DWhd{b22, cx9}, KCon{DEtR5{ri, t2, cx9, fu}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DEtR5{w1, t2, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +f2 : U32 = fu
      +w2 : U32 = w1
      +r2 : U32 = ri
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295), False{}, w2,
                      r2, Con{t2, ctx}, (f2 - 1 : U32)},
                 KCon{DEtL6{}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    # -- a Nat literal against a numeral in constructor form --
    # (the other side is the lazy loop's stalled term: no whnf here)
    case 1n+p KCon{DEy{T.ENat{d}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +y2 : U32 = yi
      km(p, KCon{DNtL2{d, y2, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kfetch(fs, y2, ri))
    case 1n+p KCon{DNtL1{d, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{DNtL2{d, r2, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{DNtL2{d, wy, ctx, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      km(p, KCon{DNtL3{I.is_nat_lit(node), d, wy, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DNtL3{True{}, d, wy, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DNtL4{True{}, wy, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kalloc(fs, T.ENat{d}, hcb))
    # literal 0 expands to the bare constructor Nat.zero, which is already
    # in whnf, so the comparison's NO is trusted; a successor expansion
    # `Nat.succ (lit)` is not (whnf folds it back to a literal), so its NO
    # stays undecided
    case 1n+p KCon{DNtL3{False{}, d, wy, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +d2 : List<&2, U32> = d
      km(p, KCon{DNtL4{I.dec_is_zero(d2), wy, ctx, fu}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb,
         knatexp(hcb, fs, d2, R.get(U32, 64n, qtt, 3, 4294967295),
                 R.get(U32, 64n, qtt, 4, 4294967295)))
    # the constructor form against the other side STRUCTURALLY (DEx, not
    # DSub: whnf_core folds `Nat.succ lit` back into the literal)
    case 1n+p KCon{DNtL4{islit, wy, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +f2 : U32 = fu
      +r2 : U32 = ri
      +w2 : U32 = wy
      km(p, KCon{DEx{r2, w2, ctx, (f2 - 1 : U32)}, KCon{DNtL5{islit}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{DNtL5{islit}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      +t2 : L.Tri = t
      +i2 : Bool = islit
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.pick_tri(i2, t2,
                              L.pick_tri(L.tri_is_no(t2), L.TUnk{}, t2))))
    case 1n+p KCon{DEy{xn, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.ENat{d}}}, ri}:
      +x2 : U32 = xi
      km(p, KCon{DNtR2{d, x2, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kfetch(fs, x2, ri))
    case 1n+p KCon{DNtR1{d, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{DNtR2{d, r2, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{DNtR2{d, wx, ctx, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      km(p, KCon{DNtR3{I.is_nat_lit(node), d, wx, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DNtR3{True{}, d, wx, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DNtR4{True{}, wx, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kalloc(fs, T.ENat{d}, hcb))
    # literal 0 expands to the bare constructor Nat.zero, which is already
    # in whnf, so the comparison's NO is trusted; a successor expansion
    # `Nat.succ (lit)` is not (whnf folds it back to a literal), so its NO
    # stays undecided
    case 1n+p KCon{DNtR3{False{}, d, wx, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +d2 : List<&2, U32> = d
      km(p, KCon{DNtR4{I.dec_is_zero(d2), wx, ctx, fu}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb,
         knatexp(hcb, fs, d2, R.get(U32, 64n, qtt, 3, 4294967295),
                 R.get(U32, 64n, qtt, 4, 4294967295)))
    case 1n+p KCon{DNtR4{islit, wx, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +f2 : U32 = fu
      +r2 : U32 = ri
      +w2 : U32 = wx
      km(p, KCon{DEx{w2, r2, ctx, (f2 - 1 : U32)}, KCon{DNtL5{islit}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, w2, 0))
    # -- a string literal against anything else: its constructor form,
    #    reduced, against the other side (try_string_lit_expansion; the
    #    other side is already in whnf, so a String.ofList application has
    #    become a String constructor). YES is trusted; NO stays undecided --
    case 1n+p KCon{DEy{T.EStr{d}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DStr0{kstr_ok(qtt), True{}, d, yi, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DEy{xn, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EStr{d}}}, ri}:
      km(p, KCon{DStr0{kstr_ok(qtt), False{}, d, xi, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DStr0{False{}, left, d, other, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TUnk{}))
    case 1n+p KCon{DStr0{True{}, left, d, other, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DStr1{left, other, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, ktin_of(kstrexp(fs, d, qtt, hcb)))
    case 1n+p KCon{DStr1{left, other, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +r2 : U32 = ri
      km(p, KCon{DWhd{r2, cx9}, KCon{DStr2{left, other, cx9, fu}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, r2))
    case 1n+p KCon{DStr2{left, other, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +w : U32 = ri
      +o2 : U32 = other
      +f2 : U32 = fu
      +l2 : Bool = left
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295),
                      U32.is_eq(w, o2), S.pick(l2, w, o2), S.pick(l2, o2, w),
                      ctx, (f2 - 1 : U32)},
                 KCon{DStr3{}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DStr3{}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.pick_tri(L.tri_is_yes(t), L.TYes{}, L.TUnk{})))
    # -- projection/projection: same (type,index) -> compare structures by
    #    defeq (args-first makes same-head structure arguments cheap), YES
    #    answers YES; otherwise fall back to the catch-all below unchanged --
    case 1n+p KCon{DEy{T.EProj{tn1, idx1, s1}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EProj{tn2, idx2, s2}}}, ri}:
      +tn1r : U32 = tn1
      +idx1r : U32 = idx1
      +s1b : U32 = s1
      +tn2r : U32 = tn2
      +idx2r : U32 = idx2
      +s2b : U32 = s2
      +xn2 : T.Ex = T.EProj{tn1r, idx1r, s1b}
      +yn2 : T.Ex = T.EProj{tn2r, idx2r, s2b}
      +c2 : List<&2, U32> = ctx
      +sp : Bool = U32.is_eq(tn1r, tn2r) && U32.is_eq(idx1r, idx2r)
      km(p, KCon{DPjDecide{sp, xn2, yn2, xi, yi, c2, fu}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # sp true: compare the two structures by defeq, YES answers YES
    case 1n+p KCon{DPjDecide{True{}, xn, yn, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +xn2 : T.Ex = xn
      +yn2 : T.Ex = yn
      +s1b : U32 = kproj_s(xn2)
      +s2b : U32 = kproj_s(yn2)
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DSub{U32.is_eq((fu - 1 : U32), 4294967295),
                      U32.is_eq(s1b, s2b), s1b, s2b, c2, (fu - 1 : U32)},
                 KCon{DPjK{xn2, yn2, xi, yi, c2, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    # sp false: not the same projection -> catch-all unchanged
    case 1n+p KCon{DPjDecide{False{}, xn, yn, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = xi
      km(p, KCon{DC1{xn, yn, x2, yi, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kspine_tin(fs, x2, ri))
    case 1n+p KCon{DPjK{xn, yn, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{DPjK2{L.tri_is_yes(t), xn, yn, xi, yi, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DPjK2{True{}, xn, yn, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{DPjK2{False{}, xn, yn, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +xn2 : T.Ex = xn
      km(p, KCon{DWhd{kproj_s(xn2), cx9}, KCon{DPjW1{xn2, yn, xi, yi, cx9, fu},
                                          k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DPjW1{xn, yn, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +yn2 : T.Ex = yn
      +w1 : U32 = ri
      km(p, KCon{DWhd{kproj_s(yn2), cx9}, KCon{DPjW2{w1, xn, yn2, xi, yi, cx9,
                                                fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DPjW2{w1, xn, yn, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +w2 : U32 = ri
      +w1b : U32 = w1
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DSub{U32.is_eq((fu - 1 : U32), 4294967295),
                      U32.is_eq(w1b, w2), w1b, w2, c2, (fu - 1 : U32)},
                 KCon{DPjW3{xn, yn, xi, yi, c2, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DPjW3{xn, yn, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{DPjW4{L.tri_is_yes(t), xn, yn, xi, yi, ctx, fu}, k}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DPjW4{True{}, xn, yn, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{DPjW4{False{}, xn, yn, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = xi
      km(p, KCon{DC1{xn, yn, x2, yi, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, x2, ri))
    # -- the structural catch-all: structure eta, else denial/delta/irrel --
    case 1n+p KCon{DEy{xn, xi, yi, ctx, fu}, k} Tuple{Tuple{fs, MX{yn}}, ri}:
      +x2 : U32 = xi
      km(p, KCon{DC1{xn, yn, x2, yi, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kspine_tin(fs, x2, ri))
    case 1n+p KCon{DC1{xn, yn, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +y2 : U32 = yi
      km(p, KCon{DC2x{xn, yn, hd, sargs, xi, y2, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, y2, ri))
    case 1n+p KCon{DC2x{xn, yn, hx, sx, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +hxl : T.Ex = hx
      +hyr : T.Ex = hd
      +swap : Bool = Bool.not(I.meta_is_ctor(
                       R.get(I.Meta, 64n, mt, I.const_nm2(hxl),
                             I.MNone{})))
                     && I.meta_is_ctor(R.get(I.Meta, 64n, mt,
                                             I.const_nm2(hyr), I.MNone{}))
      +hdp : T.Ex = I.pick_exx(swap, hyr, hxl)
      +cmi : I.Meta = R.get(I.Meta, 64n, mt, I.const_nm2(hdp), I.MNone{})
      +sx2 : List<&2, U32> = sx
      +sy2 : List<&2, U32> = sargs
      +xn2 : T.Ex = xn
      +yn2 : T.Ex = yn
      +xi2 : U32 = xi
      +yi2 : U32 = yi
      # only a fully applied constructor (Lean's try_eta_struct_core): a
      # partial `mk a` vs `y` would expand `y` to `mk (y.0) ..` forever
      +full : Bool = U32.is_eq(I.len_u(pick_us(swap, sy2, sx2), 0),
                               (I.meta_p(cmi) + I.meta_nf(cmi) : U32))
      +cboth : Bool = I.meta_is_ctor(R.get(I.Meta, 64n, mt, I.const_nm2(hxl),
                                           I.MNone{}))
                      && I.meta_is_ctor(R.get(I.Meta, 64n, mt,
                                              I.const_nm2(hyr), I.MNone{}))
      km(p, KCon{DCGo{I.meta_is_ctor(cmi) && full && Bool.not(cboth)
                      && I.meta_is_ind(R.get(I.Meta, 64n, mt,
                                             I.meta_ind(cmi), I.MNone{})),
                      S.pick(swap, yi2, xi2), S.pick(swap, xi2, yi2),
                      I.pick_exx(swap, yn2, xn2),
                      I.pick_exx(swap, xn2, yn2),
                      hdp, I.pick_exx(swap, hxl, hyr),
                      pick_us(swap, sy2, sx2), pick_us(swap, sx2, sy2),
                      I.meta_p(cmi), I.meta_nf(cmi), I.meta_ind(cmi), ctx,
                      fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # structure eta applies: build `mk (p.0) .. (p.(n-1))` and compare
    case 1n+p KCon{DCGo{True{}, pxi, pyi, pxn, pyn, hd, hdy, spx, spy, cp,
                        cnf, cind, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DCe1{I.take_u(spx, cp, Nil{}), cnf, cind, pyi, pxi, ctx,
                      fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kalloc(fs, hd, hcb))
    case 1n+p KCon{DCe1{tk, cnf, cind, pyi, pxi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +f2 : U32 = fu
      +p2 : U32 = pxi
      km(p, KCon{DSub2{p2, ctx, (f2 - 1 : U32)}, KCon{DCe3{}, k}}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         ktin_of(kprojb(hcb, U32.to_nat(cnf), 0, cind, pyi,
                        kapargs(hcb, tk, (fs, ri)))))
    case 1n+p KCon{DSub2{pxi, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +f2 : U32 = fu
      +p2 : U32 = pxi
      +r2 : U32 = ri
      km(p, KCon{DSub{U32.is_eq(f2, 4294967295), False{}, p2, r2, ctx,
                      f2}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DCe3{}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      +t2 : L.Tri = t
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.pick_tri(L.tri_is_no(t2), L.TUnk{}, t2)))
    # no structure eta: rigidity, denial, delta retry, irrelevance
    case 1n+p KCon{DCGo{False{}, pxi, pyi, pxn, pyn, hd, hdy, spx, spy,
                        cp, cnf, cind, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +px2 : T.Ex = pxn
      +hd2 : T.Ex = hd
      +cx : Bool = krigid(px2, hd2) || kctor_headed(px2, hd2, mt)
      km(p, KCon{DCr1{cx, px2, hd2, spx, pxi, pyi, pyn, hdy, spy, ctx,
                      fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DCr1{True{}, pxn, hd, spx, pxi, pyi, pyn, hdy, spy,
                        ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DCr3{pxi, pyi, pyn, hdy, spy, ctx, fu}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DCr1{False{}, pxn, hd, spx, pxi, pyi, pyn, hdy, spy,
                        ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +h2 : T.Ex = hd
      +mi : I.Meta = R.get(I.Meta, 64n, mt, I.const_nm2(h2), I.MNone{})
      +s2 : List<&2, U32> = spx
      +pp : U32 = I.meta_p(mi)
      +ni : U32 = I.meta_k(mi)
      +mn : U32 = I.meta_n(mi)
      +nmj : U32 = (pp + 1 + mn + ni : U32)
      +ok0 : Bool = I.meta_is_rec(mi) && U32.is_gt(I.len_u(s2, 0), nmj)
      +c2 : List<&2, U32> = ctx
      km(p, KCon{RSGo{ok0, I.nth_u(s2, nmj, 4294967295), pp, ni, mn,
                      I.meta_kf(mi), I.meta_rcty(mi), I.meta_ind(mi), s2, c2},
                 KCon{DCr2{False{}, pxi, pyi, pyn, hdy, spy, c2, fu},
                      k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DCr2{cx, pxi, pyi, pyn, hdy, spy, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      # ri is rec_stuck(px): 1 stuck, 0 not; cx was the cheap half
      km(p, KCon{DCr2b{Bool.or(cx, U32.is_eq(ri, 1)), pxi, pyi, pyn, hdy,
                       spy, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DCr2b{True{}, pxi, pyi, pyn, hdy, spy, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DCr3{pxi, pyi, pyn, hdy, spy, ctx, fu}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DCr2b{False{}, pxi, pyi, pyn, hdy, spy, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DRg1{False{}, pxi, pyi, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DCr3{pxi, pyi, pyn, hdy, spy, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +py2 : T.Ex = pyn
      +hy2 : T.Ex = hdy
      km(p, KCon{DCr3Go{krigid(py2, hy2) || kctor_headed(py2, hy2, mt),
                        py2, hy2, spy, pxi, pyi, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DCr3Go{True{}, pyn, hdy, spy, pxi, pyi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DRg1{True{}, pxi, pyi, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DCr3Go{False{}, pyn, hdy, spy, pxi, pyi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +h2 : T.Ex = hdy
      +mi : I.Meta = R.get(I.Meta, 64n, mt, I.const_nm2(h2), I.MNone{})
      +s2 : List<&2, U32> = spy
      +pp : U32 = I.meta_p(mi)
      +ni : U32 = I.meta_k(mi)
      +mn : U32 = I.meta_n(mi)
      +nmj : U32 = (pp + 1 + mn + ni : U32)
      +c2 : List<&2, U32> = ctx
      km(p, KCon{RSGo{I.meta_is_rec(mi)
                      && U32.is_gt(I.len_u(s2, 0), nmj),
                      I.nth_u(s2, nmj, 4294967295), pp, ni, mn,
                      I.meta_kf(mi), I.meta_rcty(mi), I.meta_ind(mi), s2, c2},
                 KCon{DCr5{pxi, pyi, c2, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DCr5{pxi, pyi, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DRg1{U32.is_eq(ri, 1), pxi, pyi, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    # the rigid denial
    case 1n+p KCon{DRg1{False{}, pxi, pyi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DDl1{False{}, pxi, pyi, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DRg1{True{}, pxi, pyi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = pxi
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DTy1{c2}, KCon{DRg2{x2, pyi, c2, fu}, k}}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, x2, ri))
    case 1n+p KCon{DRg2{pxi, pyi, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +r2 : U32 = ri
      km(p, KCon{kslev(r2, cx9, 2000000),
                 KCon{DRg3{Bool.not(U32.is_eq(r2, 4294967295)), pxi, pyi,
                           cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{DRg3{rtok, pxi, pyi, ctx, fu}, k}
         Tuple{Tuple{fs, MLn{u}}, ri}:
      km(p, KCon{DDl1{rtok && L.tri_is_no(L.ln_is_zero(u)), pxi, pyi, ctx,
                      fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # dq_or_delta: TNo goes straight to irrelevance; TUnk retries after one
    # reduction of each side
    case 1n+p KCon{DDl1{True{}, pxi, pyi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = pxi
      km(p, KCon{DIr1{L.TNo{}, x2, pyi, ctx}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kspine_tin(fs, x2, ri))
    case 1n+p KCon{DDl1{False{}, pxi, pyi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +x2 : U32 = pxi
      km(p, KCon{DWhd{x2, cx9}, KCon{DDl2{pyi, x2, cx9}, k}}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DDl2{pyi, pxi, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +y2 : U32 = pyi
      km(p, KCon{DWhd{y2, cx9}, KCon{DDl3{ri, pxi, y2, cx9}, k}}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DDl3{w1, pxi, pyi, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +w2 : U32 = w1
      +r2 : U32 = ri
      km(p, KCon{DDl4{pxi, pyi, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, keq_lists_tin(fs, Con{w2, Nil{}}, Con{r2, Nil{}}, lnt))
    case 1n+p KCon{DDl4{pxi, pyi, ctx}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      +x2 : U32 = pxi
      km(p, KCon{DIr1{t, x2, pyi, ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kspine_tin(fs, x2, ri))
    # rec_stuck
    case 1n+p KCon{RSGo{False{}, maj, pp, ni, mn, kf, rcty, ind, sargs, ctx},
                   k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, 0))
    case 1n+p KCon{RSGo{True{}, maj, pp, ni, mn, kf, rcty, ind, sargs, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +m2 : U32 = maj
      km(p, KCon{DWhd{m2, cx9}, KCon{RS2{pp, ni, mn, kf, rcty, ind, sargs, cx9},
                                k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{RS2{pp, ni, mn, kf, rcty, ind, sargs, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{RS3{r2, pp, ni, mn, kf, rcty, ind, sargs, ctx}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{RS3{wm2, pp, ni, mn, kf, rcty, ind, sargs, ctx}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
      +w2 : U32 = wm2
      km(p, KCon{RS4{node, pp, ni, mn, kf, rcty, ind, sargs, ctx}, k}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, w2, ri))
    case 1n+p KCon{RS4{mn2, pp, ni, mn, kf, rcty, ind, sargs, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, sargs2}}, ri}:
      +m2 : T.Ex = mn2
      +h2 : T.Ex = hd
      +cmi2 : I.Meta = R.get(I.Meta, 64n, mt, I.const_nm2(h2), I.MNone{})
      +uind2 : I.Meta = R.get(I.Meta, 64n, mt, ind, I.MNone{})
      +k2 : U32 = kf
      km(p, KCon{RSK{U32.is_eq(k2, 1),
                     (krigid(m2, h2)
                      && Bool.not(I.meta_is_ctor(cmi2)))
                     && Bool.not(I.meta_is_ind(uind2)
                                 && U32.is_eq(I.meta_nf(uind2), 0)),
                     pp, ni, mn, rcty, sargs, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{RSK{False{}, base, pp, ni, mn, rcty, sargs, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kkeep(fs, S.pick(base, 1, 0)))
    case 1n+p KCon{RSK{True{}, base, pp, ni, mn, rcty, sargs, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +p2 : U32 = pp
      +r2 : U32 = rcty
      +s2 : List<&2, U32> = sargs
      km(p, KCon{WPlE{r2, I.take_u(s2, p2, Nil{}), cx9},
                 KCon{RS5{base, p2, ni, mn, s2, cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, ri))
    case 1n+p KCon{RS5{base, pp, ni, mn, sargs, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{RS6{U32.is_ne(r2, 4294967295), base, pp, ni, mn, sargs, ctx},
                 k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kspine_tin(fs, S.pick(U32.is_ne(r2, 4294967295), r2, 0), 0))
    case 1n+p KCon{RS6{pok, base, pp, ni, mn, sargs, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, sargs2}}, ri}:
      +p2 : U32 = pp
      +s2 : List<&2, U32> = sargs
      km(p, KCon{KI0{I.skip_u(sargs2, p2),
                     I.take_u(I.skip_u(s2, (p2 + 1 + mn : U32)), ni,
                              Nil{}), L.TYes{}, ctx},
                 KCon{RS7{base, pok}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{RS7{base, pok}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      +b2 : Bool = base
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kkeep(fs, S.pick(Bool.and(b2,
                                   Bool.and(pok, L.tri_is_no(t))), 1,
                          0)))
    # k_idx_cmp: pairwise with the constant denial
    case 1n+p KCon{KI0{Nil{}, Nil{}, acc, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, acc))
    case 1n+p KCon{KI0{Nil{}, Con{b, tb}, acc, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TUnk{}))
    case 1n+p KCon{KI0{Con{a, ta}, Nil{}, acc, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TUnk{}))
    case 1n+p KCon{KI0{Con{a, ta}, Con{b, tb}, acc, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +a2 : U32 = a
      km(p, KCon{KI1{a2, b, ta, tb, acc, ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kfetch(fs, a2, ri))
    case 1n+p KCon{KI1{a, b, ta, tb, acc, ctx}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +b2 : U32 = b
      km(p, KCon{KI2{node, a, b2, ta, tb, acc, ctx}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kfetch(fs, b2, 0))
    case 1n+p KCon{KI2{an, a, b, ta, tb, acc, ctx}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
      +an2 : T.Ex = an
      +bn2 : T.Ex = node
      +n1 : U32 = I.const_nm2(an2)
      +n2x : U32 = I.const_nm2(bn2)
      +t12 : U32 = R.get(U32, 64n, nt, n1, 4294967295)
      +t22 : U32 = R.get(U32, 64n, nt, n2x, 4294967295)
      +precond : Bool = kis_cc(an2, bn2)
                        && Bool.not(U32.is_eq(n1, n2x))
                        && U32.is_eq(R.get(U32, 64n, vt, n1, 4294967295),
                                     4294967295)
                        && U32.is_eq(R.get(U32, 64n, vt, n2x,
                                           4294967295), 4294967295)
                        && Bool.not(U32.is_eq(t12, 4294967295))
      +a2 : U32 = a
      +b2 : U32 = b
      km(p, KCon{KI3b{precond, t12, t22, a2, b2, ta, tb, acc, ctx}, k}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         keq_lists_tin(fs, Con{a2, Nil{}}, Con{b2, Nil{}}, lnt))
    case 1n+p KCon{KI3b{precond, t1, t2, a, b, ta, tb, acc, ctx}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +t3 : L.Tri = t
      +pc : Bool = precond
      km(p, KCon{KIF{L.tri_is_unk(t3) && Bool.not(pc), t3, pc, t1, t2, a, b,
                     ta, tb, acc, ctx}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{KIF{False{}, t, precond, t1, t2, a, b, ta, tb, acc, ctx},
                   k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{KIGo2{precond, t, t1, t2, ta, tb, acc, ctx}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{KIF{True{}, t, precond, t1, t2, a, b, ta, tb, acc, ctx},
                   k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +a2 : U32 = a
      km(p, KCon{DWhd{a2, cx9}, KCon{KIF2{precond, t1, t2, b, ta, tb, acc, cx9},
                                k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{KIF2{precond, t1, t2, b, ta, tb, acc, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +b2 : U32 = b
      +wa : U32 = ri
      km(p, KCon{DWhd{b2, cx9}, KCon{KIF3{wa, precond, t1, t2, ta, tb, acc, cx9},
                                k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{KIF3{wa, precond, t1, t2, ta, tb, acc, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +wb : U32 = ri
      +wa2 : U32 = wa
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DSub{False{}, U32.is_eq(wa2, wb), wa2, wb, c2, 4096},
                 KCon{KIF4{precond, t1, t2, ta, tb, acc, c2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{KIF4{precond, t1, t2, ta, tb, acc, ctx}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{KIGo2{precond, t, t1, t2, ta, tb, acc, ctx}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{KIGo2{False{}, e2, t1, t2, ta, tb, acc, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{KI0{ta, tb, I.tri_and2(e2, acc), ctx}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{KIGo2{True{}, e2, t1, t2, ta, tb, acc, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +t12 : U32 = t1
      +t22 : U32 = t2
      km(p, KCon{KI4{e2, t12, ta, tb, acc, ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb,
         keq_lists_tin(fs, Con{t12, Nil{}}, Con{t22, Nil{}}, lnt))
    case 1n+p KCon{KI4{e2, t1, ta, tb, acc, ctx}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +t12 : U32 = t1
      km(p, KCon{kslev(t12, Nil{}, 2000000),
                 KCon{KI6{e2, L.tri_is_yes(t), ta, tb, acc, ctx}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t12, ri))
    case 1n+p KCon{KI6{e2, tqy, ta, tb, acc, ctx}, k}
         Tuple{Tuple{fs, MLn{u}}, ri}:
      +d2 : L.Tri = L.pick_tri(Bool.and(tqy,
                                        L.tri_is_no(L.ln_is_zero(u))),
                               L.TNo{}, e2)
      km(p, KCon{KI0{ta, tb, I.tri_and2(d2, acc), ctx}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ---- type inference ----
    # Lean caches inferred types per expression (shared subterms of a proof
    # are checked once; km walked them as a tree). A node's type depends on
    # the context only through its first lbr(x) entries, so it is memoised
    # under (x, cid), cid the hash-consed chain of that context prefix, and
    # both are verified on a hit (keys 0x70000000 + h: type, 0x78000000 + h:
    # x | ok << 31, 0x90000000 + h: cid). A fuel-out is not memoised.
    case 1n+p KCon{ISub{xi, ctx, fu}, k} Tuple{Tuple{Tuple{ex, nx}, msg}, ri}:
      +x2 : U32 = xi
      km(p, KCon{ISubC{x2, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, klb_tin(klb_get(ex, x2, khalf(hcb)), nx))
    case 1n+p KCon{ISubC{xi, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +l : U32 = ri
      +c2 : List<&2, U32> = ctx
      +ok : Bool = U32.is_le(l, 48) && U32.is_lt(xi, 134217728)
      km(p, KCon{ISubD{ok, xi, c2, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb,
         ktin_of(kctxid(kpre_rev(S.pick(ok, l, 0), c2, Nil{}), (fs, 0), hcb)))
    case 1n+p KCon{ISubD{ok, xi, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{ISubE{ok, xi, ri, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kfl_tin(fs, hcb, 4))
    # the pair (x, cid) as one hash-consed node: its index names the pair
    # exactly (the store is canonical), so the memo is one entry, at
    # 0x70000000 + pair (infer_only: 0x98000000 + pair, its own range -- a
    # type that skipped the argument checks must never vouch for a checked
    # one); value: type | ok << 31 (0x7FFFFFFE: ill-typed)
    case 1n+p KCon{ISubE{ok, xi, cid, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +c2 : U32 = cid
      km(p, KCon{ISubF{ok, U32.is_eq(ri, 1), xi, ctx, fu}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb,
         ktin_of(khc(fs, T.EApp{xi, c2}, hcb)))
    case 1n+p KCon{ISubF{ok, io, xi, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +pk : U32 = ri
      +ok2 : Bool = ok && U32.is_lt(pk, 134217728)
      +io2 : U32 = S.pick(io, 1, 0)
      km(p, KCon{ISubF2{ok2, io2, xi, pk, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kyi_tin(fs, hcb, S.pick(ok2, pk, 0), io2))
    case 1n+p KCon{ISubF2{ok2, io, xi, pk, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +v : U32 = ri
      +v2 : U32 = U32.and(v, 2147483647)
      +o2 : Bool = ok2
      km(p, KCon{ISubM{o2 && Bool.not(U32.is_eq(v, 4294967295)), o2,
                       S.pick(U32.is_eq(v2, 2147483646), 4294967294, v2),
                       U32.is_ge(v, 2147483648), xi, ((2 * pk : U32) + io : U32),
                       ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{ISubM{True{}, cl, t, tok, xi, key, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, t, tok))
    case 1n+p KCon{ISubM{False{}, cl, t, tok, xi, key, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +f2 : U32 = fu
      +x2 : U32 = xi
      km(p, KCon{IEvGo{U32.is_eq(f2, 0), x2, ctx, f2},
                 KCon{IMemo{cl, key}, k}}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IMemo{cl, key}, k}
         Tuple{Tuple{Tuple{ex, nx}, MIR{t, ok}}, ri}:
      +t2 : U32 = t
      +ok2 : Bool = ok
      +st : Bool = cl && (U32.is_lt(t2, 2147483646)
                          || U32.is_eq(t2, 4294967294))
      +k2 : U32 = key
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir((kyi_set(st, ex, hcb, (k2 / 2 : U32), U32.and(k2, 1),
                       (S.pick(U32.is_eq(t2, 4294967294), 2147483646, t2)
                        + S.pick(ok2, 2147483648, 0) : U32)), nx),
              t2, ok2))
    case 1n+p KCon{IEvGo{True{}, xi, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, 4294967295, False{}))
    case 1n+p KCon{IEvGo{False{}, xi, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = xi
      km(p, KCon{IEv{x2, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, kfetch(fs, x2, ri))
    # -- Sort --
    case 1n+p KCon{IEv{xi, ctx, fu}, k} Tuple{Tuple{fs, MX{T.ESort{l}}}, ri}:
      +u : L.LN = L.ln_succ(R.get(L.LN, 64n, lnt, l, L.LNun{}))
      +u2 : L.LN = u
      km(p, KCon{ISrtGo{L.is_un(u2), u2}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{ISrtGo{True{}, u}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, 4294967295, False{}))
    case 1n+p KCon{ISrtGo{False{}, u}, k} Tuple{Tuple{fs, msg}, ri}:
      +nl : U32 = nlx
      km(p, KCon{IWrap{True{}}, k},
         R.set(L.LN, 64n, lnt, nl, u, L.LNun{}), (nl + 1 : U32), mt, lp,
         vt, qtt, natn, wm, nt, hcb, kalloc(fs, T.ESort{nl}, hcb))
    case 1n+p KCon{IWrap{ok}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, r2, ok))
    # -- Pi --
    case 1n+p KCon{IEv{xi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EAll{n, ty, b, bi}}}, ri}:
      +t2 : U32 = ty
      +c2 : List<&2, U32> = ctx
      +f2 : U32 = fu
      km(p, KCon{ISub{t2, c2, (f2 - 1 : U32)},
                 KCon{IAl2{t2, b, c2, f2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IAl2{ty, b, ctx, fu}, k} Tuple{Tuple{fs, MIR{t, ok}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +t2 : U32 = t
      km(p, KCon{DWhd{t2, cx9}, KCon{IAl3{ty, b, t2, ok, cx9, fu}, k}}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IAl3{ty, b, ra, raok, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{IAl3b{ty, b, ra, raok, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{IAl3b{ty, b, ra, raok, ctx, fu}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
      +t2 : U32 = ty
      +b2 : U32 = b
      +f2 : U32 = fu
      +c2 : List<&2, U32> = ctx
      km(p, KCon{ISub{b2, Con{t2, c2}, (f2 - 1 : U32)},
                 KCon{IAl4{t2, node, ra, raok, c2, f2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IAl4{ty, ka, ra, raok, ctx, fu}, k}
         Tuple{Tuple{fs, MIR{t, ok}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +t2 : U32 = t
      km(p, KCon{DWhd{t2, cx9}, KCon{IAl5{ka, ra, raok, t2, ok, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IAl5{ka, ra, raok, rb, rbok, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{IAl5b{ka, ra, raok, rb, rbok, ctx, fu}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{IAl5b{ka, ra, raok, rb, rbok, ctx, fu}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
      +ka2 : T.Ex = ka
      km(p, KCon{IAl6{ka2, node, ra, raok, rb, rbok}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, kspine_head_tin(fs, ka2, ri))
    case 1n+p KCon{IAl6{ka, kb, ra, raok, rb, rbok}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +ka2 : T.Ex = ka
      +kb2 : T.Ex = kb
      km(p, KCon{IAl7{ka2, kb2, knever_sort(ka2, hd, mt, vt, qtt), ra,
                      raok, rb, rbok}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kspine_head_tin(fs, kb2, ri))
    case 1n+p KCon{IAl7{ka, kb, nska, ra, raok, rb, rbok}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +ka2 : T.Ex = ka
      +kb2 : T.Ex = kb
      +allok : Bool = raok && rbok && I.is_sortx(ka2) && I.is_sortx(kb2)
      +bad : Bool = (raok && rbok
                     && (nska || knever_sort(kb2, hd, mt, vt, qtt)))
                    || U32.is_eq(ra, 4294967294)
                    || U32.is_eq(rb, 4294967294)
      km(p, KCon{IAlGo{allok, bad, ka2, kb2}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IAlGo{True{}, bad, ka, kb}, k} Tuple{Tuple{fs, msg}, ri}:
      +u : L.LN = L.ln_imax(R.get(L.LN, 64n, lnt, I.sort_lvl_of(ka),
                                  L.LNun{}),
                            R.get(L.LN, 64n, lnt, I.sort_lvl_of(kb),
                                  L.LNun{}))
      +u2 : L.LN = u
      km(p, KCon{ISrtGo{L.is_un(u2), u2}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IAlGo{False{}, True{}, ka, kb}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, 4294967294, False{}))
    case 1n+p KCon{IAlGo{False{}, False{}, ka, kb}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, 4294967295, False{}))
    # -- Lam --
    case 1n+p KCon{IEv{xi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.ELam{n, ty, b, bi}}}, ri}:
      +t2 : U32 = ty
      +f2 : U32 = fu
      km(p, KCon{ISub{b, Con{t2, ctx}, (f2 - 1 : U32)},
                 KCon{ILm2{n, t2, bi}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{ILm2{n, ty, bi}, k} Tuple{Tuple{fs, MIR{t, ok}}, ri}:
      km(p, KCon{ILmGo{ok, t, n, ty, bi}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{ILmGo{True{}, bty, n, ty, bi}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{IWrap{True{}}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kalloc(fs, T.EAll{n, ty, bty, bi}, hcb))
    case 1n+p KCon{ILmGo{False{}, bty, n, ty, bi}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, S.pick(U32.is_eq(bty, 4294967294), 4294967294,
                         4294967295), False{}))
    # -- BVar --
    case 1n+p KCon{IEv{xi, ctx, fu}, k} Tuple{Tuple{fs, MX{T.EBVar{i}}}, ri}:
      +i2 : U32 = i
      +ti : U32 = I.nth_u(ctx, i2, 4294967295)
      +t2 : U32 = ti
      km(p, KCon{kev(WP{0, 0, (i2 + 1 : U32), 0, Nil{}, Nil{}, 2000000}, t2),
                 KCon{IBv{Bool.not(U32.is_eq(t2, 4294967295))}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
    case 1n+p KCon{IBv{ok}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmir(fs, r2, ok))
    # -- literals --
    case 1n+p KCon{IEv{xi, ctx, fu}, k} Tuple{Tuple{fs, MX{T.ENat{d}}}, ri}:
      km(p, KCon{INatGo{U32.is_eq(natn, 4294967295)}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{INatGo{True{}}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, 4294967295, False{}))
    case 1n+p KCon{INatGo{False{}}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{IWrap{True{}}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kalloc(fs, T.EConst{natn, Nil{}}, hcb))
    # a string literal has type `String` (qtt key 10), exactly as infer.bend;
    # this was a stub that always failed, declining every declaration with a
    # string literal (String.instInhabited, panic messages, ...)
    case 1n+p KCon{IEv{xi, ctx, fu}, k} Tuple{Tuple{fs, MX{T.EStr{d}}}, ri}:
      +sn : U32 = R.get(U32, 64n, qtt, 10, 4294967295)
      km(p, KCon{IStrGo{U32.is_eq(sn, 4294967295), sn}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IStrGo{True{}, sn}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, 4294967295, False{}))
    case 1n+p KCon{IStrGo{False{}, sn}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{IWrap{True{}}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt,
         hcb, kalloc(fs, T.EConst{sn, Nil{}}, hcb))
    # -- Const --
    case 1n+p KCon{IEv{xi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EConst{n, us}}}, ri}:
      +n2 : U32 = n
      +ti : U32 = R.get(U32, 64n, nt, n2, 4294967295)
      +t2 : U32 = ti
      km(p, KCon{ICnGo{U32.is_eq(t2, 4294967295), t2,
                       R.get(List<&2, U32>, 64n, lp, n2, Nil{}),
                       klns_of(us, lnt)}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{ICnGo{True{}, ti, ps, qs}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, 4294967295, False{}))
    case 1n+p KCon{ICnGo{False{}, ti, ps, qs}, k} Tuple{Tuple{fs, msg}, ri}:
      +t2 : U32 = ti
      km(p, KCon{kev(WP{2, 0, 0, 0, ps, qs, 2000000}, t2),
                 KCon{IWrap{True{}}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
    # -- Let --
    case 1n+p KCon{IEv{xi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.ELet{n, ty, v, b}}}, ri}:
      +b2 : U32 = b
      +f2 : U32 = fu
      km(p, KCon{kev(WP{1, 0, 0, v, Nil{}, Nil{}, 2000000}, b2),
                 KCon{ILt2{ctx, (f2 - 1 : U32)}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, b2, ri))
    case 1n+p KCon{ILt2{ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{ISub{r2, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, knoop(fs, 0))
    # -- App --
    case 1n+p KCon{IEv{xi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EApp{f, a}}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +f3 : U32 = f
      +fu2 : U32 = fu
      km(p, KCon{ISub{f3, cx9, (fu2 - 1 : U32)},
                 KCon{IAp2{a, f3, cx9, fu2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IAp2{a, f, ctx, fu}, k} Tuple{Tuple{fs, MIR{t, ok}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +t2 : U32 = t
      km(p, KCon{kwev(True{}, t2, Nil{}, 2000000, cx9),
                 KCon{IAp3{a, f, t2, ok, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
    case 1n+p KCon{IAp3{a, f, rf, rfok, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{IAp3b{a, f, rf, rfok, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{IAp3b{a, f, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
      km(p, KCon{IApR{a, node, rf, rfok, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kfetch(fs, f, ri))
    case 1n+p KCon{IApR{a, node, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EApp{g, a0}}}, ri}:
      km(p, KCon{IApRr{a0, a, node, rf, rfok, ctx, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kfetch(fs, krec_slot(hcb), ri))
    case 1n+p KCon{IApRr{a0, a, node, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EApp{ra, rt}}}, ri}:
      +a2 : U32 = a
      +hit : Bool = U32.is_eq(a0, a2) && U32.is_eq(ra, a2)
      +rt2 : U32 = rt
      km(p, KCon{IApR2{hit, a2, node, rf, rfok, ctx, fu}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, U32.and(rt2, 2147483647), U32.is_ge(rt2, 2147483648)))
    case 1n+p KCon{IApRr{a0, a, node, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{IApR2{False{}, a, node, rf, rfok, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IApR{a, node, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{IApR2{False{}, a, node, rf, rfok, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IApR2{True{}, a, node, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, MIR{t, ok}}, ri}:
      km(p, KCon{IAp4{a, node, rf, rfok, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kmir(fs, t, ok))
    case 1n+p KCon{IApR2{False{}, a, node, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +a2 : U32 = a
      +c2 : List<&2, U32> = ctx
      +fu2 : U32 = fu
      km(p, KCon{ISub{a2, c2, (fu2 - 1 : U32)},
                 KCon{IAp4{a2, node, rf, rfok, c2, fu2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IAp4{a, node, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, MIR{t, ok}}, ri}:
      +t2 : U32 = t
      +nd2 : T.Ex = node
      +ok2 : Bool = ok
      +a2 : U32 = a
      # record this argument check for an enclosing `f a` (see IApR)
      km(p, KCon{IAp5{a2, nd2, t2, ok2, rf, rfok, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb,
         keq_lists_tin(krec_write(fs, krec_slot(hcb), a2, t2, ok2),
                       Con{t2, Nil{}},
                       Con{I.all_dom(nd2), Nil{}}, lnt))
    case 1n+p KCon{IAp5{a, node, ra, raok, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{IAp5Go{L.tri_is_yes(t), a, node, ra, raok, rf, rfok, ctx,
                        fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IAp5Go{True{}, a, node, ra, raok, rf, rfok, ctx, fu},
                   k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{IAp7{a, node, ra, raok, rf, rfok, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, L.TYes{}))
    case 1n+p KCon{IAp5Go{False{}, a, node, ra, raok, rf, rfok, ctx, fu},
                   k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{IAp5iq{a, node, ra, raok, rf, rfok, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, kfl_tin(fs, hcb, 4))
    case 1n+p KCon{IAp5iq{a, node, ra, raok, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{IAp5io{U32.is_eq(ri, 1), a, node, ra, raok, rf, rfok, ctx,
                        fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    # infer_only: the argument is taken at its word
    case 1n+p KCon{IAp5io{True{}, a, node, ra, raok, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{IAp7{a, node, ra, raok, rf, rfok, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, L.TYes{}))
    case 1n+p KCon{IAp5io{False{}, a, node, ra, raok, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +r2 : U32 = ra
      km(p, KCon{DWhd{r2, cx9}, KCon{IAp5c{a, node, r2, raok, rf, rfok, cx9,
                                      fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IAp5c{a, node, ra, raok, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +nd2 : T.Ex = node
      km(p, KCon{DWhd{I.all_dom(nd2), cx9},
                 KCon{IAp5d{ri, a, nd2, ra, raok, rf, rfok, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{IAp5d{w1, a, node, ra, raok, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +w12 : U32 = w1
      +r2 : U32 = ri
      km(p, KCon{IAp6{w12, r2, a, node, ra, raok, rf, rfok, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         keq_lists_tin(fs, Con{w12, Nil{}}, Con{r2, Nil{}}, lnt))
    case 1n+p KCon{IAp6{w1, w2, a, node, ra, raok, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{IAp6Go{L.tri_is_yes(t), w1, w2, a, node, ra, raok, rf,
                        rfok, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IAp6Go{True{}, w1, w2, a, node, ra, raok, rf, rfok,
                          ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{IAp7{a, node, ra, raok, rf, rfok, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, L.TYes{}))
    # the argument-type comparison answers a Tri: everything it allocates
    # is released after (a rollback region), as Lean keeps nothing from a
    # defeq check but its caches
    case 1n+p KCon{IAp6Go{False{}, w1, w2, a, node, ra, raok, rf, rfok,
                          ctx, fu}, k} Tuple{Tuple{Tuple{ex, nx}, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +w12 : U32 = w1
      +w22 : U32 = w2
      +n2 : U32 = nx
      km(p, KCon{DSub{False{}, U32.is_eq(w12, w22), w12, w22, cx9, 4096},
                 KCon{KRb{n2, wm},
                      KCon{IAp7{a, node, ra, raok, rf, rfok, cx9, fu}, k}}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop((ex, n2), ri))
    case 1n+p KCon{IAp7{a, node, ra, raok, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +r2 : U32 = ra
      km(p, KCon{IAp8{t, a, node, r2, raok, rf, rfok, ctx, fu}, k}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, r2, ri))
    case 1n+p KCon{IAp8{dq, a, node, ra, raok, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +nd2 : T.Ex = node
      km(p, KCon{IAp9{hd, dq, a, nd2, ra, raok, rf, rfok, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kspine_tin(fs, I.all_dom(nd2), ri))
    case 1n+p KCon{IAp9{hx, dq, a, node, ra, raok, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +hx2 : T.Ex = hx
      +hy2 : T.Ex = hd
      +dq2 : L.Tri = dq
      +nd2 : T.Ex = node
      +ra2 : U32 = ra
      +rf2 : U32 = rf
      +ok2 : Bool = rfok && raok && I.is_all(nd2)
      +dd : Bool = kno_value(hx2, mt, vt, qtt)
                   && kno_value(hy2, mt, vt, qtt)
                   && Bool.not(U32.is_eq(I.const_nm2(hx2),
                                         I.const_nm2(hy2)))
      +a2 : U32 = a
      km(p, KCon{kev(WP{1, 0, 0, a2, Nil{}, Nil{}, 2000000},
                     I.all_cod(nd2)),
                 KCon{IAp10{(ok2
                             && (L.tri_is_no(dq2)
                                 || (Bool.not(L.tri_is_yes(dq2)) && dd)))
                            || U32.is_eq(rf2, 4294967294)
                            || U32.is_eq(ra2, 4294967294),
                            Bool.and(ok2, L.tri_is_yes(dq2))}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kfetch(fs, I.all_cod(nd2), ri))
    case 1n+p KCon{IAp10{bad, ok}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, S.pick(bad, 4294967294, r2), ok))
    # -- Proj --
    case 1n+p KCon{IEv{xi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EProj{tn, idx, sx}}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +s2 : U32 = sx
      +fu2 : U32 = fu
      km(p, KCon{ISub{s2, cx9, (fu2 - 1 : U32)},
                 KCon{IPj2{tn, idx, s2, cx9, fu2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IPj2{tn, idx, sx, ctx, fu}, k}
         Tuple{Tuple{fs, MIR{t, ok}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +t2 : U32 = t
      km(p, KCon{DWhd{t2, cx9}, KCon{IPj3{tn, idx, sx, t2, ok, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IPj3{tn, idx, sx, rs, rsok, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{IPj4{tn, idx, sx, rs, rsok, ctx, fu}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{IPj4{tn, idx, sx, rs, rsok, ctx, fu}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
      +nd2 : T.Ex = node
      km(p, KCon{IPj5{tn, idx, sx, nd2, rs, rsok, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_head_tin(fs, nd2, ri))
    # the structure's type is headed by another inductive than the
    # projection names: Lean's infer_proj throws (a definite ill-typing)
    case 1n+p KCon{IPj5{tn, idx, sx, sty, rs, rsok, ctx, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +h2 : T.Ex = hd
      +tn2 : U32 = tn
      +hn : U32 = I.const_nm2(h2)
      +hm : I.Meta = R.get(I.Meta, 64n, mt, hn, I.MNone{})
      km(p, KCon{IPj5b{rsok && U32.is_ne(hn, 4294967295)
                       && U32.is_ne(hn, tn2) && I.meta_is_ind(hm),
                       tn2, idx, sx, h2, rs, rsok, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         ((fs, MSP{h2, sargs}), ri))
    case 1n+p KCon{IPj5b{True{}, tn, idx, sx, hd, rs, rsok, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, 4294967294, False{}))
    case 1n+p KCon{IPj5b{False{}, tn, idx, sx, hd, rs, rsok, ctx, fu}, k}
         Tuple{Tuple{fs, MSP{hd2, sargs}}, ri}:
      +tn2 : U32 = tn
      +i2 : U32 = idx
      +h2 : T.Ex = hd2
      +mi : I.Meta = R.get(I.Meta, 64n, mt, tn2, I.MNone{})
      +cty : U32 = I.meta_cty(mi)
      km(p, KCon{kev(WP{2, 0, 0, 0,
                        R.get(List<&2, U32>, 64n, lp, tn2, Nil{}),
                        klns_of(I.sl_const_us(h2), lnt), 2000000}, cty),
                 KCon{IPj6{rsok && I.meta_is_ind(mi)
                           && U32.is_lt(i2, I.meta_nf(mi))
                           && U32.is_eq(I.const_nm2(h2), tn2),
                           I.meta_ppx(mi), I.meta_ppd(mi), I.meta_pr(mi), tn2, i2, sx,
                           sargs, rs, ctx}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, cty, ri))
    case 1n+p KCon{IPj6{ok, ppx, ppd, pr, tn, idx, sx, sargs, rs, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      +px2 : U32 = ppx
      +pd2 : U32 = ppd
      +i2 : U32 = idx
      # past the static bound of a Prop structure, before the definite one:
      # Lean sizes the instantiated fields, so size field ppx (the first
      # earlier dependent field that may be data) in this instance
      km(p, KCon{IPjQ{U32.is_ne(px2, 4294967295) && U32.is_gt(i2, px2)
                      && U32.is_lt(i2, pd2),
                      r2, ok, px2, pd2, pr, tn, i2, sx, sargs, rs, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, r2))
    case 1n+p KCon{IPjQ{False{}, lsr, ok, ppx, ppd, pr, tn, idx, sx, sargs,
                        rs, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +i2 : U32 = idx
      +tn2 : U32 = tn
      km(p, KCon{IPj7{lsr, ok, ppx, ppd, pr, tn2, i2, sargs, rs, ctx}, k}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kprojn_tin(hcb, fs, i2, tn2, sx))
    case 1n+p KCon{IPjQ{True{}, lsr, ok, ppx, ppd, pr, tn, idx, sx, sargs,
                        rs, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +px2 : U32 = ppx
      +tn2 : U32 = tn
      +sx2 : U32 = sx
      km(p, KCon{IPjR1{lsr, ok, px2, ppd, pr, tn2, idx, sx2, sargs, rs, ctx},
                 k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kprojn_tin(hcb, fs, px2, tn2, sx2))
    case 1n+p KCon{IPjR1{lsr, ok, ppx, ppd, pr, tn, idx, sx, sargs, rs, ctx},
                   k} Tuple{Tuple{fs, MSP{hd, pns}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +l2 : U32 = lsr
      +sa2 : List<&2, U32> = sargs
      km(p, KCon{WPlE{l2, List.append(&2, U32, sa2, pns), cx9},
                 KCon{IPjR2{l2, ok, ppx, ppd, pr, tn, idx, sx, sa2, rs, cx9},
                      k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, l2, ri))
    case 1n+p KCon{IPjR2{lsr, ok, ppx, ppd, pr, tn, idx, sx, sargs, rs, ctx},
                   k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{IPjR3{lsr, ok, ppx, ppd, pr, tn, idx, sx, sargs, rs, ctx},
                 k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kfetch(fs, r2, 0))
    case 1n+p KCon{IPjR3{lsr, ok, ppx, ppd, pr, tn, idx, sx, sargs, rs, ctx},
                   k} Tuple{Tuple{fs, MX{node}}, ri}:
      +nd2 : T.Ex = node
      +f2 : U32 = I.all_dom(nd2)
      +c2 : List<&2, U32> = ctx
      km(p, KCon{kslev(f2, c2, 2000000),
                 KCon{IPjR4{I.is_all(nd2), lsr, ok, ppx, ppd, pr, tn, idx, sx,
                            sargs, rs, c2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, f2, ri))
    # field ppx definitely data here: the bound is definite from it on; a
    # proof here, and the projection is the next field: every earlier
    # dependent field is a proof, so it is allowed
    case 1n+p KCon{IPjR4{isall, lsr, ok, ppx, ppd, pr, tn, idx, sx, sargs, rs,
                         ctx}, k} Tuple{Tuple{fs, MLn{u}}, ri}:
      +px2 : U32 = ppx
      +i2 : U32 = idx
      +tn2 : U32 = tn
      +z : L.Tri = L.ln_is_zero(u)
      +ia : Bool = isall
      km(p, KCon{IPj7{lsr, ok,
                      S.pick(ia && L.tri_is_yes(z)
                             && U32.is_eq(i2, (px2 + 1 : U32)), i2, px2),
                      S.pick(ia && L.tri_is_no(z), px2, ppd),
                      pr, tn2, i2, sargs, rs, ctx}, k}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kprojn_tin(hcb, fs, i2, tn2, sx))
    case 1n+p KCon{IPj7{lsr, ok, ppx, ppd, pr, tn, idx, sargs, rs, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, pns}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +l2 : U32 = lsr
      km(p, KCon{WPlE{l2, List.append(&2, U32, sargs, pns), cx9},
                 KCon{IPj8{ok, ppx, ppd, pr, idx, rs, cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, l2, ri))
    case 1n+p KCon{IPj8{ok, ppx, ppd, pr, idx, rs, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{IPj9{r2, ok, ppx, ppd, pr, idx, rs, ctx}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{IPj9{pt, ok, ppx, ppd, pr, idx, rs, ctx}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
      +nd2 : T.Ex = node
      +p2 : U32 = pt
      +fldty : U32 = I.all_dom(nd2)
      +f2 : U32 = fldty
      +c2 : List<&2, U32> = ctx
      km(p, KCon{kslev(f2, c2, 2000000), KCon{SLX0{f2, c2},
                 KCon{IPj10{ok, U32.is_ne(p2, 4294967295),
                            I.is_all(nd2), ppx, ppd, pr, idx, rs, f2}, k}}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, f2, ri))
    case 1n+p KCon{IPj10{ok, ptok, isall, ppx, ppd, pr, idx, rs, fldty}, k}
         Tuple{Tuple{fs, MLn{u}}, ri}:
      # Lean's infer_proj on a Prop structure: the field taken must be a
      # proof, and so must every earlier field a later one depends on. The
      # static bounds: below ppx no earlier dependent field can be data; at
      # or past ppd one definitely is. Between them the instance decides
      # (a field `w : α` with α a Prop): undecided, never a reject.
      +z : L.Tri = L.ln_is_zero(u)
      +fldprop : Bool = L.tri_is_yes(z)
      +fldno : Bool = L.tri_is_no(z)
      +i2 : U32 = idx
      +px2 : U32 = ppx
      +pd2 : U32 = ppd
      +defprop : Bool = U32.is_ne(px2, 4294967295)
      +allowed : Bool = fldprop && U32.is_le(i2, px2)
      +violates : Bool = defprop && (fldno || U32.is_ge(i2, pd2))
      +rity : U32 = S.pick(U32.is_eq(rs, 4294967294), 4294967294,
                           S.pick(violates, 4294967294, fldty))
      +ri2 : U32 = rity
      +ok2 : Bool = ptok && isall
                    && (U32.is_eq(pr, 0) || allowed)
      km(p, KCon{IPjOut{ok, ri2, ok2}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IPjOut{True{}, rity, ok2}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, rity, ok2))
    case 1n+p KCon{IPjOut{False{}, rity, ok2}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, S.pick(U32.is_eq(rity, 4294967294), 4294967294,
                         4294967295), False{}))
    # -- fallthrough: EBad and anything unknown --
    case 1n+p KCon{IEv{xi, ctx, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, 4294967295, False{}))
    # ---- dq_or_irrel: the proof-irrelevance fallback ----
    case 1n+p KCon{DEtX{xi, yi, ctx}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      +t2 : L.Tri = t
      km(p, KCon{DEtX2{L.tri_is_yes(t2), t2, xi, yi, ctx}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DEtX2{True{}, t, xi, yi, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, t))
    # inside a rollback region: the attempt answers a Tri, so everything it
    # allocates (inferred types, whnfs) and memoises is released after
    case 1n+p KCon{DEtX2{False{}, t, xi, yi, ctx}, k}
         Tuple{Tuple{Tuple{ex, nx}, msg}, ri}:
      +x2 : U32 = xi
      +n2 : U32 = nx
      km(p, KCon{DIr1{t, x2, yi, ctx}, KCon{KRb{n2, wm}, k}}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, kspine_tin((ex, n2), x2, 0))
    case 1n+p KCon{DIr1{t, xi, yi, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +y2 : U32 = yi
      km(p, KCon{DIr2{t, hd, I.len_u(sargs, 0), y2, xi, ctx}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, y2, ri))
    case 1n+p KCon{DIr2{t, hx, nx, yi, xi, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +hx2 : T.Ex = hx
      +hy2 : T.Ex = hd
      +ny : U32 = I.len_u(sargs, 0)
      +t2 : L.Tri = t
      +kx : U32 = I.dq_head_key(hx2)
      +gate : Bool = (Bool.not(U32.is_eq(kx, 4294967295))
                      && U32.is_eq(kx, I.dq_head_key(hy2)))
                     # Lean tries proof irrelevance on every pair, before
                     # any unfolding: a structural NO between two proofs
                     # (a theorem applied vs a projection) is not final
                     || L.tri_is_no(t2)
                     # undecided: proof irrelevance may still settle it
                     # (a proof term vs a hypothesis of the same Prop)
                     || (Bool.not(L.tri_is_yes(t2)) && Bool.not(L.tri_is_no(t2)))
      # Lean's is_def_eq_core tries structure eta once the applications
      # fail to match: `mk a.. =?= y` with y of the structure
      +cxh : Bool = I.meta_is_ctor(R.get(I.Meta, 64n, mt, I.const_nm2(hx2),
                                         I.MNone{}))
      +cyh : Bool = I.meta_is_ctor(R.get(I.Meta, 64n, mt, I.const_nm2(hy2),
                                         I.MNone{}))
      +eta : Bool = L.tri_is_no(t2)
                    && ((kseta(hx2, nx, mt) && Bool.not(cyh))
                        || (kseta(hy2, ny, mt) && Bool.not(cxh)))
      km(p, KCon{DIrEt{eta, gate, t2, xi, yi, ctx}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DIrEt{False{}, gate, t, xi, yi, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DIrGo{gate, t, xi, yi, ctx}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DIrEt{True{}, gate, t, xi, yi, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = xi
      km(p, KCon{DIrE1{gate, t, x2, yi, ctx}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kfetch(fs, x2, ri))
    case 1n+p KCon{DIrE1{gate, t, xi, yi, ctx}, k}
         Tuple{Tuple{fs, MX{xn}}, ri}:
      +y2 : U32 = yi
      km(p, KCon{DIrE2{xn, gate, t, xi, y2, ctx}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kfetch(fs, y2, ri))
    case 1n+p KCon{DIrE2{xn, gate, t, xi, yi, ctx}, k}
         Tuple{Tuple{fs, MX{yn}}, ri}:
      +x2 : U32 = xi
      +y2 : U32 = yi
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DC1{xn, yn, x2, y2, c2, 4096},
                 KCon{DIrE3{gate, t, x2, y2, c2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, x2, ri))
    case 1n+p KCon{DIrE3{gate, t, xi, yi, ctx}, k}
         Tuple{Tuple{fs, MTri{e}}, ri}:
      +e2 : L.Tri = e
      km(p, KCon{DIrEt{False{}, gate, L.pick_tri(L.tri_is_yes(e2), L.TYes{}, t),
                       xi, yi, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DIrGo{False{}, t, xi, yi, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, t))
    case 1n+p KCon{DIrGo{True{}, t, xi, yi, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = xi
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DTy1{c2}, KCon{DTyF{x2, c2}, KCon{DIr4{t, yi, c2}, k}}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kspine_tin(fs, x2, ri))
    case 1n+p KCon{DIr4{t, yi, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +y2 : U32 = yi
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DTy1{c2}, KCon{DTyF{y2, c2}, KCon{DIr5{t, ri, c2}, k}}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kspine_tin(fs, y2, 0))
    # the cheap type oracle could not type x (a projection, a beta redex
    # head, ..): Lean's proof irrelevance infers the type, so infer it
    case 1n+p KCon{DTyF{x, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{DTyF2{U32.is_eq(r2, 4294967295), x, ctx}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, r2))
    case 1n+p KCon{DTyF2{False{}, x, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, ri))
    # infer_only (Lean's infer_type in is_def_eq_proof_irrel): store flag 4
    # set while it runs, so argument types are not re-checked
    case 1n+p KCon{DTyF2{True{}, x, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DTyFs{x, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt,
         hcb, kfl_tin(fs, hcb, 4))
    case 1n+p KCon{DTyFs{x, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{ISub{x, ctx, 4096}, KCon{DTyF3{ri}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         knoop(kfl_set(fs, hcb, 4, 1), 0))
    case 1n+p KCon{DTyF3{old}, k} Tuple{Tuple{fs, MIR{t, ok}}, ri}:
      +t2 : U32 = t
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kkeep(kfl_set(fs, hcb, 4, old),
               S.pick(U32.is_ge(t2, 4294967294), 4294967295, t2)))
    case 1n+p KCon{DIr5{t, rx, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +rx2 : U32 = rx
      +r2 : U32 = ri
      km(p, KCon{DIr5x{Bool.not(U32.is_eq(rx2, 4294967295))
                       && Bool.not(U32.is_eq(r2, 4294967295)),
                       t, rx2, r2, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, r2))
    case 1n+p KCon{DIr5x{False{}, t, rx, ry, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +rx2 : U32 = rx
      +r2 : U32 = ry
      km(p, KCon{DIr6{False{}, t, rx2, r2, ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb,
         keq_lists_tin(fs, Con{rx2, Nil{}}, Con{r2, Nil{}}, lnt))
    case 1n+p KCon{DIr5x{True{}, t, rx, ry, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +rx2 : U32 = rx
      +c2 : List<&2, U32> = ctx
      km(p, KCon{kslev(rx2, c2, 2000000), KCon{DIr5p{t, rx2, ry, c2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, rx2, ri))
    case 1n+p KCon{DIr5p{t, rx, ry, ctx}, k} Tuple{Tuple{fs, MLn{u}}, ri}:
      +z : L.Tri = L.ln_is_zero(u)
      km(p, KCon{DIr5r{Bool.not(L.tri_is_yes(z)) && Bool.not(L.tri_is_no(z)),
                       L.tri_is_yes(z), t, rx, ry, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DIr5r{False{}, zy, t, rx, ry, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DIr5q{zy, t, rx, ry, ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, ri))
    # the oracle cannot size the type as it stands (a beta redex, say): Lean's
    # is_prop whnfs it first, so size its whnf
    case 1n+p KCon{DIr5r{True{}, zy, t, rx, ry, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +rx2 : U32 = rx
      km(p, KCon{DWhd{rx2, cx9}, KCon{DIr5s{t, rx2, ry, cx9}, k}}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DIr5s{t, rx, ry, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +w : U32 = ri
      +c2 : List<&2, U32> = ctx
      km(p, KCon{kslev(w, c2, 2000000), KCon{DIr5u{t, rx, ry, c2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, w, w))
    case 1n+p KCon{DIr5u{t, rx, ry, ctx}, k} Tuple{Tuple{fs, MLn{u}}, ri}:
      +z : L.Tri = L.ln_is_zero(u)
      km(p, KCon{DIr5v{Bool.not(L.tri_is_yes(z)) && Bool.not(L.tri_is_no(z)),
                       L.tri_is_yes(z), t, rx, ry, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DIr5v{False{}, zy, t, rx, ry, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DIr5q{zy, t, rx, ry, ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, ri))
    # the oracle cannot size the whnf either (a Pi over a beta redex, say):
    # Lean's is_prop infers the type's sort, so infer it (infer_only)
    case 1n+p KCon{DIr5v{True{}, zy, t, rx, ry, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +rx2 : U32 = rx
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DTyF2{True{}, rx2, c2}, KCon{DIr5w{t, rx2, ry, c2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DIr5w{t, rx, ry, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +s2 : U32 = ri
      km(p, KCon{DIr5wg{U32.is_eq(s2, 4294967295), t, rx, ry, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, s2))
    case 1n+p KCon{DIr5wg{True{}, t, rx, ry, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DIr5q{False{}, t, rx, ry, ctx}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DIr5wg{False{}, t, rx, ry, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +s2 : U32 = ri
      km(p, KCon{DWhd{s2, cx9}, KCon{DIr5wf{t, rx, ry, cx9}, k}}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, s2))
    case 1n+p KCon{DIr5wf{t, rx, ry, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +w : U32 = ri
      km(p, KCon{DIr5wz{t, rx, ry, ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kfetch(fs, w, w))
    case 1n+p KCon{DIr5wz{t, rx, ry, ctx}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +nd : T.Ex = node
      km(p, KCon{DIr5q{I.is_sortx(nd)
                       && L.tri_is_yes(L.ln_is_zero(
                            R.get(L.LN, 64n, lnt, I.sort_lvl_of(nd),
                                  L.LNun{}))),
                       t, rx, ry, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DIr5q{False{}, t, rx, ry, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, t))
    case 1n+p KCon{DIr5q{True{}, t, rx, ry, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +rx2 : U32 = rx
      km(p, KCon{DWhd{rx2, cx9}, KCon{DIr5y{t, rx2, ry, cx9}, k}}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DIr5y{t, rx, ry, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +wx : U32 = ri
      +ry2 : U32 = ry
      km(p, KCon{DWhd{ry2, cx9}, KCon{DIr5z{t, rx, ry2, wx, cx9}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DIr5z{t, rx, ry, wx, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +wy : U32 = ri
      +wx2 : U32 = wx
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DSub{False{}, U32.is_eq(wx2, wy), wx2, wy, c2, 4096},
                 KCon{DIr6{True{}, t, rx, ry, c2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    # pz: the Prop test already passed (DIr5q), possibly on the whnf
    case 1n+p KCon{DIr6{pz, t, rx, ry, ctx}, k} Tuple{Tuple{fs, MTri{sq}}, ri}:
      +rx2 : U32 = rx
      km(p, KCon{kslev(rx2, ctx, 2000000),
                 KCon{DIr7{pz, t, Bool.not(U32.is_eq(rx2, 4294967295))
                              && Bool.not(U32.is_eq(ry, 4294967295)),
                           sq}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, rx2, ri))
    # both proofs: Lean answers is_def_eq of the types, so an undecided type
    # comparison leaves the pair undecided, never the structural NO
    case 1n+p KCon{DIr7{pz, t, both, sq}, k} Tuple{Tuple{fs, MLn{u}}, ri}:
      +sq2 : L.Tri = sq
      +prf : Bool = both && (pz || L.tri_is_yes(L.ln_is_zero(u)))
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.pick_tri(prf && L.tri_is_yes(sq2), L.TYes{},
                              L.pick_tri(prf && L.tri_is_no(t)
                                         && Bool.not(L.tri_is_no(sq2)),
                                         L.TUnk{}, t))))
    # ---- dq_type_of: the type oracle ----
    case 1n+p KCon{DTy1{ctx}, k} Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      match hd:
        case T.EConst{n, us}:
          +n2 : U32 = n
          +ti : U32 = R.get(U32, 64n, nt, n2, 4294967295)
          +t2 : U32 = ti
          km(p, KCon{DTyGo{Bool.not(U32.is_eq(t2, 4294967295)), False{},
                           t2, 0, R.get(List<&2, U32>, 64n, lp, n2, Nil{}),
                           klns_of(us, lnt), sargs}, k},
             lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
        case T.EBVar{i}:
          +i2 : U32 = i
          +ti : U32 = I.nth_u(ctx, i2, 4294967295)
          +t2 : U32 = ti
          km(p, KCon{DTyGo{False{},
                           Bool.not(U32.is_eq(t2, 4294967295)), t2,
                           (i2 + 1 : U32), Nil{}, Nil{}, sargs}, k},
             lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
        case _:
          km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
             kkeep(fs, 4294967295))
    case 1n+p KCon{DTyGo{True{}, m2, ti, dlift, ps, qs, sargs}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +t2 : U32 = ti
      km(p, KCon{kev(WP{2, 0, 0, 0, ps, qs, 2000000}, t2),
                 KCon{DTy2{sargs}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
    case 1n+p KCon{DTyGo{False{}, True{}, ti, dlift, ps, qs, sargs}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +t2 : U32 = ti
      km(p, KCon{kev(WP{0, 0, dlift, 0, Nil{}, Nil{}, 2000000}, t2),
                 KCon{DTy2{sargs}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
    case 1n+p KCon{DTyGo{False{}, False{}, ti, dlift, ps, qs, sargs}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kkeep(fs, 4294967295))
    case 1n+p KCon{DTy2{sargs}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WPlE{r2, sargs, Nil{}}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{IOut{}, k} Tuple{Tuple{fs, MIR{t, ok}}, ri}:
      +t2 : U32 = t
      +okb : U32 = S.pick(ok, 1, 0)
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kkeep(fs, S.pick(U32.is_eq(t2, 4294967295),
                          (4000000000 + okb : U32),
                          S.pick(U32.is_eq(t2, 4294967294),
                                 (4000000002 + okb : U32),
                                 (t2 * 2 + okb : U32)))))
    # ---- the typed-check path ----
    # ck_typed: whd the declared type, infer its type, whd that, read its
    # sort, then route: reject / decline / accept / check the value
    case 1n+p KCon{CkT1{isthm, vi, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{ISub{r2, Nil{}, fu}, KCon{CkT2{isthm, r2, vi}, k}}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{CkT2{isthm, ti1, vi}, k} Tuple{Tuple{fs, MIR{t, ok}}, ri}:
      +t2 : U32 = t
      km(p, KCon{DWhd{t2, Nil{}}, KCon{CkT3{isthm, ti1, vi, t2, ok}, k}}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{CkT3{isthm, ti1, vi, rty, riok}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{CkT4{isthm, ti1, vi, rty, riok}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{CkT4{isthm, ti1, vi, rty, riok}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
      +kx : T.Ex = node
      +rk : Bool = riok
      +t2 : U32 = ti1
      +u : L.LN = L.pick_ln(Bool.and(rk, I.is_sortx(kx)),
                            R.get(L.LN, 64n, lnt, I.sort_lvl_of(kx),
                                  L.LNun{}),
                            L.LNun{})
      km(p, KCon{CkT5{isthm, t2, vi, u,
                      U32.is_eq(rty, 4294967294)}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
    case 1n+p KCon{CkT5{isthm, ti1, vi, u, rtybad}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
      +tx : T.Ex = node
      +sh : U32 = knat_shape(tx)
      km(p, KCon{CkT6{isthm, ti1, vi, u, rtybad, sh,
                      U32.is_eq(sh, 2)}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kfetch(fs, R.get(U32, 64n, nt, I.const_nm2(tx), 4294967295),
                ri))
    case 1n+p KCon{CkT6{isthm, ti1, vi, u, rtybad, shape, iscc}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
      +nat : Bool = U32.is_eq(shape, 1)
                    || (iscc && I.head_not_sort(node))
      +u2 : L.LN = u
      +tt : L.Tri = I.type_tri(nat, u2)
      +rb : Bool = rtybad
      +it : Bool = isthm
      +uz : L.Tri = L.ln_is_zero(u2)
      # route: reject (rtybad, tri No, thm-prop No) / decline (tri Unk,
      # thm-prop Unk) / accept (def with no value) / check the value
      +rej : Bool = rb || L.tri_is_no(tt)
                    || (L.tri_is_yes(tt) && it && L.tri_is_no(uz))
      +dec : Bool = Bool.not(rej)
                    && (L.tri_is_yes(tt) && it && Bool.not(L.tri_is_no(uz))
                        && Bool.not(L.tri_is_yes(uz))
                        || Bool.not(L.tri_is_yes(tt)))
      km(p, KCon{CkT7{rej, dec, ti1, vi}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{CkT7{True{}, b2, ti1, vi}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, 1))
    case 1n+p KCon{CkT7{False{}, True{}, ti1, vi}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, 2))
    case 1n+p KCon{CkT7{False{}, False{}, ti1, vi}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +v2 : U32 = vi
      km(p, KCon{CkT8{U32.is_eq(v2, 4294967295), ti1, v2}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{CkT8{True{}, ti1, vi}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, 0))
    case 1n+p KCon{CkT8{False{}, ti1, vi}, k} Tuple{Tuple{fs, msg}, ri}:
      +t2 : U32 = ti1
      km(p, KCon{DWhd{t2, Nil{}}, KCon{CkV2{vi, 1048576}, k}}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ck_value: whd the declared type, then bidirectionally check the value
    case 1n+p KCon{CkV2{vi, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +v2 : U32 = vi
      +r2 : U32 = ri
      km(p, KCon{CkEx{v2, r2, Nil{}, fu}, KCon{CkVOut{}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{CkVOut{}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      +t2 : L.Tri = t
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kkeep(fs, S.pick(L.tri_is_yes(t2), 0,
                          S.pick(L.tri_is_no(t2), 1, 2))))
    # ck_expr: bidirectional, answering a tri
    case 1n+p KCon{CkEx{xi, tye, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = xi
      km(p, KCon{CkEy0{x2, tye, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kfetch(fs, x2, ri))
    case 1n+p KCon{CkEy0{xi, tye, ctx, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +t2 : U32 = tye
      km(p, KCon{CkEy{node, xi, t2, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
    case 1n+p KCon{CkEy{T.ELam{n1, a1, b1, i1}, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EAll{n2, a2, b2, i2}}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +b22 : U32 = b2
      km(p, KCon{DWhd{b22, cx9},
                 KCon{CkE2{a1, b1, a2, xi, tye, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{CkE2{a1, b1, a2, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +a12 : U32 = a1
      +f2 : U32 = fu
      +c2 : List<&2, U32> = ctx
      +r2 : U32 = ri
      km(p, KCon{CkEx{b1, r2, Con{a12, c2}, (f2 - 1 : U32)},
                 KCon{CkE3{a12, a2, xi, tye, c2, f2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{CkE3{a1, a2, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +a12 : U32 = a1
      km(p, KCon{DWhd{a12, cx9},
                 KCon{CkE4{t, a12, a2, xi, tye, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{CkE4{sub, a1, a2, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +a22 : U32 = a2
      km(p, KCon{DWhd{a22, cx9},
                 KCon{CkE5{sub, ri, a1, a22, xi, tye, cx9, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{CkE5{sub, wd1, a1, a2, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +w2 : U32 = wd1
      +r2 : U32 = ri
      +a12 : U32 = a1
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DSub{False{}, U32.is_eq(a12, a2), w2, r2,
                      Con{a12, c2}, 2000000},
                 KCon{CkE6{sub, xi, tye, c2, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{CkE6{sub, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{CkE6Go{L.tri_is_yes(I.tri_and(t, sub)), xi, tye, ctx,
                        fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{CkE6Go{True{}, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{CkE6Go{False{}, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +x2 : U32 = xi
      +f2 : U32 = fu
      km(p, KCon{ISub{x2, cx9, f2}, KCon{CkI2{tye, cx9}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{CkEy{T.ELet{ln1, lt1, lv1, lb1}, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +b2 : U32 = lb1
      km(p, KCon{kev(WP{1, 0, 0, lv1, Nil{}, Nil{}, 2000000}, b2),
                 KCon{CkE7{tye, ctx, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, b2, ri))
    case 1n+p KCon{CkE7{tye, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      +f2 : U32 = fu
      km(p, KCon{CkEx{r2, tye, ctx, (f2 - 1 : U32)}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{CkEy{xn, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.ESort{lt}}}, ri}:
      +xn2 : T.Ex = xn
      +sh : U32 = knat_shape(xn2)
      km(p, KCon{CkE8c{sh, U32.is_eq(sh, 2), lt, xi, tye, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kfetch(fs, R.get(U32, 64n, nt, I.const_nm2(xn2), 4294967295),
                ri))
    case 1n+p KCon{CkE8c{shape, iscc, lt, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
      +x2 : U32 = xi
      +c2 : List<&2, U32> = ctx
      +f2 : U32 = fu
      km(p, KCon{kslev(x2, c2, f2),
                 KCon{CkE8b{U32.is_eq(shape, 1)
                            || (iscc && I.head_not_sort(node)),
                            lt, x2, tye, c2, f2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, x2, ri))
    case 1n+p KCon{CkE8b{nat, lt, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, MLn{u}}, ri}:
      +scmp : L.Tri = L.pick_tri(nat, L.TNo{},
                                 L.ln_cmp(R.get(L.LN, 64n, lnt, lt,
                                                L.LNun{}), u))
      +s2 : L.Tri = scmp
      km(p, KCon{CkE9{L.tri_is_yes(s2), L.tri_is_no(s2), xi, tye, ctx,
                      fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{CkE9{True{}, b2, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{CkE9{False{}, True{}, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TNo{}))
    case 1n+p KCon{CkE9{False{}, False{}, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +x2 : U32 = xi
      +f2 : U32 = fu
      km(p, KCon{ISub{x2, cx9, f2}, KCon{CkI2{tye, cx9}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{CkEy{xn, xi, tye, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +x2 : U32 = xi
      +f2 : U32 = fu
      km(p, KCon{ISub{x2, cx9, f2}, KCon{CkI2{tye, cx9}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ck_infer: infer, reduce both, compare
    case 1n+p KCon{CkI2{tye, ctx}, k} Tuple{Tuple{fs, MIR{t, ok}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +t2 : U32 = t
      km(p, KCon{DWhd{t2, cx9}, KCon{CkI3{tye, t2, ok, cx9}, k}}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{CkI3{tye, rty, riok, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +t2 : U32 = tye
      +rt2 : U32 = rty
      km(p, KCon{DWhd{t2, cx9},
                 KCon{CkI4{ri, U32.is_eq(rt2, t2), rt2, riok, cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{CkI4{w1, samef, rty, riok, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +w2 : U32 = w1
      +r2 : U32 = ri
      km(p, KCon{DSub{False{}, samef, w2, r2, ctx, 2000000},
                 KCon{CkI5{U32.is_eq(rty, 4294967294), riok}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{CkI5{rtybad, riok}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      +t2 : L.Tri = t
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.pick_tri(rtybad, L.TNo{},
                              L.pick_tri(riok, t2, L.TUnk{}))))
    # ---- the defeq result, as a U32 ----
    case 1n+p KCon{DOut{}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      +t2 : L.Tri = t
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kkeep(fs, S.pick(L.tri_is_yes(t2), 0,
                          S.pick(L.tri_is_no(t2), 1, 2))))
    # ---- the universe oracle ----
    case 1n+p KCon{SLEv{e, ctx, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      match node:
        case T.ESort{l}:
          km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
             kmln(fs, L.ln_succ(R.get(L.LN, 64n, lnt, l, L.LNun{}))))
        case T.EAll{n, t, b, bi}:
          +t2 : U32 = t
          +c2 : List<&2, U32> = ctx
          +f2 : U32 = fu
          km(p, KCon{kslev(t2, c2, (f2 - 1 : U32)),
                     KCon{SLIm{b, t2, c2, f2}, k}},
             lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
        case T.EBVar{i}:
          km(p, KCon{SLBv{}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
             kfetch(fs, I.nth_u(ctx, i, 4294967295), ri))
        case T.EConst{n, us}:
          +n2 : U32 = n
          km(p, KCon{SLCst{n2, us}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
             wm, nt, hcb,
             kfetch(fs, R.get(U32, 64n, nt, n2, 4294967295), ri))
        case T.EApp{f, a}:
          +e2 : U32 = e
          km(p, KCon{SLAp1{ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, e2, ri))
        case _:
          km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
             kmln(fs, L.LNun{}))
    case 1n+p KCon{SLIm{b, t, ctx, fu}, k} Tuple{Tuple{fs, MLn{dln}}, ri}:
      +b2 : U32 = b
      km(p, KCon{kslev(b2, Con{t, ctx}, (fu - 1 : U32)),
                 KCon{SLIm2{dln}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, b2, ri))
    case 1n+p KCon{SLIm2{dln}, k} Tuple{Tuple{fs, MLn{cln}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmln(fs, L.ln_imax(dln, cln)))
    case 1n+p KCon{SLBv{}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +nd : T.Ex = node
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmln(fs, L.pick_ln(I.is_sortx(nd),
                            R.get(L.LN, 64n, lnt, I.sort_lvl_of(nd),
                                  L.LNun{}),
                            L.LNun{})))
    case 1n+p KCon{SLCst{n, us}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +nd : T.Ex = node
      +n2 : U32 = n
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmln(fs, L.pick_ln(I.is_sortx(nd),
                            L.ln_subst(R.get(L.LN, 64n, lnt,
                                             I.sort_lvl_of(nd), L.LNun{}),
                                       R.get(List<&2, U32>, 64n, lp, n2,
                                             Nil{}),
                                       klns_of(us, lnt)),
                            L.LNun{})))
    case 1n+p KCon{SLAp1{ctx}, k} Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +h2 : T.Ex = hd
      km(p, KCon{SLAp2{I.sl_const_nm(h2), I.sl_const_us(h2)}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb,
         ktele_tin(fs, I.sl_head_ty(h2, nt, ctx), I.len_u(sargs, 0)))
    case 1n+p KCon{SLAp2{nm, us}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +nd : T.Ex = node
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmln(fs, L.pick_ln(I.is_sortx(nd),
                            L.ln_subst(R.get(L.LN, 64n, lnt,
                                             I.sort_lvl_of(nd), L.LNun{}),
                                       R.get(List<&2, U32>, 64n, lp, nm,
                                             Nil{}),
                                       klns_of(us, lnt)),
                            L.LNun{})))
    # the oracle's answer, or (unsized: is it a Prop?) Lean's is_prop:
    # infer the type's sort (infer_only), whnf it, read its level
    case 1n+p KCon{SLX0{e, ctx}, k} Tuple{Tuple{fs, MLn{u}}, ri}:
      +u2 : L.LN = u
      +z : L.Tri = L.ln_is_zero(u2)
      km(p, KCon{SLX0g{L.tri_is_yes(z) || L.tri_is_no(z), u2, e, ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{SLX0g{True{}, u, e, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmln(fs, u))
    case 1n+p KCon{SLX0g{False{}, u, e, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +e2 : U32 = e
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DTyF2{True{}, e2, c2}, KCon{SLX1{u}, k}}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{SLX1{u}, k} Tuple{Tuple{fs, msg}, ri}:
      +s2 : U32 = ri
      km(p, KCon{SLX1g{U32.is_eq(s2, 4294967295), u}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, s2))
    case 1n+p KCon{SLX1g{True{}, u}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmln(fs, u))
    case 1n+p KCon{SLX1g{False{}, u}, k} Tuple{Tuple{fs, msg}, ri}:
      +s2 : U32 = ri
      km(p, KCon{DWhd{s2, Nil{}}, KCon{SLX2{u}, k}}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, s2))
    case 1n+p KCon{SLX2{u}, k} Tuple{Tuple{fs, msg}, ri}:
      +w : U32 = ri
      km(p, KCon{SLX3{u}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kfetch(fs, w, w))
    case 1n+p KCon{SLX3{u}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +nd : T.Ex = node
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmln(fs, L.pick_ln(I.is_sortx(nd),
                            R.get(L.LN, 64n, lnt, I.sort_lvl_of(nd),
                                  L.LNun{}),
                            u)))
    case 1n+p KCon{SLUn{}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmln(fs, L.LNun{}))
    case 1n+p KCon{SLChk{want}, k} Tuple{Tuple{fs, MLn{got}}, ri}:
      +w2 : L.LN = want
      +g2 : L.LN = got
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kkeep(fs, S.pick(Bool.or(L.is_un(w2) && L.is_un(g2),
                                  L.tri_is_yes(L.ln_cmp(w2, g2))), 1, 0)))
    # ---- memoised whnf ----
    case 1n+p KCon{DWhd{i, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +i2 : U32 = i
      km(p, KCon{DWhdM{i2, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kwm_tin(fs, i2, khalf(hcb)))
    case 1n+p KCon{DWhdM{i, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +h2 : U32 = ri
      km(p, KCon{DWhdGo{U32.is_ne(h2, 4294967295), h2, i, ctx}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DWhdGo{True{}, h, i, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, h))
    # the memoised whnf at the caller's fuel (an iota major inside a whnf:
    # the outer fuel keeps bounding the nesting)
    case 1n+p KCon{DWhdF{i, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +i2 : U32 = i
      km(p, KCon{DWhdFM{i2, fu, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt,
         hcb, kwm_tin(fs, i2, khalf(hcb)))
    case 1n+p KCon{DWhdFM{i, fu, ctx}, k} Tuple{Tuple{Tuple{ex, nx}, msg}, ri}:
      +h2 : U32 = ri
      +i2 : U32 = i
      +n2 : U32 = nx
      km(p, KCon{DWhdFG{U32.is_ne(h2, 4294967295), h2, i2, fu, ctx}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop((ex, n2), 0))
    case 1n+p KCon{DWhdFG{True{}, h, i, fu, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, h))
    case 1n+p KCon{DWhdFG{False{}, h, i, fu, ctx}, k}
         Tuple{Tuple{Tuple{ex, nx}, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +i2 : U32 = i
      +n2 : U32 = nx
      km(p, KCon{kwev(True{}, i2, Nil{}, fu, cx9),
                 KCon{KRbN{n2, wm}, KCon{DWhdSt{i2, cx9}, k}}}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch((ex, n2), i2, 0))
    case 1n+p KCon{DWhdGo{False{}, h, i, ctx}, k}
         Tuple{Tuple{Tuple{ex, nx}, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +i2 : U32 = i
      +n2 : U32 = nx
      km(p, KCon{kwev(True{}, i2, Nil{}, 1000000, cx9),
                 KCon{KRb{n2, wm}, KCon{DWhdSt{i2, cx9}, k}}}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch((ex, n2), i2, 0))
    # A rollback region: the whnf began with the allocation pointer at
    # `mark` and memo `snap`. If its result is an OLDER node (index below
    # mark), nothing that survives can reference a node allocated since --
    # the frames below were pushed before mark, the memo is restored to the
    # snapshot (flags carried over), and the hash table's pointers into the
    # freed range become tombstones -- so the pointer drops back to mark.
    # A decide-style evaluation (a closed term to `true`) thus runs in
    # bounded store. An overflow seen here (or at the end, by fcheck)
    # marks the declaration CORRUPT.
    # a rollback region's end. A result OLDER than the mark: drop back to the
    # mark (memo snapshot restored, flags carried). A NEW result of a region
    # that allocated a lot: COMPACT -- its reachable new part is copied down
    # to the mark (kcompact: post-order, verified, lbr recomputed) and the
    # memo snapshot restored, so a long evaluation runs in bounded store
    # (Lean frees the intermediate terms by refcounting). An overflow seen
    # here marks the declaration CORRUPT.
    # ---- LD: decisive lazy defeq of two arbitrary terms ----
    case 1n+p KCon{LD{x, y, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +x2 : U32 = x
      +y2 : U32 = y
      km(p, KCon{LZ0{x2, y2, 256, cx9}, KCon{LDk{x2, y2, cx9, fu}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{LDk{x, y, ctx, fu}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      +r2 : U32 = ri
      km(p, KCon{LDk1{L.tri_is_yes(t), U32.is_eq(r2, 0), x, y, ctx, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, r2))
    case 1n+p KCon{LDk1{True{}, nopair, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    # no pair (the probe stopped before any iteration): the originals
    case 1n+p KCon{LDk1{False{}, True{}, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +x2 : U32 = x
      km(p, KCon{DWhd{x2, cx9}, KCon{LDw{y, cx9, fu}, k}}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, knoop(fs, 0))
    # the eager fallback evaluates the ORIGINAL pair (memoised, cached), not
    # the probe's furthest-unfolded pair (fresh nodes: no whnf memo, no YES
    # cache, every nested DSub re-infers types)
    case 1n+p KCon{LDk1{False{}, False{}, x, y, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +x2 : U32 = x
      km(p, KCon{DWhd{x2, cx9}, KCon{LDw{y, cx9, fu}, k}}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{LDp{x, y, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EApp{a, b}}}, ri}:
      +cx9 : List<&2, U32> = ctx
      +a2 : U32 = a
      km(p, KCon{DWhd{a2, cx9}, KCon{LDw{b, cx9, fu}, k}}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, knoop(fs, 0))
    # (not a pair node: the originals)
    case 1n+p KCon{LDp{x, y, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +x2 : U32 = x
      km(p, KCon{DWhd{x2, cx9}, KCon{LDw{y, cx9, fu}, k}}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{LDw{y, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +y2 : U32 = y
      +wx : U32 = ri
      km(p, KCon{DWhd{y2, cx9}, KCon{LDw2{wx, cx9, fu}, k}}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{LDw2{wx, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +wy : U32 = ri
      +wx2 : U32 = wx
      +f2 : U32 = fu
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295),
                      U32.is_eq(wx2, wy), wx2, wy, ctx, (f2 - 1 : U32)}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{KZr{}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, ((fs, msg), 0))
    case 1n+p KCon{KRb{mark, snap}, k} Tuple{Tuple{Tuple{ex, nx}, msg}, ri}:
      +r2 : U32 = ri
      +n2 : U32 = nx
      +m2 : U32 = mark
      +roll : Bool = U32.is_lt(r2, m2)
      +hb : U32 = khalf(hcb)
      +ovf : Bool = U32.is_ge(n2, hb)
      +comp : Bool = Bool.not(roll) && Bool.not(ovf)
                     && U32.is_ge((n2 - m2 : U32), 4096)
                     && U32.is_lt((n2 + (n2 - m2 : U32) + 16 : U32), hb)
      km(p, KCon{KRb2{comp, m2}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         krb_wm(roll || comp, ovf, wm, snap),
         nt, hcb, (((kg_bump(roll || comp, kfl_ovf(ovf, ex, hcb), hb),
                     S.pick(roll, m2, n2)), msg), r2))
    # an iota major's whnf: rolls back an old result, never compacts (moving
    # a large new normal form loses every memo of it: magma-list-pair-n7
    # 7 s -> timeout with compaction, at any threshold tried)
    case 1n+p KCon{KRbN{mark, snap}, k} Tuple{Tuple{Tuple{ex, nx}, msg}, ri}:
      +r2 : U32 = ri
      +n2 : U32 = nx
      +m2 : U32 = mark
      +roll : Bool = U32.is_lt(r2, m2)
      +hb : U32 = khalf(hcb)
      +ovf : Bool = U32.is_ge(n2, hb)
      # a large new result keeps its nodes but drops the memo entries made
      # meanwhile (the snapshot), as a compaction would
      +comp : Bool = Bool.not(roll) && Bool.not(ovf)
                     && False{} && U32.is_ge((n2 - m2 : U32), 65536)
                     && U32.is_lt((n2 + (n2 - m2 : U32) + 16 : U32), hb)
      km(p, KCon{KRb3{comp, m2}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         krb_wm(roll || comp, ovf, wm, snap),
         nt, hcb, (((kg_bump(roll || comp, kfl_ovf(ovf, ex, hcb), hb),
                     S.pick(roll, m2, n2)), msg), r2))
    case 1n+p KCon{KRb3{False{}, mark}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, ((fs, msg), ri))
    case 1n+p KCon{KRb3{True{}, mark}, k}
         Tuple{Tuple{Tuple{ex, nx}, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kwith_msg(kcompact_s(ex, nx, mark, ri, hcb), msg))
    # (the region's message -- a Tri, a node -- passes through unchanged)
    case 1n+p KCon{KRb2{False{}, mark}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, ((fs, msg), ri))
    case 1n+p KCon{KRb2{True{}, mark}, k}
         Tuple{Tuple{Tuple{ex, nx}, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kwith_msg(kcompact(ex, nx, mark, ri, hcb), msg))
    case 1n+p KCon{DWhdSt{i, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kkeep(kwm_set(fs, i, r2, khalf(hcb)), r2))
    # ---- the IH builder loop ----
    case 1n+p KCon{WIhNext{IC{Nil{}, cn, us, pre, fields, ccty, pp, ni,
                              acc, ci, need, can, delta, vi, ps, qs, e,
                              args, fu}, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +p2 : U32 = pp
      km(p, KCon{WCont{delta, I.skip_u(a2, (need + 1 : U32)),
                       (fu - 1 : U32), ctx}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         ktin_of(kapargs(hcb, List.append(&2, U32, fields, krev(acc, Nil{})),
                         (fs, I.nth_u(a2, (p2 + 1 + ci : U32),
                                      4294967295)))))
    case 1n+p KCon{WIhNext{IC{Con{h, t}, cn, us, pre, fields, ccty, pp, ni,
                              acc, ci, need, can, delta, vi, ps, qs, e,
                              args, fu}, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +cx9 : List<&2, U32> = ctx
      +h2 : U32 = h
      +pr2 : List<&2, U32> = pre
      +fl2 : List<&2, U32> = fields
      +cc2 : U32 = ccty
      +p2 : U32 = pp
      km(p, KCon{WPlE{cc2,
                      List.append(&2, U32, I.take_u(pr2, p2, Nil{}),
                                  I.take_u(fl2, (h2 - 1 : U32), Nil{})), cx9},
                 KCon{WIhPe{h2, IC{t, cn, us, pr2, fl2, cc2, p2, ni, acc,
                                   ci, need, can, delta, vi, ps, qs, e,
                                   args, fu}, cx9}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, cc2, ri))
    case 1n+p KCon{WIhPe{h, ic, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WIhFty{h, ic, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kfetch(fs, r2, 0))
    case 1n+p KCon{WIhFty{h, ic, ctx}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      km(p, KCon{WIhScanned{h, ic, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kih_scan_tin(fs, I.all_dom(node)))
    case 1n+p KCon{WIhScanned{h, ic, ctx}, k}
         Tuple{Tuple{fs, MIH{q, doms, eb}}, ri}:
      +ic2 : IC = ic
      +q2 : U32 = q
      +items : List<&2, U32> =
        List.append(&2, U32, ic_pre(ic2),
                    Con{I.nth_u(ic_fields(ic2), (h - 1 : U32),
                                4294967295), Nil{}})
      +first : U32 = head_u(items, 4294967295)
      km(p, KCon{kev(WP{0, 0, q2, 0, Nil{}, Nil{}, 2000000}, first),
                 KCon{WIhL{ktail(items), q2, Nil{},
                           I.take_u(I.skip_u(eb, ic_pp(ic2)), ic_ni(ic2),
                                    Nil{}),
                           doms, ic2, ctx}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, first, ri))
    case 1n+p KCon{WIhL{Nil{}, amt, lacc, ebni, doms, ic, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +ic2 : IC = ic
      km(p, KCon{WIhB{ic2, ctx}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kih_build(hcb, fs, krev(Con{ri, lacc}, Nil{}), ebni, doms, amt,
                   ic_cn(ic2), ic_us(ic2)))
    case 1n+p KCon{WIhL{Con{x, t}, amt, lacc, ebni, doms, ic, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      +a2 : U32 = amt
      km(p, KCon{kev(WP{0, 0, a2, 0, Nil{}, Nil{}, 2000000}, x2),
                 KCon{WIhL{t, a2, Con{ri, lacc}, ebni, doms, ic, ctx}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, x2, 0))
    case 1n+p KCon{WIhB{ic, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WIhNext{ic_push(ic, ri), ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, 0))
    # ---- resume frames for the walks ----
    case 1n+p KCon{KBvI{iseq, isgt, i, e}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kbv_fin(iseq, isgt, fs, ri, i, e, hcb))
    case 1n+p KCon{KAp2{wp, e, f0, a0}, k} Tuple{Tuple{fs, msg}, ri}:
      +w : WP = wp
      +a2 : U32 = a0
      km(p, KCon{kev(w, a2), KCon{KAp3{e, f0, a2, ri}, k}}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, a2, 0, w, hcb))
    case 1n+p KCon{KAp3{e, f0, a0, r1}, k} Tuple{Tuple{fs, msg}, ri}:
      +r1b : U32 = r1
      +rib : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kalloc_if(Bool.not(U32.is_eq(r1b, f0) && U32.is_eq(rib, a0)),
                   fs, T.EApp{r1b, rib}, e, hcb))
    case 1n+p KCon{KLm2{wp, e, n, t0, b0, bi}, k} Tuple{Tuple{fs, msg}, ri}:
      +b2 : U32 = b0
      +wb : WP = wp_bump(wp)
      km(p, KCon{kev(wb, b2), KCon{KLm3{e, n, t0, b2, bi, ri}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kfetch_w(fs, b2, 0, wb, hcb))
    case 1n+p KCon{KLm3{e, n, t0, b0, bi, r1}, k} Tuple{Tuple{fs, msg}, ri}:
      +r1b : U32 = r1
      +rib : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kalloc_if(Bool.not(U32.is_eq(r1b, t0) && U32.is_eq(rib, b0)),
                   fs, T.ELam{n, r1b, rib, bi}, e, hcb))
    case 1n+p KCon{KAl2{wp, e, n, t0, b0, bi}, k} Tuple{Tuple{fs, msg}, ri}:
      +b2 : U32 = b0
      +wb : WP = wp_bump(wp)
      km(p, KCon{kev(wb, b2), KCon{KAl3{e, n, t0, b2, bi, ri}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kfetch_w(fs, b2, 0, wb, hcb))
    case 1n+p KCon{KAl3{e, n, t0, b0, bi, r1}, k} Tuple{Tuple{fs, msg}, ri}:
      +r1b : U32 = r1
      +rib : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kalloc_if(Bool.not(U32.is_eq(r1b, t0) && U32.is_eq(rib, b0)),
                   fs, T.EAll{n, r1b, rib, bi}, e, hcb))
    case 1n+p KCon{KLt2{wp, e, n, t0, v0, b0}, k} Tuple{Tuple{fs, msg}, ri}:
      +w : WP = wp
      +v02 : U32 = v0
      km(p, KCon{kev(w, v02), KCon{KLt3{w, e, n, t0, v02, b0, ri}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch_w(fs, v02, 0, w, hcb))
    case 1n+p KCon{KLt3{wp, e, n, t0, v0, b0, r1}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +b2 : U32 = b0
      +wb : WP = wp_bump(wp)
      km(p, KCon{kev(wb, b2),
                 KCon{KLt4{e, n, t0, v0, b2, r1, ri}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kfetch_w(fs, b2, 0, wb, hcb))
    case 1n+p KCon{KLt4{e, n, t0, v0, b0, r1, r2}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r1b : U32 = r1
      +r2b : U32 = r2
      +rib : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kalloc_if(Bool.not(U32.is_eq(r1b, t0) && U32.is_eq(r2b, v0)
                            && U32.is_eq(rib, b0)),
                   fs, T.ELet{n, r1b, r2b, rib}, e, hcb))
    case 1n+p KCon{KPj2{e, tn, ix, s0}, k} Tuple{Tuple{fs, msg}, ri}:
      +rib : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kalloc_if(Bool.not(U32.is_eq(rib, s0)), fs,
                   T.EProj{tn, ix, rib}, e, hcb))

    # A frame/message combination no transition produces; unreachable by
    # construction (every eval frame follows a fetch), mapped to the error
    # sentinel rather than an abort.
    case 1n+p _ Tuple{Tuple{fs, msg}, ri}:
      ((fs, 4294967294), ((lnt, nlx), wm))

# --- entry points ------------------------------------------------------------
def klift(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>, +nlx: U32,
          +e: U32, +c: U32, +d: U32, +fu: U32, +hcb: U32)
    -> ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>):
  +e2 : U32 = e
  km(fuel, KCon{kev(WP{0, c, d, 0, Nil{}, Nil{}, fu}, e2), KNil{}}, lnt,
     nlx, R.TNil{}, R.TNil{}, R.TNil{}, R.TNil{}, 4294967295, R.TNil{},
     R.TNil{}, hcb, kfetch(fs, e2, 0))

def kinst(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>, +nlx: U32,
          +e: U32, +j: U32, +v: U32, +fu: U32, +hcb: U32)
    -> ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>):
  +e2 : U32 = e
  km(fuel, KCon{kev(WP{1, j, 0, v, Nil{}, Nil{}, fu}, e2), KNil{}}, lnt,
     nlx, R.TNil{}, R.TNil{}, R.TNil{}, R.TNil{}, 4294967295, R.TNil{},
     R.TNil{}, hcb, kfetch(fs, e2, 0))

def klsubst(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>, +nlx: U32,
            +e: U32, +ps: List<&2, U32>, +qs: List<&2, L.LN>, +fu: U32,
            +hcb: U32)
    -> ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>):
  +e2 : U32 = e
  km(fuel, KCon{kev(WP{2, 0, 0, 0, ps, qs, fu}, e2), KNil{}}, lnt, nlx,
     R.TNil{}, R.TNil{}, R.TNil{}, R.TNil{}, 4294967295, R.TNil{},
     R.TNil{}, hcb, kfetch(fs, e2, 0))

def ksl_test(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>,
             +nlx: U32, +lp: R.Tr<List<&2, U32>>, +nt: R.Tr<U32>, +e: U32,
             +ctx: List<&2, U32>, +want: L.LN, +hcb: U32)
    -> ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>):
  +e2 : U32 = e
  km(fuel, KCon{SLEv{e2, ctx, 2000000}, KCon{SLChk{want}, KNil{}}}, lnt, nlx,
     R.TNil{}, lp, R.TNil{}, R.TNil{}, 4294967295, R.TNil{}, nt, hcb,
     kfetch(fs, e2, 0))

def kdefeq(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>, +nlx: U32,
           +mt: R.Tr<I.Meta>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
           +qtt: R.Tr<U32>, +natn: U32, +wm: R.Tr<U32>, +nt: R.Tr<U32>,
           +xi: U32, +yi: U32, +ctx: List<&2, U32>, +same: Bool, +fu: U32,
           +hcb: U32)
    -> ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>):
  km(fuel, KCon{DSub{U32.is_eq(fu, 0), same, xi, yi, ctx, fu},
                KCon{DOut{}, KNil{}}},
     lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))

def kinfer(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>, +nlx: U32,
           +mt: R.Tr<I.Meta>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
           +qtt: R.Tr<U32>, +natn: U32, +wm: R.Tr<U32>, +nt: R.Tr<U32>,
           +xi: U32, +ctx: List<&2, U32>, +fu: U32, +hcb: U32)
    -> ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>):
  km(fuel, KCon{ISub{xi, ctx, fu}, KCon{IOut{}, KNil{}}}, lnt, nlx, mt,
     lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))

# the typed-check entry: whd the declared type, then the CkT pipeline
def fck_typed(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>,
              +nlx: U32, +mt: R.Tr<I.Meta>, +lp: R.Tr<List<&2, U32>>,
              +vt: R.Tr<U32>, +qtt: R.Tr<U32>, +natn: U32,
              +wm: R.Tr<U32>, +nt: R.Tr<U32>, +isthm: Bool, +ti: U32,
              +vi: U32, +hcb: U32)
    -> ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>):
  +t2 : U32 = ti
  km(fuel, KCon{DWhd{t2, Nil{}}, KCon{CkT1{isthm, vi, 1048576}, KNil{}}}, lnt, nlx,
     mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))

def kwhd(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>, +nlx: U32,
         +mt: R.Tr<I.Meta>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
         +qtt: R.Tr<U32>, +natn: U32, +wm: R.Tr<U32>, +nt: R.Tr<U32>,
         +i: U32, +hcb: U32)
    -> ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>):
  km(fuel, KCon{DWhd{i, Nil{}}, KNil{}}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
     knoop(fs, 0))

def kwhnf(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>, +nlx: U32,
          +mt: R.Tr<I.Meta>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
          +qtt: R.Tr<U32>, +natn: U32, +wm: R.Tr<U32>, +nt: R.Tr<U32>,
          +e: U32, +delta: Bool, +fu: U32, +hcb: U32)
    -> ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>):
  +e2 : U32 = e
  km(fuel, KCon{kwev(delta, e2, Nil{}, fu, Nil{}), KNil{}}, lnt, nlx, mt, lp, vt,
     qtt, natn, wm, nt, hcb, kfetch(fs, e2, 0))
