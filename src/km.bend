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
  # a level normal form (the sl universe oracle's answers)
  MLn{l: L.LN}
  # an inference result: a type index and the ok flag
  MIR{ty: U32, ok: Bool}
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
  # ---- definitional equality (infer.bend's defeq) ----
  # entry: fuel guard, same-index shortcut, then fetch both sides
  DSub{z0: Bool, same: Bool, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DEx{xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
  DEy{xn: T.Ex, xi: U32, yi: U32, ctx: List<&2, U32>, fu: U32}
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
  DIr2{t: L.Tri, hx: T.Ex, yi: U32, xi: U32, ctx: List<&2, U32>}
  DIrGo{gate: Bool, t: L.Tri, xi: U32, yi: U32, ctx: List<&2, U32>}
  DIr4{t: L.Tri, yi: U32, ctx: List<&2, U32>}
  DIr5{t: L.Tri, rx: U32, ctx: List<&2, U32>}
  DIr6{t: L.Tri, rx: U32, ry: U32, ctx: List<&2, U32>}
  DIr7{t: L.Tri, both: Bool, sameq: Bool}
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
  DBv6{a: U32, b: U32, wa: U32, samety: Bool, both: Bool,
       ctx: List<&2, U32>}
  DBv7{a: U32, b: U32, wa: U32, samety: Bool, both: Bool, rtok: Bool,
       ctx: List<&2, U32>}
  DBv8{a: U32, b: U32, wa: U32, samety: Bool, both: Bool, rtok: Bool,
       ctx: List<&2, U32>}
  DBv9{a: U32, b: U32, wa: U32, samety: Bool, both: Bool, part1: Bool,
       ctx: List<&2, U32>}
  DBv10{a: U32, b: U32, samety: Bool, both: Bool, isprop: Bool}
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
       rcty: U32, ind: U32, sargs: List<&2, U32>}
  RS2{pp: U32, ni: U32, mn: U32, kf: U32, rcty: U32, ind: U32,
      sargs: List<&2, U32>}
  RS3{wm2: U32, pp: U32, ni: U32, mn: U32, kf: U32, rcty: U32, ind: U32,
      sargs: List<&2, U32>}
  RS4{mn2: T.Ex, pp: U32, ni: U32, mn: U32, kf: U32, rcty: U32, ind: U32,
      sargs: List<&2, U32>}
  RSK{dok: Bool, base: Bool, pp: U32, ni: U32, mn: U32, rcty: U32,
      sargs: List<&2, U32>}
  RS5{base: Bool, pp: U32, ni: U32, mn: U32, sargs: List<&2, U32>}
  RS6{pok: Bool, base: Bool, pp: U32, ni: U32, mn: U32,
      sargs: List<&2, U32>}
  RS7{base: Bool, pok: Bool}
  # pairwise index comparison with the constant denial (k_idx_cmp)
  KI0{xs: List<&2, U32>, ys: List<&2, U32>, acc: L.Tri}
  KI1{a: U32, b: U32, ta: List<&2, U32>, tb: List<&2, U32>, acc: L.Tri}
  KI2{an: T.Ex, a: U32, b: U32, ta: List<&2, U32>, tb: List<&2, U32>,
      acc: L.Tri}
  KI3b{precond: Bool, t1: U32, t2: U32, ta: List<&2, U32>,
       tb: List<&2, U32>, acc: L.Tri}
  KIGo2{precond: Bool, e2: L.Tri, t1: U32, t2: U32, ta: List<&2, U32>,
        tb: List<&2, U32>, acc: L.Tri}
  KI4{e2: L.Tri, t1: U32, ta: List<&2, U32>, tb: List<&2, U32>,
      acc: L.Tri}
  KI5{e2: L.Tri, t1: U32, tqy: Bool, ta: List<&2, U32>,
      tb: List<&2, U32>, acc: L.Tri}
  KI6{e2: L.Tri, tqy: Bool, ta: List<&2, U32>, tb: List<&2, U32>,
      acc: L.Tri}
  # ---- type inference (infer.bend's infer) ----
  ISub{xi: U32, ctx: List<&2, U32>, fu: U32}
  IEvGo{z0: Bool, xi: U32, ctx: List<&2, U32>, fu: U32}
  IEv{xi: U32, ctx: List<&2, U32>, fu: U32}
  IAl3b{ty: U32, b: U32, ra: U32, raok: Bool, ctx: List<&2, U32>,
        fu: U32}
  IAl5b{ka: T.Ex, ra: U32, raok: Bool, rb: U32, rbok: Bool,
        ctx: List<&2, U32>, fu: U32}
  INatGo{bad: Bool}
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
  IAp2{a: U32, ctx: List<&2, U32>, fu: U32}
  IAp3{a: U32, rf: U32, rfok: Bool, ctx: List<&2, U32>, fu: U32}
  IAp3b{a: U32, rf: U32, rfok: Bool, ctx: List<&2, U32>, fu: U32}
  IAp4{a: U32, node: T.Ex, rf: U32, rfok: Bool, ctx: List<&2, U32>,
       fu: U32}
  IAp5{a: U32, node: T.Ex, ra: U32, raok: Bool, rf: U32, rfok: Bool,
       ctx: List<&2, U32>, fu: U32}
  IAp5Go{isyes: Bool, a: U32, node: T.Ex, ra: U32, raok: Bool, rf: U32,
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
  IPj6{ok: Bool, ppx: U32, pr: U32, tn: U32, idx: U32, sx: U32,
       sargs: List<&2, U32>, rs: U32, ctx: List<&2, U32>}
  IPj7{lsr: U32, ok: Bool, ppx: U32, pr: U32, tn: U32, idx: U32,
       sargs: List<&2, U32>, rs: U32, ctx: List<&2, U32>}
  IPj8{ok: Bool, ppx: U32, pr: U32, idx: U32, rs: U32,
       ctx: List<&2, U32>}
  IPj9{pt: U32, ok: Bool, ppx: U32, pr: U32, idx: U32, rs: U32,
       ctx: List<&2, U32>}
  IPj10{ok: Bool, ptok: Bool, isall: Bool, ppx: U32, pr: U32, idx: U32,
        rs: U32, fldty: U32}
  IPjOut{ok: Bool, rity: U32, ok2: Bool}
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
  DWhd{i: U32}
  DWhdGo{hit: Bool, h: U32, i: U32}
  DWhdSt{i: U32}
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
# --- hash-consing (proven in bench/hashcons.bend) -------------------------
# A region of the expression Array itself, [base, base+KMASK], is an open-
# addressing hash table: slot = base + (fingerprint & KMASK), linear probe.
# A fixed-K scan (always iterates, no early return -> no mutual recursion)
# finds the first structural match and the first empty slot; kalloc then
# shares, inserts, or overflow-appends at nx. Children are already
# hash-consed, so structural equality is tag + field-index equality (no
# recursion). This restores the export's DAG sharing through reduction, so
# the whnf memo hits and reduction stays linear.
def kmask() -> U32:
  65535

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
      kmix(kmix(kmix(kmix(kmix(2166136261, 5), n), t), b), bi)
    case T.EAll{n, t, b, bi}:
      kmix(kmix(kmix(kmix(kmix(2166136261, 6), n), t), b), bi)
    case T.ELet{n, t, v, b}:
      kmix(kmix(kmix(kmix(kmix(2166136261, 7), n), t), v), b)
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

def kscan(k: Nat, +base: U32, +node: T.Ex, +slot: U32, +found: U32,
          +fempty: U32, +stopped: Bool,
          pr: Array<T.Ex> & T.Ex) -> Array<T.Ex> & (U32 & U32):
  match k pr:
    case 0n Tuple{ex, cand}:
      (ex, (found, fempty))
    case 1n+p Tuple{ex, cand}:
      +cd : T.Ex = cand
      +eb : Bool = kis_bad(cd)
      +hit : Bool = Bool.not(stopped) && kexeq(cd, node)
                    && U32.is_eq(found, 4294967295)
      +f2 : U32 = kpu(hit, slot, found)
      +fe2 : U32 = kpu(eb && U32.is_eq(fempty, 4294967295), slot, fempty)
      +slot2 : U32 = knxt(base, slot)
      kscan(p, base, node, slot2, f2, fe2, Bool.or(stopped, eb),
            Array.get(T.Ex, ex, slot2))

def kfin2b(+miss: Bool, +fempty: U32, ex: Array<T.Ex>, +node: T.Ex,
           +nx: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match miss:
    case False{}:
      (((Array.set(T.Ex, ex, fempty, node), nx), MN{}), fempty)
    case True{}:
      +n : U32 = nx
      (((Array.set(T.Ex, ex, n, node), (n + 1 : U32)), MN{}), n)

def kfin1b(+miss: Bool, +found: U32, +fempty: U32, ex: Array<T.Ex>,
           +node: T.Ex, +nx: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match miss:
    case False{}:
      (((ex, nx), MN{}), found)
    case True{}:
      kfin2b(U32.is_eq(fempty, 4294967295), fempty, ex, node, nx)

def kfin(r: Array<T.Ex> & (U32 & U32), +node: T.Ex, +nx: U32,
         +base: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match r:
    case Tuple{ex, Tuple{found, fempty}}:
      +fd : U32 = found
      kfin1b(U32.is_eq(fd, 4294967295), fd, fempty, ex, node, nx)

def kalloc(fs: Array<T.Ex> & U32, +node: T.Ex,
           +base: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match fs:
    case Tuple{ex, nx}:
      +nd : T.Ex = node
      +s0 : U32 = (base + U32.and(kfp(nd), kmask()) : U32)
      kfin(kscan(24n, base, nd, s0, 4294967295, 4294967295, False{},
                 Array.get(T.Ex, ex, s0)),
           nd, nx, base)

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
         +fn2: U32, +base: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match aw:
    case 0:
      kalloc(fs, T.ENat{I.dec_add(da, db)}, base)
    case 1:
      kalloc(fs, T.ENat{I.dec_sub(da, db)}, base)
    case _:
      kalloc(fs, T.EConst{S.pick(I.dec_le(da, db), tn, fn2), Nil{}}, base)

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

# the oracle eval frame, fuel-guarded (the old sl's `case 0n`: unknown)
def kslev(+e: U32, +ctx: List<&2, U32>, +fu: U32) -> KF:
  pick_kf(U32.is_eq(fu, 0), SLUn{}, SLEv{e, ctx, fu})

# answer an inference result
def kmir(fs: Array<T.Ex> & U32, +ty: U32,
         +ok: Bool) -> ((Array<T.Ex> & U32) & MG) & U32:
  ((fs, MIR{ty, ok}), 0)

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
def kprojb(n: Nat, +i: U32, +tn: U32, +yi: U32,
           r: (Array<T.Ex> & U32) & U32) -> (Array<T.Ex> & U32) & U32:
  match n r:
    case 0n Tuple{fs, acc}:
      (fs, acc)
    case 1n+q Tuple{Tuple{ex, nx}, acc}:
      +n2 : U32 = nx
      kprojb(q, (i + 1 : U32), tn, yi,
             ((Array.set(T.Ex,
                         Array.set(T.Ex, ex, n2, T.EProj{tn, i, yi}),
                         (n2 + 1 : U32), T.EApp{acc, n2}),
               (n2 + 2 : U32)), (n2 + 1 : U32)))

# STUCK: nothing can reduce this term's head (infer.bend's rigid), with the
# spine head supplied by the caller
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

def kctor_headed(+x: T.Ex, +hd: T.Ex, +mt: R.Tr<I.Meta>) -> Bool:
  match x:
    case T.EApp{f, a}:
      I.meta_is_ctor(R.get(I.Meta, 32n, mt, I.const_nm2(hd), I.MNone{}))
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
      U32.is_eq(R.get(U32, 32n, vt, n2, 4294967295), 4294967295)
      && Bool.not(I.meta_is_rec(R.get(I.Meta, 32n, mt, n2, I.MNone{})))
      && Bool.not(U32.is_eq(n2, R.get(U32, 32n, qtt, 0, 4294967295)))
      && Bool.not(U32.is_eq(n2, R.get(U32, 32n, qtt, 1, 4294967295)))
      && Bool.not(U32.is_eq(n2, R.get(U32, 32n, qtt, 5, 4294967295)))
      && Bool.not(U32.is_eq(n2, R.get(U32, 32n, qtt, 6, 4294967295)))
      && Bool.not(U32.is_eq(n2, R.get(U32, 32n, qtt, 7, 4294967295)))
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
def kprojn_go(n: Nat, +i: U32, +tn: U32, +sx: U32, acc: List<&2, U32>,
              fs: Array<T.Ex> & U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  match n fs:
    case 0n Tuple{ex, nx}:
      (((ex, nx), MSP{T.EBad{}, I.rev_u(acc, Nil{})}), 0)
    case 1n+q Tuple{ex, nx}:
      +n2 : U32 = nx
      kprojn_go(q, (i + 1 : U32), tn, sx, Con{n2, acc},
                (Array.set(T.Ex, ex, n2, T.EProj{tn, i, sx}),
                 (n2 + 1 : U32)))

def kprojn_tin(fs: Array<T.Ex> & U32, +idx: U32, +tn: U32,
               +sx: U32) -> ((Array<T.Ex> & U32) & MG) & U32:
  kprojn_go(U32.to_nat(idx), 0, tn, sx, Nil{}, fs)

# not_a_type's shape half: 1 = definitely not a type by shape, 2 = a
# constant (decided by its declared type's head), 0 = neither
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
    # ---- eval: lift ----
    case 1n+p KCon{KEvL{c, d, e, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      match node:
        case T.EBVar{i}:
          km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kbv_lift(fs, i, e, c, d, hcb))
        case T.EApp{f, a}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +f2 : U32 = f
          km(p, KCon{kev(w, f2), KCon{KAp2{w, e, f2, a}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, f2, ri))
        case T.ELam{n, t, b, bi}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLm2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
        case T.EAll{n, t, b, bi}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KAl2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
        case T.ELet{n, t, v, b}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLt2{w, e, n, t2, v, b}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
        case T.EProj{tn, i, s}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +s2 : U32 = s
          km(p, KCon{kev(w, s2), KCon{KPj2{e, tn, i, s2}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, s2, ri))
        case _:
          km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, e))
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
             lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, tgt, ri))
        case T.EApp{f, a}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +f2 : U32 = f
          km(p, KCon{kev(w, f2), KCon{KAp2{w, e, f2, a}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, f2, ri))
        case T.ELam{n, t, b, bi}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLm2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
        case T.EAll{n, t, b, bi}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KAl2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
        case T.ELet{n, t, vv, b}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLt2{w, e, n, t2, vv, b}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
        case T.EProj{tn, i, s}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +s2 : U32 = s
          km(p, KCon{kev(w, s2), KCon{KPj2{e, tn, i, s2}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, s2, ri))
        case _:
          km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, e))
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
             S.pick(same, nl, (nl + 1 : U32)), mt, lp, vt, qtt, natn, wm, nt, hcb,
             ksort3(same, fs, nl, e, hcb))
        case T.EConst{n, us}:
          +r : LVS = klsub_lvls(us, lnt, nlx, ps, qs)
          km(p, k, lvs_t(r), lvs_nx(r), mt, lp, vt, qtt, natn, wm, nt, hcb,
             ksconst(fs, n, lvs_xs(r), hcb))
        case T.EApp{f, a}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +f2 : U32 = f
          km(p, KCon{kev(w, f2), KCon{KAp2{w, e, f2, a}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, f2, ri))
        case T.ELam{n, t, b, bi}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLm2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
        case T.EAll{n, t, b, bi}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KAl2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
        case T.ELet{n, t, v, b}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLt2{w, e, n, t2, v, b}, k}}, lnt,
             nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
        case T.EProj{tn, i, s}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +s2 : U32 = s
          km(p, KCon{kev(w, s2), KCon{KPj2{e, tn, i, s2}, k}}, lnt, nlx, mt,
             lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, s2, ri))
        case _:
          km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, e))
    # ---- whnf: rebuild on exhausted fuel ----
    case 1n+p KCon{WRb{e, args}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, krebuild(args, fs, e))
    # ---- whnf: eval (entry-level node dispatch; first match wins) ----
    case 1n+p KCon{WEv{delta, e, args, fu}, k}
         Tuple{Tuple{fs, MX{T.EApp{f, a}}}, ri}:
      +f2 : U32 = f
      km(p, KCon{kwev(delta, f2, Con{a, args}, (fu - 1 : U32)), k}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, f2, ri))
    case 1n+p KCon{WEv{delta, e, Con{a, rest}, fu}, k}
         Tuple{Tuple{fs, MX{T.ELam{n, t, b, bi}}}, ri}:
      +b2 : U32 = b
      km(p, KCon{kev(WP{1, 0, 0, a, Nil{}, Nil{}, 256}, b2),
                 KCon{WCont{delta, rest, (fu - 1 : U32)}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, b2, ri))
    case 1n+p KCon{WEv{delta, e, args, fu}, k}
         Tuple{Tuple{fs, MX{T.ELet{n, t, v, b}}}, ri}:
      +b2 : U32 = b
      km(p, KCon{kev(WP{1, 0, 0, v, Nil{}, Nil{}, 256}, b2),
                 KCon{WCont{delta, args, (fu - 1 : U32)}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, b2, ri))
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
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WEv{delta, e, args, fu}, k}
         Tuple{Tuple{fs, MX{T.EProj{tn, idx, sx}}}, ri}:
      +s2 : U32 = sx
      +f2 : U32 = (fu - 1 : U32)
      km(p, KCon{kwev(delta, s2, Nil{}, f2),
                 KCon{WPrj{delta, e, tn, idx, args, f2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, s2, ri))
    case 1n+p KCon{WEv{delta, e, args, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, krebuild(args, fs, e))
    # ---- whnf: continue on a substitution result ----
    case 1n+p KCon{WCont{delta, args, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{kwev(delta, r2, args, fu), k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
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
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, ri))
    case 1n+p KCon{WPh1{False{}, isue, can, delta, vi, ps, qs, e, args, fu,
                        pp, mn, mk, rcty, cn, p5}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WPh2{isue, can, delta, vi, ps, qs, e, args, fu, pp, mn,
                      cn, p5}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ---- telescope peel (ordered: the Pi case must precede the stuck one)
    case 1n+p KCon{WPlE{tyi, Nil{}}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, tyi))
    case 1n+p KCon{WPlE{tyi, Con{v, rest}}, k}
         Tuple{Tuple{fs, MX{T.EAll{n, t, b, bi}}}, ri}:
      +b2 : U32 = b
      km(p, KCon{kev(WP{1, 0, 0, v, Nil{}, Nil{}, 256}, b2),
                 KCon{WPlC{rest}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, b2, ri))
    case 1n+p KCon{WPlE{tyi, Con{v, rest}}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, 4294967295))
    case 1n+p KCon{WPlC{vals}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WPlE{r2, vals}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kfetch(fs, r2, 0))
    # ---- K: peel done -> spine of the peeled type ----
    case 1n+p KCon{WK2{isue, can, delta, vi, ps, qs, e, args, fu, pp, mn,
                       mk, cn, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WK3{U32.is_ne(r2, 4294967295), isue, can, delta, vi, ps,
                     qs, e, args, fu, pp, mn, mk, cn, p5}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
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
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         keq_lists_tin(fs, I.skip_u(sargs, p2),
                       I.take_u(I.skip_u(a2, (p2 + 1 + m2 : U32)), k2,
                                Nil{}),
                       lnt))
    # ---- K: verdict arrived ----
    case 1n+p KCon{WK4{pok, isue, can, delta, vi, ps, qs, e, args, fu, pp,
                       mn, mk, cn, p5}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{WKGo{Bool.and(pok, L.tri_is_yes(t)), isue, can, delta, vi,
                      ps, qs, e, args, fu, pp, mn, mk, cn, p5}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WKGo{True{}, isue, can, delta, vi, ps, qs, e, args, fu,
                        pp, mn, mk, cn, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +p2 : U32 = pp
      +mi2 : U32 = I.nth_u(a2, (p2 + 1 : U32), 4294967295)
      km(p, KCon{kwev(delta, mi2, I.skip_u(a2, (p2 + 1 + mn + mk + 1 : U32)),
                      (fu - 1 : U32)), k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, mi2, ri))
    case 1n+p KCon{WKGo{False{}, isue, can, delta, vi, ps, qs, e, args, fu,
                        pp, mn, mk, cn, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WPh2{isue, can, delta, vi, ps, qs, e, args, fu, pp, mn,
                      cn, p5}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ---- phase 2: unit-like structure eta ----
    case 1n+p KCon{WPh2{True{}, can, delta, vi, ps, qs, e, args, fu, pp,
                        mn, cn, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +p2 : U32 = pp
      +mi2 : U32 = I.nth_u(a2, (p2 + 1 : U32), 4294967295)
      km(p, KCon{kwev(delta, mi2, I.skip_u(a2, (p2 + 1 + mn + 1 : U32)),
                      (fu - 1 : U32)), k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, mi2, ri))
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
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ---- phase 3: literal arithmetic ----
    case 1n+p KCon{WPh3{True{}, aw, isq, qneed, can, delta, vi, ps, qs, e,
                        args, fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +a0 : U32 = I.nth_u(a2, 0, 4294967295)
      km(p, KCon{kwev(delta, a0, Nil{}, (fu - 1 : U32)),
                 KCon{WLa{aw, isq, qneed, can, delta, vi, ps, qs, e, a2,
                          fu, p5}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, a0, ri))
    case 1n+p KCon{WPh3{False{}, aw, isq, qneed, can, delta, vi, ps, qs, e,
                        args, fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WPh4{isq, qneed, can, delta, vi, ps, qs, e, args, fu, p5},
                 k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WLa{aw, isq, qneed, can, delta, vi, ps, qs, e, args,
                       fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +a1 : U32 = I.nth_u(a2, 1, 4294967295)
      km(p, KCon{kwev(delta, a1, Nil{}, (fu - 1 : U32)),
                 KCon{WLb{ri, aw, isq, qneed, can, delta, vi, ps, qs, e,
                          a2, fu, p5}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, a1, 0))
    case 1n+p KCon{WLb{r0, aw, isq, qneed, can, delta, vi, ps, qs, e, args,
                       fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = r0
      km(p, KCon{WLc{ri, aw, isq, qneed, can, delta, vi, ps, qs, e, args,
                     fu, p5}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{WLc{r1, aw, isq, qneed, can, delta, vi, ps, qs, e, args,
                       fu, p5}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +r2 : U32 = r1
      km(p, KCon{WLd{node, aw, isq, qneed, can, delta, vi, ps, qs, e, args,
                     fu, p5}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{WLd{na, aw, isq, qneed, can, delta, vi, ps, qs, e, args,
                       fu, p5}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +n1 : T.Ex = na
      +n2x : T.Ex = node
      km(p, KCon{WLGo{I.is_nat_lit(n1) && I.is_nat_lit(n2x), aw,
                      I.nat_digits(n1), I.nat_digits(n2x), isq, qneed, can,
                      delta, vi, ps, qs, e, args, fu, p5}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WLGo{True{}, aw, da, db, isq, qneed, can, delta, vi, ps,
                        qs, e, args, fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WCont{delta, I.skip_u(args, 2), (fu - 1 : U32)}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         klit(fs, aw, da, db, R.get(U32, 32n, qtt, 8, 4294967295),
              R.get(U32, 32n, qtt, 9, 4294967295), hcb))
    case 1n+p KCon{WLGo{False{}, aw, da, db, isq, qneed, can, delta, vi,
                        ps, qs, e, args, fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WPh4{isq, qneed, can, delta, vi, ps, qs, e, args, fu, p5},
                 k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ---- phase 4: quotient reduction ----
    case 1n+p KCon{WPh4{True{}, qneed, can, delta, vi, ps, qs, e, args,
                        fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +q2 : U32 = qneed
      +qm : U32 = I.nth_u(a2, q2, 4294967295)
      km(p, KCon{kwev(delta, qm, Nil{}, (fu - 1 : U32)),
                 KCon{WQ1{q2, can, delta, vi, ps, qs, e, a2, fu, p5},
                      k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, qm, ri))
    case 1n+p KCon{WPh4{False{}, qneed, can, delta, vi, ps, qs, e, args,
                        fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WPh5{p5, can, delta, vi, ps, qs, e, args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WQ1{qneed, can, delta, vi, ps, qs, e, args, fu, p5}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WQ2{qneed, can, delta, vi, ps, qs, e, args, fu, p5}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, r2, 0))
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
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WQGo{True{}, fv, vv, qneed, can, delta, vi, ps, qs, e,
                        args, fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WCont{delta, I.skip_u(args, (qneed + 1 : U32)),
                       (fu - 1 : U32)}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kalloc(fs, T.EApp{fv, vv}, hcb))
    case 1n+p KCon{WQGo{False{}, fv, vv, qneed, can, delta, vi, ps, qs, e,
                        args, fu, p5}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WPh5{p5, can, delta, vi, ps, qs, e, args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ---- whnf: delta branch ----
    case 1n+p KCon{WDelGo{True{}, delta, vi, ps, qs, e, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +v2 : U32 = vi
      km(p, KCon{kev(WP{2, 0, 0, 0, ps, qs, 256}, v2),
                 KCon{WCont{delta, args, (fu - 1 : U32)}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, v2, ri))
    case 1n+p KCon{WDelGo{False{}, delta, vi, ps, qs, e, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, krebuild(args, fs, e))
    # ---- whnf: projection, struct reduced -> collect its spine ----
    case 1n+p KCon{WPrj{delta, e, tn, idx, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WPrjS{delta, e, tn, idx, args, fu}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, r2, r2))
    # ---- whnf: projection, spine collected -> constructor? ----
    case 1n+p KCon{WPrjS{delta, e, tn, idx, args, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +cmi : I.Meta = R.get(I.Meta, 32n, mt, I.const_nm2(hd), I.MNone{})
      km(p, KCon{WPrjGo{I.meta_is_ctor(cmi), delta, e,
                        I.nth_u(sargs, (I.meta_p(cmi) + idx : U32),
                                4294967295),
                        args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ---- whnf: projection branch ----
    case 1n+p KCon{WPrjGo{True{}, delta, e, fld, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +f2 : U32 = fld
      km(p, KCon{kwev(delta, f2, args, fu), k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kfetch(fs, f2, ri))
    case 1n+p KCon{WPrjGo{False{}, delta, e, fld, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, krebuild(args, fs, e))
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
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, maj, ri))
    case 1n+p KCon{WPh5{P5{False{}, need, ind, pp, mk, cn, us}, can, delta,
                        vi, ps, qs, e, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WDelGo{can, delta, vi, ps, qs, e, args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WI1{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs,
                       e, args, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WI2{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs, e,
                     args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, r2))
    case 1n+p KCon{WI2{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs,
                       e, args, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +i2 : U32 = ind
      +nd : T.Ex = node
      km(p, KCon{WI2Go{I.is_nat_lit(nd) && U32.is_eq(i2, natn),
                       I.nat_digits(nd), ri, need, i2, pp, mk, cn, us, can,
                       delta, vi, ps, qs, e, args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{WI2Go{True{}, d, orig, need, ind, pp, mk, cn, us, can,
                         delta, vi, ps, qs, e, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WI2b{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs, e,
                      args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         knatexp(fs, d, R.get(U32, 32n, qtt, 3, 4294967295),
                 R.get(U32, 32n, qtt, 4, 4294967295)))
    case 1n+p KCon{WI2Go{False{}, d, orig, need, ind, pp, mk, cn, us, can,
                         delta, vi, ps, qs, e, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WI2b{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs, e,
                      args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, orig))
    case 1n+p KCon{WI2b{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs,
                        e, args, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WI3{need, ind, pp, mk, cn, us, can, delta, vi, ps, qs, e,
                     args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, r2, 0))
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
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WIGo{True{}, fields, recsl, ci, ccty, need, pp, mk, cn,
                        us, can, delta, vi, ps, qs, e, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +n2 : U32 = need
      km(p, KCon{WIhNext{IC{recsl, cn, us,
                            I.take_u(a2, (n2 - mk : U32), Nil{}), fields,
                            ccty, pp, mk, Nil{}, ci, n2, can, delta, vi,
                            ps, qs, e, a2, fu}}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{WIGo{False{}, fields, recsl, ci, ccty, need, pp, mk, cn,
                        us, can, delta, vi, ps, qs, e, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WDelGo{can, delta, vi, ps, qs, e, args, fu}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ---- definitional equality ----
    case 1n+p KCon{DSub{True{}, same, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TUnk{}))
    case 1n+p KCon{DSub{False{}, True{}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TYes{}))
    case 1n+p KCon{DSub{False{}, False{}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = xi
      km(p, KCon{DEx{x2, yi, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, kfetch(fs, x2, ri))
    case 1n+p KCon{DEx{xi, yi, ctx, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +y2 : U32 = yi
      km(p, KCon{DEy{node, xi, y2, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kfetch(fs, y2, ri))
    # -- Sort/Sort --
    case 1n+p KCon{DEy{T.ESort{a}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.ESort{b}}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.ln_cmp(R.get(L.LN, 32n, lnt, a, L.LNun{}),
                            R.get(L.LN, 32n, lnt, b, L.LNun{}))))
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
      km(p, KCon{kev(WP{0, 0, (a2 + 1 : U32), 0, Nil{}, Nil{}, 256}, t2),
                 KCon{DBv1{a2, b2, tb, Bool.not(U32.is_eq(t2,
                                                          4294967295)),
                           Bool.not(U32.is_eq(tb, 4294967295)), c2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
    case 1n+p KCon{DBv1{a, b, tb, taok, tbok, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +t2 : U32 = tb
      +b2 : U32 = b
      km(p, KCon{kev(WP{0, 0, (b2 + 1 : U32), 0, Nil{}, Nil{}, 256}, t2),
                 KCon{DBv2{a, b2, ri, taok, tbok, ctx}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, 0))
    case 1n+p KCon{DBv2{a, b, la, taok, tbok, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +l2 : U32 = la
      km(p, KCon{DWhd{l2}, KCon{DBv3{a, b, ri, taok, tbok, ctx}, k}}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DBv3{a, b, lb, taok, tbok, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +l2 : U32 = lb
      km(p, KCon{DWhd{l2}, KCon{DBv4{a, b, ri, taok, tbok, ctx}, k}}, lnt,
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
      km(p, KCon{DTy1{c2},
                 KCon{DBv6{a, b, w2, L.tri_is_yes(t),
                           Bool.and(taok, tbok), c2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, w2, ri))
    case 1n+p KCon{DBv6{a, b, wa, samety, both, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{DWhd{r2}, KCon{DBv7{a, b, wa, samety, both,
                                     Bool.not(U32.is_eq(r2, 4294967295)),
                                     ctx}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DBv7{a, b, wa, samety, both, rtok, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{DBv8{a, b, wa, samety, both, rtok, ctx}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{DBv8{a, b, wa, samety, both, rtok, ctx}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
      +ks : T.Ex = node
      +w2 : U32 = wa
      km(p, KCon{kslev(w2, ctx, 256),
                 KCon{DBv9{a, b, w2, samety, both,
                           rtok && I.is_sortx(ks)
                           && L.tri_is_yes(L.ln_is_zero(
                                R.get(L.LN, 32n, lnt, I.sort_lvl_of(ks),
                                      L.LNun{}))), ctx}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, w2, ri))
    case 1n+p KCon{DBv9{a, b, wa, samety, both, part1, ctx}, k}
         Tuple{Tuple{fs, MLn{u}}, ri}:
      +w2 : U32 = wa
      km(p, KCon{DBv10{a, b, samety, both,
                       Bool.or(part1,
                               L.tri_is_yes(L.ln_is_zero(u)))}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, w2, ri))
    case 1n+p KCon{DBv10{a, b, samety, both, isprop}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +smi : I.Meta = R.get(I.Meta, 32n, mt, I.const_nm2(hd), I.MNone{})
      +isunit : Bool = I.meta_is_ind(smi)
                       && U32.is_eq(I.meta_nf(smi), 0)
      +b3 : Bool = both
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.pick_tri(U32.is_eq(a, b), L.TYes{},
                    L.pick_tri(b3 && samety && (isprop || isunit),
                               L.TYes{},
                               L.pick_tri(b3, L.TNo{}, L.TUnk{})))))
    # -- Const/Const --
    case 1n+p KCon{DEy{T.EConst{a, us}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EConst{b, vs}}}, ri}:
      +a2 : U32 = a
      +b2 : U32 = b
      +ta : U32 = R.get(U32, 32n, nt, a2, 4294967295)
      +tb : U32 = R.get(U32, 32n, nt, b2, 4294967295)
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
      km(p, KCon{kslev(t2, ctx, 256),
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
      +novals : Bool = U32.is_eq(R.get(U32, 32n, vt, a2, 4294967295),
                                 4294967295)
                       && U32.is_eq(R.get(U32, 32n, vt, b2, 4294967295),
                                    4294967295)
      +hasval : Bool = Bool.not(U32.is_eq(R.get(U32, 32n, vt, a2,
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
    case 1n+p KCon{DEy{T.EAll{n1, t1, b1, i1}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EAll{n2, t2, b2, i2}}}, ri}:
      +t12 : U32 = t1
      km(p, KCon{DWhd{t12}, KCon{DAl2{0, t12, t2, b1, b2, ctx, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DAl2{w1, t1, t2, b1, b2, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +t22 : U32 = t2
      km(p, KCon{DWhd{t22}, KCon{DAl2b{ri, t1, t22, b1, b2, ctx, fu}, k}},
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
      +b12 : U32 = b1
      km(p, KCon{DWhd{b12}, KCon{DAl4{t, b12, b2, t1, ctx, fu}, k}}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DAl4{d1, b1, b2, t1, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +b22 : U32 = b2
      km(p, KCon{DWhd{b22}, KCon{DAl5{d1, ri, b1, b22, t1, ctx, fu}, k}},
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
      +b12 : U32 = b1
      km(p, KCon{DWhd{b12}, KCon{DLm3{0, b12, b2, t1, ctx, fu}, k}}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DLm3{w3, b1, b2, t1, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +b22 : U32 = b2
      km(p, KCon{DWhd{b22}, KCon{DLm3b{ri, b1, b22, t1, ctx, fu}, k}}, lnt,
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
    case 1n+p KCon{DEy{T.EApp{f1, a1}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EApp{f2, a2}}}, ri}:
      +f12 : U32 = f1
      +f22 : U32 = f2
      km(p, KCon{DAq1{f12, f22, a1, a2, xi, yi, ctx, fu}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb,
         keq_lists_tin(fs, Con{f12, Nil{}}, Con{f22, Nil{}}, lnt))
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
      km(p, KCon{DWhd{a12}, KCon{DAq4{L.TYes{}, a12, a2, xi, yi, ctx, fu},
                                 k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DAqGo{False{}, f1, f2, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +f12 : U32 = f1
      km(p, KCon{DWhd{f12}, KCon{DAq2{f12, f2, a1, a2, xi, yi, ctx, fu},
                                 k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DAq2{f1, f2, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +f22 : U32 = f2
      km(p, KCon{DWhd{f22}, KCon{DAq3{ri, f1, f22, a1, a2, xi, yi, ctx,
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
      +a12 : U32 = a1
      km(p, KCon{DWhd{a12}, KCon{DAq4{t, a12, a2, xi, yi, ctx, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DAq4{d1, a1, a2, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +a22 : U32 = a2
      km(p, KCon{DWhd{a22}, KCon{DAq5{d1, ri, a1, a22, xi, yi, ctx, fu},
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
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.pick_tri(I.eq_u32s(d1, d2), L.TYes{}, L.TUnk{})))
    # -- function eta, lambda on the left --
    case 1n+p KCon{DEy{T.ELam{n1, t1, b1, i1}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +y2 : U32 = yi
      km(p, KCon{kev(WP{0, 0, 1, 0, Nil{}, Nil{}, 256}, y2),
                 KCon{DEtL1{t1, b1, ctx, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, y2, ri))
    case 1n+p KCon{DEtL1{t1, b1, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DEtL2{ri, t1, b1, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kalloc(fs, T.EBVar{0}, hcb))
    case 1n+p KCon{DEtL2{ly, t1, b1, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DEtL3{t1, b1, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kalloc(fs, T.EApp{ly, ri}, hcb))
    case 1n+p KCon{DEtL3{t1, b1, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +b12 : U32 = b1
      km(p, KCon{DWhd{b12}, KCon{DEtL4{ri, t1, ctx, fu}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DEtL4{ap, t1, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +a2 : U32 = ap
      km(p, KCon{DWhd{a2}, KCon{DEtL5{ri, t1, ctx, fu}, k}}, lnt, nlx, mt,
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
      km(p, KCon{kev(WP{0, 0, 1, 0, Nil{}, Nil{}, 256}, x2),
                 KCon{DEtR1{t2, b2, ctx, fu}, k}},
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
      km(p, KCon{DWhd{a2}, KCon{DEtR4{a2, t2, b2, ctx, fu}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DEtR4{ap, t2, b2, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +b22 : U32 = b2
      km(p, KCon{DWhd{b22}, KCon{DEtR5{ri, t2, ctx, fu}, k}}, lnt, nlx,
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
    case 1n+p KCon{DEy{T.ENat{d}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +y2 : U32 = yi
      km(p, KCon{DWhd{y2}, KCon{DNtL1{d, ctx, fu}, k}}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
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
    case 1n+p KCon{DNtL3{False{}, d, wy, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DNtL4{False{}, wy, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb,
         knatexp(fs, d, R.get(U32, 32n, qtt, 3, 4294967295),
                 R.get(U32, 32n, qtt, 4, 4294967295)))
    case 1n+p KCon{DNtL4{islit, wy, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +f2 : U32 = fu
      +r2 : U32 = ri
      +w2 : U32 = wy
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295), False{}, r2,
                      w2, ctx, (f2 - 1 : U32)},
                 KCon{DNtL5{islit}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{DNtL5{islit}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      +t2 : L.Tri = t
      +i2 : Bool = islit
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.pick_tri(i2, t2,
                              L.pick_tri(L.tri_is_no(t2), L.TUnk{}, t2))))
    case 1n+p KCon{DEy{xn, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.ENat{d}}}, ri}:
      +x2 : U32 = xi
      km(p, KCon{DWhd{x2}, KCon{DNtR1{d, ctx, fu}, k}}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
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
    case 1n+p KCon{DNtR3{False{}, d, wx, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{DNtR4{False{}, wx, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb,
         knatexp(fs, d, R.get(U32, 32n, qtt, 3, 4294967295),
                 R.get(U32, 32n, qtt, 4, 4294967295)))
    case 1n+p KCon{DNtR4{islit, wx, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +f2 : U32 = fu
      +r2 : U32 = ri
      +w2 : U32 = wx
      km(p, KCon{DSub{U32.is_eq((f2 - 1 : U32), 4294967295), False{}, w2,
                      r2, ctx, (f2 - 1 : U32)},
                 KCon{DNtL5{islit}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
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
                       R.get(I.Meta, 32n, mt, I.const_nm2(hxl),
                             I.MNone{})))
                     && I.meta_is_ctor(R.get(I.Meta, 32n, mt,
                                             I.const_nm2(hyr), I.MNone{}))
      +hdp : T.Ex = I.pick_exx(swap, hyr, hxl)
      +cmi : I.Meta = R.get(I.Meta, 32n, mt, I.const_nm2(hdp), I.MNone{})
      +sx2 : List<&2, U32> = sx
      +sy2 : List<&2, U32> = sargs
      +xn2 : T.Ex = xn
      +yn2 : T.Ex = yn
      +xi2 : U32 = xi
      +yi2 : U32 = yi
      km(p, KCon{DCGo{I.meta_is_ctor(cmi)
                      && I.meta_is_ind(R.get(I.Meta, 32n, mt,
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
         ktin_of(kprojb(U32.to_nat(cnf), 0, cind, pyi,
                        kapargs(tk, (fs, ri)))))
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
      +mi : I.Meta = R.get(I.Meta, 32n, mt, I.const_nm2(h2), I.MNone{})
      +s2 : List<&2, U32> = spx
      +pp : U32 = I.meta_p(mi)
      +ni : U32 = I.meta_k(mi)
      +mn : U32 = I.meta_n(mi)
      +nmj : U32 = (pp + 1 + mn + ni : U32)
      +ok0 : Bool = I.meta_is_rec(mi) && U32.is_gt(I.len_u(s2, 0), nmj)
      km(p, KCon{RSGo{ok0, I.nth_u(s2, nmj, 4294967295), pp, ni, mn,
                      I.meta_kf(mi), I.meta_rcty(mi), I.meta_ind(mi), s2},
                 KCon{DCr2{False{}, pxi, pyi, pyn, hdy, spy, ctx, fu},
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
      +mi : I.Meta = R.get(I.Meta, 32n, mt, I.const_nm2(h2), I.MNone{})
      +s2 : List<&2, U32> = spy
      +pp : U32 = I.meta_p(mi)
      +ni : U32 = I.meta_k(mi)
      +mn : U32 = I.meta_n(mi)
      +nmj : U32 = (pp + 1 + mn + ni : U32)
      km(p, KCon{RSGo{I.meta_is_rec(mi)
                      && U32.is_gt(I.len_u(s2, 0), nmj),
                      I.nth_u(s2, nmj, 4294967295), pp, ni, mn,
                      I.meta_kf(mi), I.meta_rcty(mi), I.meta_ind(mi), s2},
                 KCon{DCr5{pxi, pyi, ctx, fu}, k}},
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
      +r2 : U32 = ri
      km(p, KCon{kslev(r2, ctx, 256),
                 KCon{DRg3{Bool.not(U32.is_eq(r2, 4294967295)), pxi, pyi,
                           ctx, fu}, k}},
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
      +x2 : U32 = pxi
      km(p, KCon{DWhd{x2}, KCon{DDl2{pyi, x2, ctx}, k}}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DDl2{pyi, pxi, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +y2 : U32 = pyi
      km(p, KCon{DWhd{y2}, KCon{DDl3{ri, pxi, y2, ctx}, k}}, lnt, nlx, mt,
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
    case 1n+p KCon{RSGo{False{}, maj, pp, ni, mn, kf, rcty, ind, sargs},
                   k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, 0))
    case 1n+p KCon{RSGo{True{}, maj, pp, ni, mn, kf, rcty, ind, sargs}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +m2 : U32 = maj
      km(p, KCon{DWhd{m2}, KCon{RS2{pp, ni, mn, kf, rcty, ind, sargs},
                                k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{RS2{pp, ni, mn, kf, rcty, ind, sargs}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{RS3{r2, pp, ni, mn, kf, rcty, ind, sargs}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{RS3{wm2, pp, ni, mn, kf, rcty, ind, sargs}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
      +w2 : U32 = wm2
      km(p, KCon{RS4{node, pp, ni, mn, kf, rcty, ind, sargs}, k}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, w2, ri))
    case 1n+p KCon{RS4{mn2, pp, ni, mn, kf, rcty, ind, sargs}, k}
         Tuple{Tuple{fs, MSP{hd, sargs2}}, ri}:
      +m2 : T.Ex = mn2
      +h2 : T.Ex = hd
      +cmi2 : I.Meta = R.get(I.Meta, 32n, mt, I.const_nm2(h2), I.MNone{})
      +uind2 : I.Meta = R.get(I.Meta, 32n, mt, ind, I.MNone{})
      +k2 : U32 = kf
      km(p, KCon{RSK{U32.is_eq(k2, 1),
                     (krigid(m2, h2)
                      && Bool.not(I.meta_is_ctor(cmi2)))
                     && Bool.not(I.meta_is_ind(uind2)
                                 && U32.is_eq(I.meta_nf(uind2), 0)),
                     pp, ni, mn, rcty, sargs}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{RSK{False{}, base, pp, ni, mn, rcty, sargs}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kkeep(fs, S.pick(base, 1, 0)))
    case 1n+p KCon{RSK{True{}, base, pp, ni, mn, rcty, sargs}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +p2 : U32 = pp
      +r2 : U32 = rcty
      +s2 : List<&2, U32> = sargs
      km(p, KCon{WPlE{r2, I.take_u(s2, p2, Nil{})},
                 KCon{RS5{base, p2, ni, mn, s2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, ri))
    case 1n+p KCon{RS5{base, pp, ni, mn, sargs}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{RS6{U32.is_ne(r2, 4294967295), base, pp, ni, mn, sargs},
                 k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kspine_tin(fs, S.pick(U32.is_ne(r2, 4294967295), r2, 0), 0))
    case 1n+p KCon{RS6{pok, base, pp, ni, mn, sargs}, k}
         Tuple{Tuple{fs, MSP{hd, sargs2}}, ri}:
      +p2 : U32 = pp
      +s2 : List<&2, U32> = sargs
      km(p, KCon{KI0{I.skip_u(sargs2, p2),
                     I.take_u(I.skip_u(s2, (p2 + 1 + mn : U32)), ni,
                              Nil{}), L.TYes{}},
                 KCon{RS7{base, pok}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{RS7{base, pok}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      +b2 : Bool = base
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kkeep(fs, S.pick(Bool.and(b2,
                                   Bool.and(pok, L.tri_is_no(t))), 1,
                          0)))
    # k_idx_cmp: pairwise with the constant denial
    case 1n+p KCon{KI0{Nil{}, Nil{}, acc}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, acc))
    case 1n+p KCon{KI0{Nil{}, Con{b, tb}, acc}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TUnk{}))
    case 1n+p KCon{KI0{Con{a, ta}, Nil{}, acc}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.TUnk{}))
    case 1n+p KCon{KI0{Con{a, ta}, Con{b, tb}, acc}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +a2 : U32 = a
      km(p, KCon{KI1{a2, b, ta, tb, acc}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kfetch(fs, a2, ri))
    case 1n+p KCon{KI1{a, b, ta, tb, acc}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +b2 : U32 = b
      km(p, KCon{KI2{node, a, b2, ta, tb, acc}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kfetch(fs, b2, 0))
    case 1n+p KCon{KI2{an, a, b, ta, tb, acc}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
      +an2 : T.Ex = an
      +bn2 : T.Ex = node
      +n1 : U32 = I.const_nm2(an2)
      +n2x : U32 = I.const_nm2(bn2)
      +t12 : U32 = R.get(U32, 32n, nt, n1, 4294967295)
      +t22 : U32 = R.get(U32, 32n, nt, n2x, 4294967295)
      +precond : Bool = kis_cc(an2, bn2)
                        && Bool.not(U32.is_eq(n1, n2x))
                        && U32.is_eq(R.get(U32, 32n, vt, n1, 4294967295),
                                     4294967295)
                        && U32.is_eq(R.get(U32, 32n, vt, n2x,
                                           4294967295), 4294967295)
                        && Bool.not(U32.is_eq(t12, 4294967295))
      +a2 : U32 = a
      +b2 : U32 = b
      km(p, KCon{KI3b{precond, t12, t22, ta, tb, acc}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb,
         keq_lists_tin(fs, Con{a2, Nil{}}, Con{b2, Nil{}}, lnt))
    case 1n+p KCon{KI3b{precond, t1, t2, ta, tb, acc}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      km(p, KCon{KIGo2{precond, t, t1, t2, ta, tb, acc}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{KIGo2{False{}, e2, t1, t2, ta, tb, acc}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{KI0{ta, tb, I.tri_and2(e2, acc)}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{KIGo2{True{}, e2, t1, t2, ta, tb, acc}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +t12 : U32 = t1
      +t22 : U32 = t2
      km(p, KCon{KI4{e2, t12, ta, tb, acc}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb,
         keq_lists_tin(fs, Con{t12, Nil{}}, Con{t22, Nil{}}, lnt))
    case 1n+p KCon{KI4{e2, t1, ta, tb, acc}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +t12 : U32 = t1
      km(p, KCon{kslev(t12, Nil{}, 256),
                 KCon{KI6{e2, L.tri_is_yes(t), ta, tb, acc}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t12, ri))
    case 1n+p KCon{KI6{e2, tqy, ta, tb, acc}, k}
         Tuple{Tuple{fs, MLn{u}}, ri}:
      +d2 : L.Tri = L.pick_tri(Bool.and(tqy,
                                        L.tri_is_no(L.ln_is_zero(u))),
                               L.TNo{}, e2)
      km(p, KCon{KI0{ta, tb, I.tri_and2(d2, acc)}, k}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ---- type inference ----
    case 1n+p KCon{ISub{xi, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +f2 : U32 = fu
      +x2 : U32 = xi
      km(p, KCon{IEvGo{U32.is_eq(f2, 0), x2, ctx, f2}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IEvGo{True{}, xi, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, 4294967295, False{}))
    case 1n+p KCon{IEvGo{False{}, xi, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = xi
      km(p, KCon{IEv{x2, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, kfetch(fs, x2, ri))
    # -- Sort --
    case 1n+p KCon{IEv{xi, ctx, fu}, k} Tuple{Tuple{fs, MX{T.ESort{l}}}, ri}:
      +u : L.LN = L.ln_succ(R.get(L.LN, 32n, lnt, l, L.LNun{}))
      +u2 : L.LN = u
      km(p, KCon{ISrtGo{L.is_un(u2), u2}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{ISrtGo{True{}, u}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, 4294967295, False{}))
    case 1n+p KCon{ISrtGo{False{}, u}, k} Tuple{Tuple{fs, msg}, ri}:
      +nl : U32 = nlx
      km(p, KCon{IWrap{True{}}, k},
         R.set(L.LN, 32n, lnt, nl, u, L.LNun{}), (nl + 1 : U32), mt, lp,
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
      +t2 : U32 = t
      km(p, KCon{DWhd{t2}, KCon{IAl3{ty, b, t2, ok, ctx, fu}, k}}, lnt,
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
      +t2 : U32 = t
      km(p, KCon{DWhd{t2}, KCon{IAl5{ka, ra, raok, t2, ok, ctx, fu}, k}},
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
      +u : L.LN = L.ln_imax(R.get(L.LN, 32n, lnt, I.sort_lvl_of(ka),
                                  L.LNun{}),
                            R.get(L.LN, 32n, lnt, I.sort_lvl_of(kb),
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
      km(p, KCon{kev(WP{0, 0, (i2 + 1 : U32), 0, Nil{}, Nil{}, 256}, t2),
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
    case 1n+p KCon{IEv{xi, ctx, fu}, k} Tuple{Tuple{fs, MX{T.EStr{d}}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, 4294967295, False{}))
    # -- Const --
    case 1n+p KCon{IEv{xi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EConst{n, us}}}, ri}:
      +n2 : U32 = n
      +ti : U32 = R.get(U32, 32n, nt, n2, 4294967295)
      +t2 : U32 = ti
      km(p, KCon{ICnGo{U32.is_eq(t2, 4294967295), t2,
                       R.get(List<&2, U32>, 32n, lp, n2, Nil{}),
                       klns_of(us, lnt)}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{ICnGo{True{}, ti, ps, qs}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, 4294967295, False{}))
    case 1n+p KCon{ICnGo{False{}, ti, ps, qs}, k} Tuple{Tuple{fs, msg}, ri}:
      +t2 : U32 = ti
      km(p, KCon{kev(WP{2, 0, 0, 0, ps, qs, 256}, t2),
                 KCon{IWrap{True{}}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
    # -- Let --
    case 1n+p KCon{IEv{xi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.ELet{n, ty, v, b}}}, ri}:
      +b2 : U32 = b
      +f2 : U32 = fu
      km(p, KCon{kev(WP{1, 0, 0, v, Nil{}, Nil{}, 256}, b2),
                 KCon{ILt2{ctx, (f2 - 1 : U32)}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, b2, ri))
    case 1n+p KCon{ILt2{ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{ISub{r2, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, knoop(fs, 0))
    # -- App --
    case 1n+p KCon{IEv{xi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EApp{f, a}}}, ri}:
      +f3 : U32 = f
      +fu2 : U32 = fu
      km(p, KCon{ISub{f3, ctx, (fu2 - 1 : U32)},
                 KCon{IAp2{a, ctx, fu2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IAp2{a, ctx, fu}, k} Tuple{Tuple{fs, MIR{t, ok}}, ri}:
      +t2 : U32 = t
      km(p, KCon{kwev(True{}, t2, Nil{}, 256),
                 KCon{IAp3{a, t2, ok, ctx, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
    case 1n+p KCon{IAp3{a, rf, rfok, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{IAp3b{a, rf, rfok, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{IAp3b{a, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
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
      km(p, KCon{IAp5{a, nd2, t2, ok, rf, rfok, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb,
         keq_lists_tin(fs, Con{t2, Nil{}},
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
      +r2 : U32 = ra
      km(p, KCon{DWhd{r2}, KCon{IAp5c{a, node, r2, raok, rf, rfok, ctx,
                                      fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IAp5c{a, node, ra, raok, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +nd2 : T.Ex = node
      km(p, KCon{DWhd{I.all_dom(nd2)},
                 KCon{IAp5d{ri, a, nd2, ra, raok, rf, rfok, ctx, fu}, k}},
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
    case 1n+p KCon{IAp6Go{False{}, w1, w2, a, node, ra, raok, rf, rfok,
                          ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +w12 : U32 = w1
      +w22 : U32 = w2
      km(p, KCon{DSub{False{}, U32.is_eq(w12, w22), w12, w22, ctx, 24},
                 KCon{IAp7{a, node, ra, raok, rf, rfok, ctx, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
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
      km(p, KCon{kev(WP{1, 0, 0, a2, Nil{}, Nil{}, 256},
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
      +s2 : U32 = sx
      +fu2 : U32 = fu
      km(p, KCon{ISub{s2, ctx, (fu2 - 1 : U32)},
                 KCon{IPj2{tn, idx, s2, ctx, fu2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IPj2{tn, idx, sx, ctx, fu}, k}
         Tuple{Tuple{fs, MIR{t, ok}}, ri}:
      +t2 : U32 = t
      km(p, KCon{DWhd{t2}, KCon{IPj3{tn, idx, sx, t2, ok, ctx, fu}, k}},
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
    case 1n+p KCon{IPj5{tn, idx, sx, sty, rs, rsok, ctx, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +tn2 : U32 = tn
      +i2 : U32 = idx
      +h2 : T.Ex = hd
      +mi : I.Meta = R.get(I.Meta, 32n, mt, tn2, I.MNone{})
      +cty : U32 = I.meta_cty(mi)
      km(p, KCon{kev(WP{2, 0, 0, 0,
                        R.get(List<&2, U32>, 32n, lp, tn2, Nil{}),
                        klns_of(I.sl_const_us(h2), lnt), 256}, cty),
                 KCon{IPj6{rsok && I.meta_is_ind(mi)
                           && U32.is_lt(i2, I.meta_nf(mi))
                           && U32.is_eq(I.const_nm2(h2), tn2),
                           I.meta_ppx(mi), I.meta_pr(mi), tn2, i2, sx,
                           sargs, rs, ctx}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, cty, ri))
    case 1n+p KCon{IPj6{ok, ppx, pr, tn, idx, sx, sargs, rs, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{IPj7{r2, ok, ppx, pr, tn, idx, sargs, rs, ctx}, k}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kprojn_tin(fs, idx, tn, sx))
    case 1n+p KCon{IPj7{lsr, ok, ppx, pr, tn, idx, sargs, rs, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, pns}}, ri}:
      +l2 : U32 = lsr
      km(p, KCon{WPlE{l2, List.append(&2, U32, sargs, pns)},
                 KCon{IPj8{ok, ppx, pr, idx, rs, ctx}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, l2, ri))
    case 1n+p KCon{IPj8{ok, ppx, pr, idx, rs, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{IPj9{r2, ok, ppx, pr, idx, rs, ctx}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{IPj9{pt, ok, ppx, pr, idx, rs, ctx}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
      +nd2 : T.Ex = node
      +p2 : U32 = pt
      +fldty : U32 = I.all_dom(nd2)
      +f2 : U32 = fldty
      km(p, KCon{kslev(f2, ctx, 256),
                 KCon{IPj10{ok, U32.is_ne(p2, 4294967295),
                            I.is_all(nd2), ppx, pr, idx, rs, f2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, f2, ri))
    case 1n+p KCon{IPj10{ok, ptok, isall, ppx, pr, idx, rs, fldty}, k}
         Tuple{Tuple{fs, MLn{u}}, ri}:
      +fldprop : Bool = L.tri_is_yes(L.ln_is_zero(u))
      +i2 : U32 = idx
      +px2 : U32 = ppx
      +defprop : Bool = U32.is_ne(px2, 4294967295)
      +violates : Bool = defprop
                         && Bool.not(fldprop && U32.is_lt(i2, px2))
      +rity : U32 = S.pick(U32.is_eq(rs, 4294967294), 4294967294,
                           S.pick(violates, 4294967294, fldty))
      +ri2 : U32 = rity
      +ok2 : Bool = ptok && isall
                    && (U32.is_eq(pr, 0)
                        || (fldprop && U32.is_lt(i2, px2)))
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
    case 1n+p KCon{DIr1{t, xi, yi, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +y2 : U32 = yi
      km(p, KCon{DIr2{t, hd, y2, xi, ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kspine_tin(fs, y2, ri))
    case 1n+p KCon{DIr2{t, hx, yi, xi, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +hx2 : T.Ex = hx
      +hy2 : T.Ex = hd
      +t2 : L.Tri = t
      +kx : U32 = I.dq_head_key(hx2)
      +gate : Bool = (Bool.not(U32.is_eq(kx, 4294967295))
                      && U32.is_eq(kx, I.dq_head_key(hy2)))
                     || (L.tri_is_no(t2)
                         && (I.no_value_hd(hx2) || I.is_bvarx(hx2))
                         && (I.no_value_hd(hy2) || I.is_bvarx(hy2)))
      km(p, KCon{DIrGo{gate, t2, xi, yi, ctx}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DIrGo{False{}, t, xi, yi, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, t))
    case 1n+p KCon{DIrGo{True{}, t, xi, yi, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = xi
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DTy1{c2}, KCon{DIr4{t, yi, c2}, k}}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, x2, ri))
    case 1n+p KCon{DIr4{t, yi, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +y2 : U32 = yi
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DTy1{c2}, KCon{DIr5{t, ri, c2}, k}}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, y2, 0))
    case 1n+p KCon{DIr5{t, rx, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +rx2 : U32 = rx
      +r2 : U32 = ri
      km(p, KCon{DIr6{t, rx2, r2, ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb,
         keq_lists_tin(fs, Con{rx2, Nil{}}, Con{r2, Nil{}}, lnt))
    case 1n+p KCon{DIr6{t, rx, ry, ctx}, k} Tuple{Tuple{fs, MTri{sq}}, ri}:
      +rx2 : U32 = rx
      km(p, KCon{kslev(rx2, ctx, 256),
                 KCon{DIr7{t, Bool.not(U32.is_eq(rx2, 4294967295))
                              && Bool.not(U32.is_eq(ry, 4294967295)),
                           L.tri_is_yes(sq)}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, rx2, ri))
    case 1n+p KCon{DIr7{t, both, sameq}, k} Tuple{Tuple{fs, MLn{u}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.pick_tri(both && sameq
                              && L.tri_is_yes(L.ln_is_zero(u)),
                              L.TYes{}, t)))
    # ---- dq_type_of: the type oracle ----
    case 1n+p KCon{DTy1{ctx}, k} Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      match hd:
        case T.EConst{n, us}:
          +n2 : U32 = n
          +ti : U32 = R.get(U32, 32n, nt, n2, 4294967295)
          +t2 : U32 = ti
          km(p, KCon{DTyGo{Bool.not(U32.is_eq(t2, 4294967295)), False{},
                           t2, 0, R.get(List<&2, U32>, 32n, lp, n2, Nil{}),
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
      km(p, KCon{kev(WP{2, 0, 0, 0, ps, qs, 256}, t2),
                 KCon{DTy2{sargs}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
    case 1n+p KCon{DTyGo{False{}, True{}, ti, dlift, ps, qs, sargs}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +t2 : U32 = ti
      km(p, KCon{kev(WP{0, 0, dlift, 0, Nil{}, Nil{}, 256}, t2),
                 KCon{DTy2{sargs}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
    case 1n+p KCon{DTyGo{False{}, False{}, ti, dlift, ps, qs, sargs}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kkeep(fs, 4294967295))
    case 1n+p KCon{DTy2{sargs}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WPlE{r2, sargs}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
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
      km(p, KCon{DWhd{t2}, KCon{CkT3{isthm, ti1, vi, t2, ok}, k}}, lnt,
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
                            R.get(L.LN, 32n, lnt, I.sort_lvl_of(kx),
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
         kfetch(fs, R.get(U32, 32n, nt, I.const_nm2(tx), 4294967295),
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
      km(p, KCon{DWhd{t2}, KCon{CkV2{vi, 8192}, k}}, lnt, nlx, mt, lp, vt,
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
      +b22 : U32 = b2
      km(p, KCon{DWhd{b22},
                 KCon{CkE2{a1, b1, a2, xi, tye, ctx, fu}, k}},
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
      +a12 : U32 = a1
      km(p, KCon{DWhd{a12},
                 KCon{CkE4{t, a12, a2, xi, tye, ctx, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{CkE4{sub, a1, a2, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +a22 : U32 = a2
      km(p, KCon{DWhd{a22},
                 KCon{CkE5{sub, ri, a1, a22, xi, tye, ctx, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{CkE5{sub, wd1, a1, a2, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +w2 : U32 = wd1
      +r2 : U32 = ri
      +a12 : U32 = a1
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DSub{False{}, U32.is_eq(a12, a2), w2, r2,
                      Con{a12, c2}, 64},
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
      +x2 : U32 = xi
      +f2 : U32 = fu
      km(p, KCon{ISub{x2, ctx, f2}, KCon{CkI2{tye, ctx}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{CkEy{T.ELet{ln1, lt1, lv1, lb1}, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +b2 : U32 = lb1
      km(p, KCon{kev(WP{1, 0, 0, lv1, Nil{}, Nil{}, 256}, b2),
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
         kfetch(fs, R.get(U32, 32n, nt, I.const_nm2(xn2), 4294967295),
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
                                 L.ln_cmp(R.get(L.LN, 32n, lnt, lt,
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
      +x2 : U32 = xi
      +f2 : U32 = fu
      km(p, KCon{ISub{x2, ctx, f2}, KCon{CkI2{tye, ctx}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{CkEy{xn, xi, tye, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = xi
      +f2 : U32 = fu
      km(p, KCon{ISub{x2, ctx, f2}, KCon{CkI2{tye, ctx}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ck_infer: infer, reduce both, compare
    case 1n+p KCon{CkI2{tye, ctx}, k} Tuple{Tuple{fs, MIR{t, ok}}, ri}:
      +t2 : U32 = t
      km(p, KCon{DWhd{t2}, KCon{CkI3{tye, t2, ok, ctx}, k}}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{CkI3{tye, rty, riok, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +t2 : U32 = tye
      +rt2 : U32 = rty
      km(p, KCon{DWhd{t2},
                 KCon{CkI4{ri, U32.is_eq(rt2, t2), rt2, riok, ctx}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{CkI4{w1, samef, rty, riok, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +w2 : U32 = w1
      +r2 : U32 = ri
      km(p, KCon{DSub{False{}, samef, w2, r2, ctx, 64},
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
    # ---- the universe oracle ----    # ---- type inference ----
    case 1n+p KCon{ISub{xi, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +f2 : U32 = fu
      +x2 : U32 = xi
      km(p, KCon{IEvGo{U32.is_eq(f2, 0), x2, ctx, f2}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IEvGo{True{}, xi, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, 4294967295, False{}))
    case 1n+p KCon{IEvGo{False{}, xi, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = xi
      km(p, KCon{IEv{x2, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, kfetch(fs, x2, ri))
    # -- Sort --
    case 1n+p KCon{IEv{xi, ctx, fu}, k} Tuple{Tuple{fs, MX{T.ESort{l}}}, ri}:
      +u : L.LN = L.ln_succ(R.get(L.LN, 32n, lnt, l, L.LNun{}))
      +u2 : L.LN = u
      km(p, KCon{ISrtGo{L.is_un(u2), u2}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{ISrtGo{True{}, u}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, 4294967295, False{}))
    case 1n+p KCon{ISrtGo{False{}, u}, k} Tuple{Tuple{fs, msg}, ri}:
      +nl : U32 = nlx
      km(p, KCon{IWrap{True{}}, k},
         R.set(L.LN, 32n, lnt, nl, u, L.LNun{}), (nl + 1 : U32), mt, lp,
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
      +t2 : U32 = t
      km(p, KCon{DWhd{t2}, KCon{IAl3{ty, b, t2, ok, ctx, fu}, k}}, lnt,
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
      +t2 : U32 = t
      km(p, KCon{DWhd{t2}, KCon{IAl5{ka, ra, raok, t2, ok, ctx, fu}, k}},
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
      +u : L.LN = L.ln_imax(R.get(L.LN, 32n, lnt, I.sort_lvl_of(ka),
                                  L.LNun{}),
                            R.get(L.LN, 32n, lnt, I.sort_lvl_of(kb),
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
      km(p, KCon{kev(WP{0, 0, (i2 + 1 : U32), 0, Nil{}, Nil{}, 256}, t2),
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
    case 1n+p KCon{IEv{xi, ctx, fu}, k} Tuple{Tuple{fs, MX{T.EStr{d}}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, 4294967295, False{}))
    # -- Const --
    case 1n+p KCon{IEv{xi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EConst{n, us}}}, ri}:
      +n2 : U32 = n
      +ti : U32 = R.get(U32, 32n, nt, n2, 4294967295)
      +t2 : U32 = ti
      km(p, KCon{ICnGo{U32.is_eq(t2, 4294967295), t2,
                       R.get(List<&2, U32>, 32n, lp, n2, Nil{}),
                       klns_of(us, lnt)}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{ICnGo{True{}, ti, ps, qs}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmir(fs, 4294967295, False{}))
    case 1n+p KCon{ICnGo{False{}, ti, ps, qs}, k} Tuple{Tuple{fs, msg}, ri}:
      +t2 : U32 = ti
      km(p, KCon{kev(WP{2, 0, 0, 0, ps, qs, 256}, t2),
                 KCon{IWrap{True{}}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
    # -- Let --
    case 1n+p KCon{IEv{xi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.ELet{n, ty, v, b}}}, ri}:
      +b2 : U32 = b
      +f2 : U32 = fu
      km(p, KCon{kev(WP{1, 0, 0, v, Nil{}, Nil{}, 256}, b2),
                 KCon{ILt2{ctx, (f2 - 1 : U32)}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, b2, ri))
    case 1n+p KCon{ILt2{ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{ISub{r2, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, knoop(fs, 0))
    # -- App --
    case 1n+p KCon{IEv{xi, ctx, fu}, k}
         Tuple{Tuple{fs, MX{T.EApp{f, a}}}, ri}:
      +f3 : U32 = f
      +fu2 : U32 = fu
      km(p, KCon{ISub{f3, ctx, (fu2 - 1 : U32)},
                 KCon{IAp2{a, ctx, fu2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IAp2{a, ctx, fu}, k} Tuple{Tuple{fs, MIR{t, ok}}, ri}:
      +t2 : U32 = t
      km(p, KCon{kwev(True{}, t2, Nil{}, 256),
                 KCon{IAp3{a, t2, ok, ctx, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
    case 1n+p KCon{IAp3{a, rf, rfok, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{IAp3b{a, rf, rfok, ctx, fu}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{IAp3b{a, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
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
      km(p, KCon{IAp5{a, nd2, t2, ok, rf, rfok, ctx, fu}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb,
         keq_lists_tin(fs, Con{t2, Nil{}},
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
      +r2 : U32 = ra
      km(p, KCon{DWhd{r2}, KCon{IAp5c{a, node, r2, raok, rf, rfok, ctx,
                                      fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IAp5c{a, node, ra, raok, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +nd2 : T.Ex = node
      km(p, KCon{DWhd{I.all_dom(nd2)},
                 KCon{IAp5d{ri, a, nd2, ra, raok, rf, rfok, ctx, fu}, k}},
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
    case 1n+p KCon{IAp6Go{False{}, w1, w2, a, node, ra, raok, rf, rfok,
                          ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +w12 : U32 = w1
      +w22 : U32 = w2
      km(p, KCon{DSub{False{}, U32.is_eq(w12, w22), w12, w22, ctx, 24},
                 KCon{IAp7{a, node, ra, raok, rf, rfok, ctx, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
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
      km(p, KCon{kev(WP{1, 0, 0, a2, Nil{}, Nil{}, 256},
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
      +s2 : U32 = sx
      +fu2 : U32 = fu
      km(p, KCon{ISub{s2, ctx, (fu2 - 1 : U32)},
                 KCon{IPj2{tn, idx, s2, ctx, fu2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{IPj2{tn, idx, sx, ctx, fu}, k}
         Tuple{Tuple{fs, MIR{t, ok}}, ri}:
      +t2 : U32 = t
      km(p, KCon{DWhd{t2}, KCon{IPj3{tn, idx, sx, t2, ok, ctx, fu}, k}},
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
    case 1n+p KCon{IPj5{tn, idx, sx, sty, rs, rsok, ctx, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +tn2 : U32 = tn
      +i2 : U32 = idx
      +h2 : T.Ex = hd
      +mi : I.Meta = R.get(I.Meta, 32n, mt, tn2, I.MNone{})
      +cty : U32 = I.meta_cty(mi)
      km(p, KCon{kev(WP{2, 0, 0, 0,
                        R.get(List<&2, U32>, 32n, lp, tn2, Nil{}),
                        klns_of(I.sl_const_us(h2), lnt), 256}, cty),
                 KCon{IPj6{rsok && I.meta_is_ind(mi)
                           && U32.is_lt(i2, I.meta_nf(mi))
                           && U32.is_eq(I.const_nm2(h2), tn2),
                           I.meta_ppx(mi), I.meta_pr(mi), tn2, i2, sx,
                           sargs, rs, ctx}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, cty, ri))
    case 1n+p KCon{IPj6{ok, ppx, pr, tn, idx, sx, sargs, rs, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{IPj7{r2, ok, ppx, pr, tn, idx, sargs, rs, ctx}, k}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kprojn_tin(fs, idx, tn, sx))
    case 1n+p KCon{IPj7{lsr, ok, ppx, pr, tn, idx, sargs, rs, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, pns}}, ri}:
      +l2 : U32 = lsr
      km(p, KCon{WPlE{l2, List.append(&2, U32, sargs, pns)},
                 KCon{IPj8{ok, ppx, pr, idx, rs, ctx}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, l2, ri))
    case 1n+p KCon{IPj8{ok, ppx, pr, idx, rs, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{IPj9{r2, ok, ppx, pr, idx, rs, ctx}, k}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
    case 1n+p KCon{IPj9{pt, ok, ppx, pr, idx, rs, ctx}, k}
         Tuple{Tuple{fs, MX{node}}, ri}:
      +nd2 : T.Ex = node
      +p2 : U32 = pt
      +fldty : U32 = I.all_dom(nd2)
      +f2 : U32 = fldty
      km(p, KCon{kslev(f2, ctx, 256),
                 KCon{IPj10{ok, U32.is_ne(p2, 4294967295),
                            I.is_all(nd2), ppx, pr, idx, rs, f2}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, f2, ri))
    case 1n+p KCon{IPj10{ok, ptok, isall, ppx, pr, idx, rs, fldty}, k}
         Tuple{Tuple{fs, MLn{u}}, ri}:
      +fldprop : Bool = L.tri_is_yes(L.ln_is_zero(u))
      +i2 : U32 = idx
      +px2 : U32 = ppx
      +defprop : Bool = U32.is_ne(px2, 4294967295)
      +violates : Bool = defprop
                         && Bool.not(fldprop && U32.is_lt(i2, px2))
      +rity : U32 = S.pick(U32.is_eq(rs, 4294967294), 4294967294,
                           S.pick(violates, 4294967294, fldty))
      +ri2 : U32 = rity
      +ok2 : Bool = ptok && isall
                    && (U32.is_eq(pr, 0)
                        || (fldprop && U32.is_lt(i2, px2)))
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
    case 1n+p KCon{DIr1{t, xi, yi, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +y2 : U32 = yi
      km(p, KCon{DIr2{t, hd, y2, xi, ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, kspine_tin(fs, y2, ri))
    case 1n+p KCon{DIr2{t, hx, yi, xi, ctx}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +hx2 : T.Ex = hx
      +hy2 : T.Ex = hd
      +t2 : L.Tri = t
      +kx : U32 = I.dq_head_key(hx2)
      +gate : Bool = (Bool.not(U32.is_eq(kx, 4294967295))
                      && U32.is_eq(kx, I.dq_head_key(hy2)))
                     || (L.tri_is_no(t2)
                         && (I.no_value_hd(hx2) || I.is_bvarx(hx2))
                         && (I.no_value_hd(hy2) || I.is_bvarx(hy2)))
      km(p, KCon{DIrGo{gate, t2, xi, yi, ctx}, k}, lnt, nlx, mt, lp, vt,
         qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DIrGo{False{}, t, xi, yi, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri(fs, t))
    case 1n+p KCon{DIrGo{True{}, t, xi, yi, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = xi
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DTy1{c2}, KCon{DIr4{t, yi, c2}, k}}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, x2, ri))
    case 1n+p KCon{DIr4{t, yi, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +y2 : U32 = yi
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DTy1{c2}, KCon{DIr5{t, ri, c2}, k}}, lnt, nlx, mt, lp,
         vt, qtt, natn, wm, nt, hcb, kspine_tin(fs, y2, 0))
    case 1n+p KCon{DIr5{t, rx, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +rx2 : U32 = rx
      +r2 : U32 = ri
      km(p, KCon{DIr6{t, rx2, r2, ctx}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb,
         keq_lists_tin(fs, Con{rx2, Nil{}}, Con{r2, Nil{}}, lnt))
    case 1n+p KCon{DIr6{t, rx, ry, ctx}, k} Tuple{Tuple{fs, MTri{sq}}, ri}:
      +rx2 : U32 = rx
      km(p, KCon{kslev(rx2, ctx, 256),
                 KCon{DIr7{t, Bool.not(U32.is_eq(rx2, 4294967295))
                              && Bool.not(U32.is_eq(ry, 4294967295)),
                           L.tri_is_yes(sq)}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, rx2, ri))
    case 1n+p KCon{DIr7{t, both, sameq}, k} Tuple{Tuple{fs, MLn{u}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmtri(fs, L.pick_tri(both && sameq
                              && L.tri_is_yes(L.ln_is_zero(u)),
                              L.TYes{}, t)))
    # ---- dq_type_of: the type oracle ----
    case 1n+p KCon{DTy1{ctx}, k} Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      match hd:
        case T.EConst{n, us}:
          +n2 : U32 = n
          +ti : U32 = R.get(U32, 32n, nt, n2, 4294967295)
          +t2 : U32 = ti
          km(p, KCon{DTyGo{Bool.not(U32.is_eq(t2, 4294967295)), False{},
                           t2, 0, R.get(List<&2, U32>, 32n, lp, n2, Nil{}),
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
      km(p, KCon{kev(WP{2, 0, 0, 0, ps, qs, 256}, t2),
                 KCon{DTy2{sargs}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
    case 1n+p KCon{DTyGo{False{}, True{}, ti, dlift, ps, qs, sargs}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +t2 : U32 = ti
      km(p, KCon{kev(WP{0, 0, dlift, 0, Nil{}, Nil{}, 256}, t2),
                 KCon{DTy2{sargs}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, t2, ri))
    case 1n+p KCon{DTyGo{False{}, False{}, ti, dlift, ps, qs, sargs}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kkeep(fs, 4294967295))
    case 1n+p KCon{DTy2{sargs}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WPlE{r2, sargs}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, r2, 0))
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
      km(p, KCon{DWhd{t2}, KCon{CkT3{isthm, ti1, vi, t2, ok}, k}}, lnt,
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
                            R.get(L.LN, 32n, lnt, I.sort_lvl_of(kx),
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
         kfetch(fs, R.get(U32, 32n, nt, I.const_nm2(tx), 4294967295),
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
      km(p, KCon{DWhd{t2}, KCon{CkV2{vi, 8192}, k}}, lnt, nlx, mt, lp, vt,
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
      +b22 : U32 = b2
      km(p, KCon{DWhd{b22},
                 KCon{CkE2{a1, b1, a2, xi, tye, ctx, fu}, k}},
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
      +a12 : U32 = a1
      km(p, KCon{DWhd{a12},
                 KCon{CkE4{t, a12, a2, xi, tye, ctx, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{CkE4{sub, a1, a2, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +a22 : U32 = a2
      km(p, KCon{DWhd{a22},
                 KCon{CkE5{sub, ri, a1, a22, xi, tye, ctx, fu}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{CkE5{sub, wd1, a1, a2, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +w2 : U32 = wd1
      +r2 : U32 = ri
      +a12 : U32 = a1
      +c2 : List<&2, U32> = ctx
      km(p, KCon{DSub{False{}, U32.is_eq(a12, a2), w2, r2,
                      Con{a12, c2}, 64},
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
      +x2 : U32 = xi
      +f2 : U32 = fu
      km(p, KCon{ISub{x2, ctx, f2}, KCon{CkI2{tye, ctx}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{CkEy{T.ELet{ln1, lt1, lv1, lb1}, xi, tye, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +b2 : U32 = lb1
      km(p, KCon{kev(WP{1, 0, 0, lv1, Nil{}, Nil{}, 256}, b2),
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
         kfetch(fs, R.get(U32, 32n, nt, I.const_nm2(xn2), 4294967295),
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
                                 L.ln_cmp(R.get(L.LN, 32n, lnt, lt,
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
      +x2 : U32 = xi
      +f2 : U32 = fu
      km(p, KCon{ISub{x2, ctx, f2}, KCon{CkI2{tye, ctx}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{CkEy{xn, xi, tye, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = xi
      +f2 : U32 = fu
      km(p, KCon{ISub{x2, ctx, f2}, KCon{CkI2{tye, ctx}, k}}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    # ck_infer: infer, reduce both, compare
    case 1n+p KCon{CkI2{tye, ctx}, k} Tuple{Tuple{fs, MIR{t, ok}}, ri}:
      +t2 : U32 = t
      km(p, KCon{DWhd{t2}, KCon{CkI3{tye, t2, ok, ctx}, k}}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{CkI3{tye, rty, riok, ctx}, k} Tuple{Tuple{fs, msg}, ri}:
      +t2 : U32 = tye
      +rt2 : U32 = rty
      km(p, KCon{DWhd{t2},
                 KCon{CkI4{ri, U32.is_eq(rt2, t2), rt2, riok, ctx}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))
    case 1n+p KCon{CkI4{w1, samef, rty, riok, ctx}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +w2 : U32 = w1
      +r2 : U32 = ri
      km(p, KCon{DSub{False{}, samef, w2, r2, ctx, 64},
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
             kmln(fs, L.ln_succ(R.get(L.LN, 32n, lnt, l, L.LNun{}))))
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
             kfetch(fs, R.get(U32, 32n, nt, n2, 4294967295), ri))
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
                            R.get(L.LN, 32n, lnt, I.sort_lvl_of(nd),
                                  L.LNun{}),
                            L.LNun{})))
    case 1n+p KCon{SLCst{n, us}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      +nd : T.Ex = node
      +n2 : U32 = n
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kmln(fs, L.pick_ln(I.is_sortx(nd),
                            L.ln_subst(R.get(L.LN, 32n, lnt,
                                             I.sort_lvl_of(nd), L.LNun{}),
                                       R.get(List<&2, U32>, 32n, lp, n2,
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
                            L.ln_subst(R.get(L.LN, 32n, lnt,
                                             I.sort_lvl_of(nd), L.LNun{}),
                                       R.get(List<&2, U32>, 32n, lp, nm,
                                             Nil{}),
                                       klns_of(us, lnt)),
                            L.LNun{})))
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
    case 1n+p KCon{DWhd{i}, k} Tuple{Tuple{fs, msg}, ri}:
      +i2 : U32 = i
      +h : U32 = R.get(U32, 64n, wm, i2, 4294967295)
      +h2 : U32 = h
      km(p, KCon{DWhdGo{U32.is_ne(h2, 4294967295), h2, i2}, k}, lnt, nlx,
         mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, ri))
    case 1n+p KCon{DWhdGo{True{}, h, i}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kkeep(fs, h))
    case 1n+p KCon{DWhdGo{False{}, h, i}, k} Tuple{Tuple{fs, msg}, ri}:
      +i2 : U32 = i
      km(p, KCon{kwev(True{}, i2, Nil{}, 256), KCon{DWhdSt{i2}, k}}, lnt,
         nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, i2, 0))
    case 1n+p KCon{DWhdSt{i}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn,
         R.set(U32, 64n, wm, i, r2, 4294967295), nt, hcb, kkeep(fs, r2))
    # ---- the IH builder loop ----
    case 1n+p KCon{WIhNext{IC{Nil{}, cn, us, pre, fields, ccty, pp, ni,
                              acc, ci, need, can, delta, vi, ps, qs, e,
                              args, fu}}, k} Tuple{Tuple{fs, msg}, ri}:
      +a2 : List<&2, U32> = args
      +p2 : U32 = pp
      km(p, KCon{WCont{delta, I.skip_u(a2, (need + 1 : U32)),
                       (fu - 1 : U32)}, k},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
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
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, cc2, ri))
    case 1n+p KCon{WIhPe{h, ic}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WIhFty{h, ic}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kfetch(fs, r2, 0))
    case 1n+p KCon{WIhFty{h, ic}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      km(p, KCon{WIhScanned{h, ic}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
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
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, first, ri))
    case 1n+p KCon{WIhL{Nil{}, amt, lacc, ebni, doms, ic}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +ic2 : IC = ic
      km(p, KCon{WIhB{ic2}, k}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kih_build(fs, krev(Con{ri, lacc}, Nil{}), ebni, doms, amt,
                   ic_cn(ic2), ic_us(ic2)))
    case 1n+p KCon{WIhL{Con{x, t}, amt, lacc, ebni, doms, ic}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = x
      +a2 : U32 = amt
      km(p, KCon{kev(WP{0, 0, a2, 0, Nil{}, Nil{}, 256}, x2),
                 KCon{WIhL{t, a2, Con{ri, lacc}, ebni, doms, ic}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, x2, 0))
    case 1n+p KCon{WIhB{ic}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, KCon{WIhNext{ic_push(ic, ri)}, k}, lnt, nlx, mt, lp, vt, qtt,
         natn, wm, nt, hcb, knoop(fs, 0))
    # ---- resume frames for the walks ----
    case 1n+p KCon{KBvI{iseq, isgt, i, e}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kbv_fin(iseq, isgt, fs, ri, i, e, hcb))
    case 1n+p KCon{KAp2{wp, e, f0, a0}, k} Tuple{Tuple{fs, msg}, ri}:
      +w : WP = wp
      +a2 : U32 = a0
      km(p, KCon{kev(w, a2), KCon{KAp3{e, f0, a2, ri}, k}}, lnt, nlx, mt,
         lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, a2, 0))
    case 1n+p KCon{KAp3{e, f0, a0, r1}, k} Tuple{Tuple{fs, msg}, ri}:
      +r1b : U32 = r1
      +rib : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kalloc_if(Bool.not(U32.is_eq(r1b, f0) && U32.is_eq(rib, a0)),
                   fs, T.EApp{r1b, rib}, e, hcb))
    case 1n+p KCon{KLm2{wp, e, n, t0, b0, bi}, k} Tuple{Tuple{fs, msg}, ri}:
      +b2 : U32 = b0
      km(p, KCon{kev(wp_bump(wp), b2), KCon{KLm3{e, n, t0, b2, bi, ri}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, b2, 0))
    case 1n+p KCon{KLm3{e, n, t0, b0, bi, r1}, k} Tuple{Tuple{fs, msg}, ri}:
      +r1b : U32 = r1
      +rib : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
         kalloc_if(Bool.not(U32.is_eq(r1b, t0) && U32.is_eq(rib, b0)),
                   fs, T.ELam{n, r1b, rib, bi}, e, hcb))
    case 1n+p KCon{KAl2{wp, e, n, t0, b0, bi}, k} Tuple{Tuple{fs, msg}, ri}:
      +b2 : U32 = b0
      km(p, KCon{kev(wp_bump(wp), b2), KCon{KAl3{e, n, t0, b2, bi, ri}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, b2, 0))
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
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, v02, 0))
    case 1n+p KCon{KLt3{wp, e, n, t0, v0, b0, r1}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +b2 : U32 = b0
      km(p, KCon{kev(wp_bump(wp), b2),
                 KCon{KLt4{e, n, t0, v0, b2, r1, ri}, k}},
         lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kfetch(fs, b2, 0))
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
  km(fuel, KCon{SLEv{e2, ctx, 256}, KCon{SLChk{want}, KNil{}}}, lnt, nlx,
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
  km(fuel, KCon{DWhd{t2}, KCon{CkT1{isthm, vi, 8192}, KNil{}}}, lnt, nlx,
     mt, lp, vt, qtt, natn, wm, nt, hcb, knoop(fs, 0))

def kwhd(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>, +nlx: U32,
         +mt: R.Tr<I.Meta>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
         +qtt: R.Tr<U32>, +natn: U32, +wm: R.Tr<U32>, +nt: R.Tr<U32>,
         +i: U32, +hcb: U32)
    -> ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>):
  km(fuel, KCon{DWhd{i}, KNil{}}, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb,
     knoop(fs, 0))

def kwhnf(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>, +nlx: U32,
          +mt: R.Tr<I.Meta>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
          +qtt: R.Tr<U32>, +natn: U32, +wm: R.Tr<U32>, +nt: R.Tr<U32>,
          +e: U32, +delta: Bool, +fu: U32, +hcb: U32)
    -> ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>):
  +e2 : U32 = e
  km(fuel, KCon{kwev(delta, e2, Nil{}, fu), KNil{}}, lnt, nlx, mt, lp, vt,
     qtt, natn, wm, nt, hcb, kfetch(fs, e2, 0))
