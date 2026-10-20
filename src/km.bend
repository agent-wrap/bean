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
       tin: ((Array<T.Ex> & U32) & MG) & U32)
    -> ((Array<T.Ex> & U32) & U32) & (R.Tr<L.LN> & U32):
  match fuel stk tin:
    case 0n _ Tuple{Tuple{fs, msg}, ri}:
      ((fs, 4294967295), (lnt, nlx))
    case 1n+p KNil{} Tuple{Tuple{fs, msg}, ri}:
      ((fs, ri), (lnt, nlx))
    case 1n+p KCon{KKp{e}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, kkeep(fs, e))
    # ---- eval: lift ----
    case 1n+p KCon{KEvL{c, d, e, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      match node:
        case T.EBVar{i}:
          km(p, k, lnt, nlx, mt, lp, vt, kbv_lift(fs, i, e, c, d))
        case T.EApp{f, a}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +f2 : U32 = f
          km(p, KCon{kev(w, f2), KCon{KAp2{w, e, f2, a}, k}}, lnt, nlx, mt,
             lp, vt, kfetch(fs, f2, ri))
        case T.ELam{n, t, b, bi}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLm2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, kfetch(fs, t2, ri))
        case T.EAll{n, t, b, bi}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KAl2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, kfetch(fs, t2, ri))
        case T.ELet{n, t, v, b}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLt2{w, e, n, t2, v, b}, k}}, lnt,
             nlx, mt, lp, vt, kfetch(fs, t2, ri))
        case T.EProj{tn, i, s}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +s2 : U32 = s
          km(p, KCon{kev(w, s2), KCon{KPj2{e, tn, i, s2}, k}}, lnt, nlx, mt,
             lp, vt, kfetch(fs, s2, ri))
        case _:
          km(p, k, lnt, nlx, mt, lp, vt, kkeep(fs, e))
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
             lnt, nlx, mt, lp, vt, kfetch(fs, tgt, ri))
        case T.EApp{f, a}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +f2 : U32 = f
          km(p, KCon{kev(w, f2), KCon{KAp2{w, e, f2, a}, k}}, lnt, nlx, mt,
             lp, vt, kfetch(fs, f2, ri))
        case T.ELam{n, t, b, bi}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLm2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, kfetch(fs, t2, ri))
        case T.EAll{n, t, b, bi}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KAl2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, kfetch(fs, t2, ri))
        case T.ELet{n, t, vv, b}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLt2{w, e, n, t2, vv, b}, k}}, lnt,
             nlx, mt, lp, vt, kfetch(fs, t2, ri))
        case T.EProj{tn, i, s}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +s2 : U32 = s
          km(p, KCon{kev(w, s2), KCon{KPj2{e, tn, i, s2}, k}}, lnt, nlx, mt,
             lp, vt, kfetch(fs, s2, ri))
        case _:
          km(p, k, lnt, nlx, mt, lp, vt, kkeep(fs, e))
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
             S.pick(same, nl, (nl + 1 : U32)), mt, lp, vt,
             ksort3(same, fs, nl, e))
        case T.EConst{n, us}:
          +r : LVS = klsub_lvls(us, lnt, nlx, ps, qs)
          km(p, k, lvs_t(r), lvs_nx(r), mt, lp, vt,
             ksconst(fs, n, lvs_xs(r)))
        case T.EApp{f, a}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +f2 : U32 = f
          km(p, KCon{kev(w, f2), KCon{KAp2{w, e, f2, a}, k}}, lnt, nlx, mt,
             lp, vt, kfetch(fs, f2, ri))
        case T.ELam{n, t, b, bi}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLm2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, kfetch(fs, t2, ri))
        case T.EAll{n, t, b, bi}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KAl2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, mt, lp, vt, kfetch(fs, t2, ri))
        case T.ELet{n, t, v, b}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLt2{w, e, n, t2, v, b}, k}}, lnt,
             nlx, mt, lp, vt, kfetch(fs, t2, ri))
        case T.EProj{tn, i, s}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +s2 : U32 = s
          km(p, KCon{kev(w, s2), KCon{KPj2{e, tn, i, s2}, k}}, lnt, nlx, mt,
             lp, vt, kfetch(fs, s2, ri))
        case _:
          km(p, k, lnt, nlx, mt, lp, vt, kkeep(fs, e))
    # ---- whnf: rebuild on exhausted fuel ----
    case 1n+p KCon{WRb{e, args}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, krebuild(args, fs, e))
    # ---- whnf: eval (entry-level node dispatch; first match wins) ----
    case 1n+p KCon{WEv{delta, e, args, fu}, k}
         Tuple{Tuple{fs, MX{T.EApp{f, a}}}, ri}:
      +f2 : U32 = f
      km(p, KCon{kwev(delta, f2, Con{a, args}, (fu - 1 : U32)), k}, lnt,
         nlx, mt, lp, vt, kfetch(fs, f2, ri))
    case 1n+p KCon{WEv{delta, e, Con{a, rest}, fu}, k}
         Tuple{Tuple{fs, MX{T.ELam{n, t, b, bi}}}, ri}:
      +b2 : U32 = b
      km(p, KCon{kev(WP{1, 0, 0, a, Nil{}, Nil{}, 256}, b2),
                 KCon{WCont{delta, rest, (fu - 1 : U32)}, k}},
         lnt, nlx, mt, lp, vt, kfetch(fs, b2, ri))
    case 1n+p KCon{WEv{delta, e, args, fu}, k}
         Tuple{Tuple{fs, MX{T.ELet{n, t, v, b}}}, ri}:
      +b2 : U32 = b
      km(p, KCon{kev(WP{1, 0, 0, v, Nil{}, Nil{}, 256}, b2),
                 KCon{WCont{delta, args, (fu - 1 : U32)}, k}},
         lnt, nlx, mt, lp, vt, kfetch(fs, b2, ri))
    case 1n+p KCon{WEv{delta, e, args, fu}, k}
         Tuple{Tuple{fs, MX{T.EConst{n, us}}}, ri}:
      +n2 : U32 = n
      +vi : U32 = R.get(U32, 32n, vt, n2, 4294967295)
      +d2 : Bool = delta
      +can : Bool = Bool.and(d2, U32.is_ne(vi, 4294967295))
      km(p, KCon{WDelGo{can, d2, vi,
                        R.get(List<&2, U32>, 32n, lp, n2, Nil{}),
                        klns_of(us, lnt), e, args, fu}, k},
         lnt, nlx, mt, lp, vt, knoop(fs, ri))
    case 1n+p KCon{WEv{delta, e, args, fu}, k}
         Tuple{Tuple{fs, MX{T.EProj{tn, idx, sx}}}, ri}:
      +s2 : U32 = sx
      +f2 : U32 = (fu - 1 : U32)
      km(p, KCon{kwev(delta, s2, Nil{}, f2),
                 KCon{WPrj{delta, e, tn, idx, args, f2}, k}},
         lnt, nlx, mt, lp, vt, kfetch(fs, s2, ri))
    case 1n+p KCon{WEv{delta, e, args, fu}, k} Tuple{Tuple{fs, MX{node}}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, krebuild(args, fs, e))
    # ---- whnf: continue on a substitution result ----
    case 1n+p KCon{WCont{delta, args, fu}, k} Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{kwev(delta, r2, args, fu), k}, lnt, nlx, mt, lp, vt,
         kfetch(fs, r2, 0))
    # ---- whnf: delta branch ----
    case 1n+p KCon{WDelGo{True{}, delta, vi, ps, qs, e, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +v2 : U32 = vi
      km(p, KCon{kev(WP{2, 0, 0, 0, ps, qs, 256}, v2),
                 KCon{WCont{delta, args, (fu - 1 : U32)}, k}},
         lnt, nlx, mt, lp, vt, kfetch(fs, v2, ri))
    case 1n+p KCon{WDelGo{False{}, delta, vi, ps, qs, e, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, krebuild(args, fs, e))
    # ---- whnf: projection, struct reduced -> collect its spine ----
    case 1n+p KCon{WPrj{delta, e, tn, idx, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r2 : U32 = ri
      km(p, KCon{WPrjS{delta, e, tn, idx, args, fu}, k}, lnt, nlx, mt, lp,
         vt, kspine_tin(fs, r2, r2))
    # ---- whnf: projection, spine collected -> constructor? ----
    case 1n+p KCon{WPrjS{delta, e, tn, idx, args, fu}, k}
         Tuple{Tuple{fs, MSP{hd, sargs}}, ri}:
      +cmi : I.Meta = R.get(I.Meta, 32n, mt, I.const_nm2(hd), I.MNone{})
      km(p, KCon{WPrjGo{I.meta_is_ctor(cmi), delta, e,
                        I.nth_u(sargs, (I.meta_p(cmi) + idx : U32),
                                4294967295),
                        args, fu}, k},
         lnt, nlx, mt, lp, vt, knoop(fs, ri))
    # ---- whnf: projection branch ----
    case 1n+p KCon{WPrjGo{True{}, delta, e, fld, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +f2 : U32 = fld
      km(p, KCon{kwev(delta, f2, args, fu), k}, lnt, nlx, mt, lp, vt,
         kfetch(fs, f2, ri))
    case 1n+p KCon{WPrjGo{False{}, delta, e, fld, args, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, krebuild(args, fs, e))
    # ---- resume frames for the walks ----
    case 1n+p KCon{KBvI{iseq, isgt, i, e}, k} Tuple{Tuple{fs, msg}, ri}:
      km(p, k, lnt, nlx, mt, lp, vt, kbv_fin(iseq, isgt, fs, ri, i, e))
    case 1n+p KCon{KAp2{wp, e, f0, a0}, k} Tuple{Tuple{fs, msg}, ri}:
      +w : WP = wp
      +a2 : U32 = a0
      km(p, KCon{kev(w, a2), KCon{KAp3{e, f0, a2, ri}, k}}, lnt, nlx, mt,
         lp, vt, kfetch(fs, a2, 0))
    case 1n+p KCon{KAp3{e, f0, a0, r1}, k} Tuple{Tuple{fs, msg}, ri}:
      +r1b : U32 = r1
      +rib : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt,
         kalloc_if(Bool.not(U32.is_eq(r1b, f0) && U32.is_eq(rib, a0)),
                   fs, T.EApp{r1b, rib}, e))
    case 1n+p KCon{KLm2{wp, e, n, t0, b0, bi}, k} Tuple{Tuple{fs, msg}, ri}:
      +b2 : U32 = b0
      km(p, KCon{kev(wp_bump(wp), b2), KCon{KLm3{e, n, t0, b2, bi, ri}, k}},
         lnt, nlx, mt, lp, vt, kfetch(fs, b2, 0))
    case 1n+p KCon{KLm3{e, n, t0, b0, bi, r1}, k} Tuple{Tuple{fs, msg}, ri}:
      +r1b : U32 = r1
      +rib : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt,
         kalloc_if(Bool.not(U32.is_eq(r1b, t0) && U32.is_eq(rib, b0)),
                   fs, T.ELam{n, r1b, rib, bi}, e))
    case 1n+p KCon{KAl2{wp, e, n, t0, b0, bi}, k} Tuple{Tuple{fs, msg}, ri}:
      +b2 : U32 = b0
      km(p, KCon{kev(wp_bump(wp), b2), KCon{KAl3{e, n, t0, b2, bi, ri}, k}},
         lnt, nlx, mt, lp, vt, kfetch(fs, b2, 0))
    case 1n+p KCon{KAl3{e, n, t0, b0, bi, r1}, k} Tuple{Tuple{fs, msg}, ri}:
      +r1b : U32 = r1
      +rib : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt,
         kalloc_if(Bool.not(U32.is_eq(r1b, t0) && U32.is_eq(rib, b0)),
                   fs, T.EAll{n, r1b, rib, bi}, e))
    case 1n+p KCon{KLt2{wp, e, n, t0, v0, b0}, k} Tuple{Tuple{fs, msg}, ri}:
      +w : WP = wp
      +v02 : U32 = v0
      km(p, KCon{kev(w, v02), KCon{KLt3{w, e, n, t0, v02, b0, ri}, k}},
         lnt, nlx, mt, lp, vt, kfetch(fs, v02, 0))
    case 1n+p KCon{KLt3{wp, e, n, t0, v0, b0, r1}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +b2 : U32 = b0
      km(p, KCon{kev(wp_bump(wp), b2),
                 KCon{KLt4{e, n, t0, v0, b2, r1, ri}, k}},
         lnt, nlx, mt, lp, vt, kfetch(fs, b2, 0))
    case 1n+p KCon{KLt4{e, n, t0, v0, b0, r1, r2}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +r1b : U32 = r1
      +r2b : U32 = r2
      +rib : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt,
         kalloc_if(Bool.not(U32.is_eq(r1b, t0) && U32.is_eq(r2b, v0)
                            && U32.is_eq(rib, b0)),
                   fs, T.ELet{n, r1b, r2b, rib}, e))
    case 1n+p KCon{KPj2{e, tn, ix, s0}, k} Tuple{Tuple{fs, msg}, ri}:
      +rib : U32 = ri
      km(p, k, lnt, nlx, mt, lp, vt,
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
     nlx, R.TNil{}, R.TNil{}, R.TNil{}, kfetch(fs, e2, 0))

def kinst(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>, +nlx: U32,
          +e: U32, +j: U32, +v: U32, +fu: U32)
    -> ((Array<T.Ex> & U32) & U32) & (R.Tr<L.LN> & U32):
  +e2 : U32 = e
  km(fuel, KCon{kev(WP{1, j, 0, v, Nil{}, Nil{}, fu}, e2), KNil{}}, lnt,
     nlx, R.TNil{}, R.TNil{}, R.TNil{}, kfetch(fs, e2, 0))

def klsubst(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>, +nlx: U32,
            +e: U32, +ps: List<&2, U32>, +qs: List<&2, L.LN>, +fu: U32)
    -> ((Array<T.Ex> & U32) & U32) & (R.Tr<L.LN> & U32):
  +e2 : U32 = e
  km(fuel, KCon{kev(WP{2, 0, 0, 0, ps, qs, fu}, e2), KNil{}}, lnt, nlx,
     R.TNil{}, R.TNil{}, R.TNil{}, kfetch(fs, e2, 0))

def kwhnf(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>, +nlx: U32,
          +mt: R.Tr<I.Meta>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
          +e: U32, +delta: Bool, +fu: U32)
    -> ((Array<T.Ex> & U32) & U32) & (R.Tr<L.LN> & U32):
  +e2 : U32 = e
  km(fuel, KCon{kwev(delta, e2, Nil{}, fu), KNil{}}, lnt, nlx, mt, lp, vt,
     kfetch(fs, e2, 0))
