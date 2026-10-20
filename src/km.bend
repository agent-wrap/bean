# The kernel machine over the flat store -- M2 of docs/port-plan.md.
#
# Architecture call: ONLY the expression store is hot enough to need the
# flat Array (it is Type-kinded, one owner, so it flows POSITIONALLY in a
# threaded tuple and every Array op's pair re-enters via a parameter).
# Levels are few and cold: they stay a Data TRIE (lnt) plus next-index
# (nlx), passed as ordinary reusable parameters, exactly as in the old
# kernel -- idiomatic code, no pair gymnastics. Control that must resume
# after a sub-walk is a FRAME: a Data record of scalars/lists on an explicit
# stack, dispatched by the entry match.
#
# v3 carries the three substitution walks -- subst.bend's lift and inst and
# infer.bend's lsubst (universe substitution) -- validated expression by
# expression against the trie implementations by fsdiff.bend. Depth fuel is
# part of the SEMANTICS (the old walks keep the subtree at depth 256); it
# rides in each eval frame and resets exactly where the old code resets.

import Base
import ./scan.bend as S
import ./term.bend as T
import ./level.bend as L
import ./trie.bend as R

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
# TIN = ((Array<T.Ex> & U32) & T.Ex) & U32 -- store, fetched node, result
def kfetch2(pr: Array<T.Ex> & T.Ex, +nx: U32,
            +ri: U32) -> ((Array<T.Ex> & U32) & T.Ex) & U32:
  match pr:
    case Tuple{ex, node}:
      (((ex, nx), node), ri)

def kfetch(fs: Array<T.Ex> & U32, +i: U32,
           +ri: U32) -> ((Array<T.Ex> & U32) & T.Ex) & U32:
  match fs:
    case Tuple{ex, nx}:
      kfetch2(Array.get(T.Ex, ex, i), nx, ri)

# allocate `node`, result register = fresh index
def kalloc(fs: Array<T.Ex> & U32,
           +node: T.Ex) -> ((Array<T.Ex> & U32) & T.Ex) & U32:
  match fs:
    case Tuple{ex, nx}:
      +n : U32 = nx
      (((Array.set(T.Ex, ex, n, node), (n + 1 : U32)), T.EBad{}), n)

# no allocation, result register = existing index
def kkeep(fs: Array<T.Ex> & U32,
          +e: U32) -> ((Array<T.Ex> & U32) & T.Ex) & U32:
  ((fs, T.EBad{}), e)

# allocate if changed, else keep e
def kalloc_if(+chg: Bool, fs: Array<T.Ex> & U32, +node: T.Ex,
              +e: U32) -> ((Array<T.Ex> & U32) & T.Ex) & U32:
  match chg:
    case True{}:
      kalloc(fs, node)
    case False{}:
      kkeep(fs, e)

# lift's bvar leaf: shift a free index, keep a bound one
def kbv_lift(fs: Array<T.Ex> & U32, +i: U32, +e: U32, +c: U32,
             +d: U32) -> ((Array<T.Ex> & U32) & T.Ex) & U32:
  kalloc_if(U32.is_ge(i, c), fs, T.EBVar{(i + d : U32)}, e)

# inst's bvar leaf, after the sentinel walk
def kbv_fin(+iseq: Bool, +isgt: Bool, fs: Array<T.Ex> & U32, +ri: U32,
            +i: U32, +e: U32) -> ((Array<T.Ex> & U32) & T.Ex) & U32:
  match iseq:
    case True{}:
      kkeep(fs, ri)
    case False{}:
      kalloc_if(isgt, fs, T.EBVar{(i - 1 : U32)}, e)

# lsubst's sort leaf, decided: keep when the substitution changed nothing,
# else allocate ESort over the freshly allocated level nlx
def ksort3(+same: Bool, fs: Array<T.Ex> & U32, +nlx: U32,
           +e: U32) -> ((Array<T.Ex> & U32) & T.Ex) & U32:
  match same:
    case True{}:
      kkeep(fs, e)
    case False{}:
      kalloc(fs, T.ESort{nlx})

# lsubst's const leaf: allocate the constant over fresh level indices
def ksconst(fs: Array<T.Ex> & U32, +n: U32,
            +xs: List<&2, U32>) -> ((Array<T.Ex> & U32) & T.Ex) & U32:
  kalloc(fs, T.EConst{n, xs})

# --- the machine -------------------------------------------------------------
# The level trie and its next index thread as plain Data parameters; the
# expression store threads inside `tin`. Returns ((store & result) & levels).
def km(fuel: Nat, +stk: KS, +lnt: R.Tr<L.LN>, +nlx: U32,
       tin: ((Array<T.Ex> & U32) & T.Ex) & U32)
    -> ((Array<T.Ex> & U32) & U32) & (R.Tr<L.LN> & U32):
  match fuel stk tin:
    case 0n _ Tuple{Tuple{fs, node}, ri}:
      ((fs, 4294967295), (lnt, nlx))
    case 1n+p KNil{} Tuple{Tuple{fs, node}, ri}:
      ((fs, ri), (lnt, nlx))
    case 1n+p KCon{KKp{e}, k} Tuple{Tuple{fs, node}, ri}:
      km(p, k, lnt, nlx, kkeep(fs, e))
    # ---- eval: lift ----
    case 1n+p KCon{KEvL{c, d, e, fu}, k} Tuple{Tuple{fs, node}, ri}:
      match node:
        case T.EBVar{i}:
          km(p, k, lnt, nlx, kbv_lift(fs, i, e, c, d))
        case T.EApp{f, a}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +f2 : U32 = f
          km(p, KCon{kev(w, f2), KCon{KAp2{w, e, f2, a}, k}}, lnt, nlx,
             kfetch(fs, f2, ri))
        case T.ELam{n, t, b, bi}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLm2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, kfetch(fs, t2, ri))
        case T.EAll{n, t, b, bi}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KAl2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, kfetch(fs, t2, ri))
        case T.ELet{n, t, v, b}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLt2{w, e, n, t2, v, b}, k}}, lnt,
             nlx, kfetch(fs, t2, ri))
        case T.EProj{tn, i, s}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +s2 : U32 = s
          km(p, KCon{kev(w, s2), KCon{KPj2{e, tn, i, s2}, k}}, lnt, nlx,
             kfetch(fs, s2, ri))
        case _:
          km(p, k, lnt, nlx, kkeep(fs, e))
    # ---- eval: inst ----
    case 1n+p KCon{KEvI{c, v, e, fu}, k} Tuple{Tuple{fs, node}, ri}:
      match node:
        # Three-way branch on a computed comparison: run a lift walk on the
        # VALUE when the index matches (fresh 256 depth, as the old code
        # resets), on a sentinel otherwise (EBad is a 1-step keep), then let
        # KBvI pick.
        case T.EBVar{i}:
          +c2 : U32 = c
          +i2 : U32 = i
          +v2 : U32 = v
          +iseq : Bool = U32.is_eq(i2, c2)
          +tgt : U32 = S.pick(iseq, v2, 4294967295)
          km(p, KCon{kev(WP{0, 0, c2, 0, Nil{}, Nil{}, 256}, tgt),
                     KCon{KBvI{iseq, U32.is_gt(i2, c2), i2, e}, k}},
             lnt, nlx, kfetch(fs, tgt, ri))
        case T.EApp{f, a}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +f2 : U32 = f
          km(p, KCon{kev(w, f2), KCon{KAp2{w, e, f2, a}, k}}, lnt, nlx,
             kfetch(fs, f2, ri))
        case T.ELam{n, t, b, bi}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLm2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, kfetch(fs, t2, ri))
        case T.EAll{n, t, b, bi}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KAl2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, kfetch(fs, t2, ri))
        case T.ELet{n, t, vv, b}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLt2{w, e, n, t2, vv, b}, k}}, lnt,
             nlx, kfetch(fs, t2, ri))
        case T.EProj{tn, i, s}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +s2 : U32 = s
          km(p, KCon{kev(w, s2), KCon{KPj2{e, tn, i, s2}, k}}, lnt, nlx,
             kfetch(fs, s2, ri))
        case _:
          km(p, k, lnt, nlx, kkeep(fs, e))
    # ---- eval: lsubst ----
    case 1n+p KCon{KEvS{ps, qs, e, fu}, k} Tuple{Tuple{fs, node}, ri}:
      match node:
        case T.ESort{l}:
          +old : L.LN = R.get(L.LN, 32n, lnt, l, L.LNun{})
          +u : L.LN = L.ln_subst(old, ps, qs)
          +same : Bool = L.tri_is_yes(L.ln_cmp(old, u))
          +nl : U32 = nlx
          km(p, k,
             R.sub(L.LN, same, lnt, R.set(L.LN, 32n, lnt, nl, u, L.LNun{})),
             S.pick(same, nl, (nl + 1 : U32)),
             ksort3(same, fs, nl, e))
        case T.EConst{n, us}:
          +r : LVS = klsub_lvls(us, lnt, nlx, ps, qs)
          km(p, k, lvs_t(r), lvs_nx(r), ksconst(fs, n, lvs_xs(r)))
        case T.EApp{f, a}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +f2 : U32 = f
          km(p, KCon{kev(w, f2), KCon{KAp2{w, e, f2, a}, k}}, lnt, nlx,
             kfetch(fs, f2, ri))
        case T.ELam{n, t, b, bi}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLm2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, kfetch(fs, t2, ri))
        case T.EAll{n, t, b, bi}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KAl2{w, e, n, t2, b, bi}, k}}, lnt,
             nlx, kfetch(fs, t2, ri))
        case T.ELet{n, t, v, b}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLt2{w, e, n, t2, v, b}, k}}, lnt,
             nlx, kfetch(fs, t2, ri))
        case T.EProj{tn, i, s}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +s2 : U32 = s
          km(p, KCon{kev(w, s2), KCon{KPj2{e, tn, i, s2}, k}}, lnt, nlx,
             kfetch(fs, s2, ri))
        case _:
          km(p, k, lnt, nlx, kkeep(fs, e))
    # ---- resume frames ----
    case 1n+p KCon{KBvI{iseq, isgt, i, e}, k} Tuple{Tuple{fs, node}, ri}:
      km(p, k, lnt, nlx, kbv_fin(iseq, isgt, fs, ri, i, e))
    case 1n+p KCon{KAp2{wp, e, f0, a0}, k} Tuple{Tuple{fs, node}, ri}:
      +w : WP = wp
      +a2 : U32 = a0
      km(p, KCon{kev(w, a2), KCon{KAp3{e, f0, a2, ri}, k}}, lnt, nlx,
         kfetch(fs, a2, 0))
    case 1n+p KCon{KAp3{e, f0, a0, r1}, k} Tuple{Tuple{fs, node}, ri}:
      +r1b : U32 = r1
      +rib : U32 = ri
      km(p, k, lnt, nlx,
         kalloc_if(Bool.not(U32.is_eq(r1b, f0) && U32.is_eq(rib, a0)),
                   fs, T.EApp{r1b, rib}, e))
    case 1n+p KCon{KLm2{wp, e, n, t0, b0, bi}, k} Tuple{Tuple{fs, node}, ri}:
      +b2 : U32 = b0
      km(p, KCon{kev(wp_bump(wp), b2), KCon{KLm3{e, n, t0, b2, bi, ri}, k}},
         lnt, nlx, kfetch(fs, b2, 0))
    case 1n+p KCon{KLm3{e, n, t0, b0, bi, r1}, k} Tuple{Tuple{fs, node}, ri}:
      +r1b : U32 = r1
      +rib : U32 = ri
      km(p, k, lnt, nlx,
         kalloc_if(Bool.not(U32.is_eq(r1b, t0) && U32.is_eq(rib, b0)),
                   fs, T.ELam{n, r1b, rib, bi}, e))
    case 1n+p KCon{KAl2{wp, e, n, t0, b0, bi}, k} Tuple{Tuple{fs, node}, ri}:
      +b2 : U32 = b0
      km(p, KCon{kev(wp_bump(wp), b2), KCon{KAl3{e, n, t0, b2, bi, ri}, k}},
         lnt, nlx, kfetch(fs, b2, 0))
    case 1n+p KCon{KAl3{e, n, t0, b0, bi, r1}, k} Tuple{Tuple{fs, node}, ri}:
      +r1b : U32 = r1
      +rib : U32 = ri
      km(p, k, lnt, nlx,
         kalloc_if(Bool.not(U32.is_eq(r1b, t0) && U32.is_eq(rib, b0)),
                   fs, T.EAll{n, r1b, rib, bi}, e))
    case 1n+p KCon{KLt2{wp, e, n, t0, v0, b0}, k} Tuple{Tuple{fs, node}, ri}:
      +w : WP = wp
      +v02 : U32 = v0
      km(p, KCon{kev(w, v02), KCon{KLt3{w, e, n, t0, v02, b0, ri}, k}},
         lnt, nlx, kfetch(fs, v02, 0))
    case 1n+p KCon{KLt3{wp, e, n, t0, v0, b0, r1}, k}
         Tuple{Tuple{fs, node}, ri}:
      +b2 : U32 = b0
      km(p, KCon{kev(wp_bump(wp), b2),
                 KCon{KLt4{e, n, t0, v0, b2, r1, ri}, k}},
         lnt, nlx, kfetch(fs, b2, 0))
    case 1n+p KCon{KLt4{e, n, t0, v0, b0, r1, r2}, k}
         Tuple{Tuple{fs, node}, ri}:
      +r1b : U32 = r1
      +r2b : U32 = r2
      +rib : U32 = ri
      km(p, k, lnt, nlx,
         kalloc_if(Bool.not(U32.is_eq(r1b, t0) && U32.is_eq(r2b, v0)
                            && U32.is_eq(rib, b0)),
                   fs, T.ELet{n, r1b, r2b, rib}, e))
    case 1n+p KCon{KPj2{e, tn, ix, s0}, k} Tuple{Tuple{fs, node}, ri}:
      +rib : U32 = ri
      km(p, k, lnt, nlx,
         kalloc_if(Bool.not(U32.is_eq(rib, s0)), fs,
                   T.EProj{tn, ix, rib}, e))

# --- entry points ------------------------------------------------------------
def klift(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>, +nlx: U32,
          +e: U32, +c: U32, +d: U32, +fu: U32)
    -> ((Array<T.Ex> & U32) & U32) & (R.Tr<L.LN> & U32):
  +e2 : U32 = e
  km(fuel, KCon{kev(WP{0, c, d, 0, Nil{}, Nil{}, fu}, e2), KNil{}}, lnt,
     nlx, kfetch(fs, e2, 0))

def kinst(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>, +nlx: U32,
          +e: U32, +j: U32, +v: U32, +fu: U32)
    -> ((Array<T.Ex> & U32) & U32) & (R.Tr<L.LN> & U32):
  +e2 : U32 = e
  km(fuel, KCon{kev(WP{1, j, 0, v, Nil{}, Nil{}, fu}, e2), KNil{}}, lnt,
     nlx, kfetch(fs, e2, 0))

def klsubst(fuel: Nat, fs: Array<T.Ex> & U32, +lnt: R.Tr<L.LN>, +nlx: U32,
            +e: U32, +ps: List<&2, U32>, +qs: List<&2, L.LN>, +fu: U32)
    -> ((Array<T.Ex> & U32) & U32) & (R.Tr<L.LN> & U32):
  +e2 : U32 = e
  km(fuel, KCon{kev(WP{2, 0, 0, 0, ps, qs, fu}, e2), KNil{}}, lnt, nlx,
     kfetch(fs, e2, 0))
