# The kernel machine over the flat store -- M2 of docs/port-plan.md.
#
# The expression store is an affine Array (plus its next-free index), so it
# can never ride inside a Data record the way the trie rides in IS. The
# discipline that replaces it:
#   * the store flows POSITIONALLY: one (Array<Ex> & U32) tuple threaded
#     through every call, every Array op's pair re-entering via a parameter;
#   * control that must resume after a sub-walk is a FRAME: a Data record of
#     scalars pushed on an explicit stack, dispatched by the entry match;
#   * scalar intermediates still use the old style -- Data records taken
#     apart by accessor defs.
#
# v1 carries exactly the substitution walks (subst.bend's lift and inst),
# validated index-by-index against the trie implementation by fsdiff.bend.

import Base
import ./scan.bend as S
import ./term.bend as T

# --- frames ----------------------------------------------------------------
# A walk is either lift (c = cutoff, d = shift) or inst (c = target index,
# v = value); `op` 0 is lift, 1 is inst. KEvL/KEvI: "the node just fetched is
# `e`'s; evaluate it". The K*2/K*3 frames resume a parent after child
# `slot`'s result arrives in the machine's `ri` register.
type KF is Data:
  KEvL{c: U32, d: U32, e: U32}
  KEvI{c: U32, v: U32, e: U32}
  # after the bvar-eq sentinel walk: pick the real answer for an inst bvar
  KBvI{iseq: Bool, isgt: Bool, i: U32, e: U32}
  KAp2{op: U32, c: U32, d: U32, v: U32, e: U32, f0: U32, a0: U32}
  KAp3{e: U32, f0: U32, a0: U32, r1: U32}
  KLm2{op: U32, c: U32, d: U32, v: U32, e: U32, n: U32, t0: U32, b0: U32,
       bi: U32}
  KLm3{e: U32, n: U32, t0: U32, b0: U32, bi: U32, r1: U32}
  KAl2{op: U32, c: U32, d: U32, v: U32, e: U32, n: U32, t0: U32, b0: U32,
       bi: U32}
  KAl3{e: U32, n: U32, t0: U32, b0: U32, bi: U32, r1: U32}
  KLt2{op: U32, c: U32, d: U32, v: U32, e: U32, n: U32, t0: U32, v0: U32,
       b0: U32}
  KLt3{op: U32, c: U32, d: U32, v: U32, e: U32, n: U32, t0: U32, v0: U32,
       b0: U32, r1: U32}
  KLt4{e: U32, n: U32, t0: U32, v0: U32, b0: U32, r1: U32, r2: U32}
  KPj2{e: U32, tn: U32, ix: U32, s0: U32}

type KS is Data:
  KNil{}
  KCon{f: KF, k: KS}

# pick a frame by a flag (frames are scalars-only Data, strictness is cheap)
def pick_kf(+z: Bool, +x: KF, +y: KF) -> KF:
  match z:
    case True{}:
      x
    case False{}:
      y

# the eval frame for `op` on target e with the op's own parameters
def kev(+op: U32, +c: U32, +d: U32, +v: U32, +e: U32) -> KF:
  pick_kf(U32.is_eq(op, 0), KEvL{c, d, e}, KEvI{c, v, e})

# --- store shufflers --------------------------------------------------------
# The machine's threaded value: ((store & nx) & node) & ri.
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
      +n = nx
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

# inst's bvar leaf, after the sentinel walk: ri is the lifted value if the
# index matched; below the cutoff keeps, above it decrements
def kbv_fin(+iseq: Bool, +isgt: Bool, fs: Array<T.Ex> & U32, +ri: U32,
            +i: U32, +e: U32) -> ((Array<T.Ex> & U32) & T.Ex) & U32:
  match iseq:
    case True{}:
      kkeep(fs, ri)
    case False{}:
      kalloc_if(isgt, fs, T.EBVar{(i - 1 : U32)}, e)

# --- the machine -------------------------------------------------------------
# `tin` is ((store & nx) & node) & ri: the store, the node the top eval frame
# asked for (EBad otherwise), and the last completed walk's result index.
# Rebuild frames compare child results against the original child indices so
# an unchanged subterm keeps its shared index (subst.bend's alloc_if).
def km(fuel: Nat, +stk: KS,
       tin: ((Array<T.Ex> & U32) & T.Ex) & U32) -> (Array<T.Ex> & U32) & U32:
  match fuel stk tin:
    case 0n _ Tuple{Tuple{fs, node}, ri}:
      (fs, 4294967295)
    case 1n+p KNil{} Tuple{Tuple{fs, node}, ri}:
      (fs, ri)
    # ---- eval: lift ----
    case 1n+p KCon{KEvL{c, d, e}, k} Tuple{Tuple{fs, node}, ri}:
      match node:
        case T.EBVar{i}:
          km(p, k, kbv_lift(fs, i, e, c, d))
        case T.EApp{f, a}:
          +c2 = c
          +d2 = d
          +f2 = f
          km(p, KCon{kev(0, c2, d2, 0, f2),
                     KCon{KAp2{0, c2, d2, 0, e, f2, a}, k}},
             kfetch(fs, f2, ri))
        case T.ELam{n, t, b, bi}:
          +c2 = c
          +d2 = d
          +t2 = t
          km(p, KCon{kev(0, c2, d2, 0, t2),
                     KCon{KLm2{0, c2, d2, 0, e, n, t2, b, bi}, k}},
             kfetch(fs, t2, ri))
        case T.EAll{n, t, b, bi}:
          +c2 = c
          +d2 = d
          +t2 = t
          km(p, KCon{kev(0, c2, d2, 0, t2),
                     KCon{KAl2{0, c2, d2, 0, e, n, t2, b, bi}, k}},
             kfetch(fs, t2, ri))
        case T.ELet{n, t, v, b}:
          +c2 = c
          +d2 = d
          +t2 = t
          km(p, KCon{kev(0, c2, d2, 0, t2),
                     KCon{KLt2{0, c2, d2, 0, e, n, t2, v, b}, k}},
             kfetch(fs, t2, ri))
        case T.EProj{tn, i, s}:
          +s2 = s
          km(p, KCon{kev(0, c, d, 0, s2), KCon{KPj2{e, tn, i, s2}, k}},
             kfetch(fs, s2, ri))
        case _:
          km(p, k, kkeep(fs, e))
    # ---- eval: inst ----
    case 1n+p KCon{KEvI{c, v, e}, k} Tuple{Tuple{fs, node}, ri}:
      match node:
        # Three-way branch on a computed comparison: run a lift walk on the
        # VALUE when the index matches, on a sentinel otherwise (EBad is a
        # 1-step keep), then let KBvI pick. The wasted step on the non-eq
        # paths is two machine transitions.
        case T.EBVar{i}:
          +c2 = c
          +i2 = i
          +v2 = v
          +iseq = U32.is_eq(i2, c2)
          +tgt = S.pick(iseq, v2, 4294967295)
          km(p, KCon{kev(0, 0, c2, 0, tgt),
                     KCon{KBvI{iseq, U32.is_gt(i2, c2), i2, e}, k}},
             kfetch(fs, tgt, ri))
        case T.EApp{f, a}:
          +c2 = c
          +v2 = v
          +f2 = f
          km(p, KCon{kev(1, c2, 0, v2, f2),
                     KCon{KAp2{1, c2, 0, v2, e, f2, a}, k}},
             kfetch(fs, f2, ri))
        case T.ELam{n, t, b, bi}:
          +c2 = c
          +v2 = v
          +t2 = t
          km(p, KCon{kev(1, c2, 0, v2, t2),
                     KCon{KLm2{1, c2, 0, v2, e, n, t2, b, bi}, k}},
             kfetch(fs, t2, ri))
        case T.EAll{n, t, b, bi}:
          +c2 = c
          +v2 = v
          +t2 = t
          km(p, KCon{kev(1, c2, 0, v2, t2),
                     KCon{KAl2{1, c2, 0, v2, e, n, t2, b, bi}, k}},
             kfetch(fs, t2, ri))
        case T.ELet{n, t, vv, b}:
          +c2 = c
          +v2 = v
          +t2 = t
          km(p, KCon{kev(1, c2, 0, v2, t2),
                     KCon{KLt2{1, c2, 0, v2, e, n, t2, vv, b}, k}},
             kfetch(fs, t2, ri))
        case T.EProj{tn, i, s}:
          +s2 = s
          km(p, KCon{kev(1, c, 0, v, s2), KCon{KPj2{e, tn, i, s2}, k}},
             kfetch(fs, s2, ri))
        case _:
          km(p, k, kkeep(fs, e))
    # ---- resume frames ----
    case 1n+p KCon{KBvI{iseq, isgt, i, e}, k} Tuple{Tuple{fs, node}, ri}:
      km(p, k, kbv_fin(iseq, isgt, fs, ri, i, e))
    case 1n+p KCon{KAp2{op, c, d, v, e, f0, a0}, k} Tuple{Tuple{fs, node}, ri}:
      +a2 = a0
      km(p, KCon{kev(op, c, d, v, a2), KCon{KAp3{e, f0, a2, ri}, k}},
         kfetch(fs, a2, 0))
    case 1n+p KCon{KAp3{e, f0, a0, r1}, k} Tuple{Tuple{fs, node}, ri}:
      +r1b = r1
      +rib = ri
      km(p, k, kalloc_if(Bool.not(U32.is_eq(r1b, f0) && U32.is_eq(rib, a0)),
                         fs, T.EApp{r1b, rib}, e))
    case 1n+p KCon{KLm2{op, c, d, v, e, n, t0, b0, bi}, k}
         Tuple{Tuple{fs, node}, ri}:
      +b2 = b0
      km(p, KCon{kev(op, (c + 1 : U32), d, v, b2),
                 KCon{KLm3{e, n, t0, b2, bi, ri}, k}},
         kfetch(fs, b2, 0))
    case 1n+p KCon{KLm3{e, n, t0, b0, bi, r1}, k} Tuple{Tuple{fs, node}, ri}:
      +r1b = r1
      +rib = ri
      km(p, k, kalloc_if(Bool.not(U32.is_eq(r1b, t0) && U32.is_eq(rib, b0)),
                         fs, T.ELam{n, r1b, rib, bi}, e))
    case 1n+p KCon{KAl2{op, c, d, v, e, n, t0, b0, bi}, k}
         Tuple{Tuple{fs, node}, ri}:
      +b2 = b0
      km(p, KCon{kev(op, (c + 1 : U32), d, v, b2),
                 KCon{KAl3{e, n, t0, b2, bi, ri}, k}},
         kfetch(fs, b2, 0))
    case 1n+p KCon{KAl3{e, n, t0, b0, bi, r1}, k} Tuple{Tuple{fs, node}, ri}:
      +r1b = r1
      +rib = ri
      km(p, k, kalloc_if(Bool.not(U32.is_eq(r1b, t0) && U32.is_eq(rib, b0)),
                         fs, T.EAll{n, r1b, rib, bi}, e))
    case 1n+p KCon{KLt2{op, c, d, v, e, n, t0, v0, b0}, k}
         Tuple{Tuple{fs, node}, ri}:
      +op2 = op
      +c2 = c
      +d2 = d
      +v2 = v
      +v02 = v0
      km(p, KCon{kev(op2, c2, d2, v2, v02),
                 KCon{KLt3{op2, c2, d2, v2, e, n, t0, v02, b0, ri}, k}},
         kfetch(fs, v02, 0))
    case 1n+p KCon{KLt3{op, c, d, v, e, n, t0, v0, b0, r1}, k}
         Tuple{Tuple{fs, node}, ri}:
      +b2 = b0
      km(p, KCon{kev(op, (c + 1 : U32), d, v, b2),
                 KCon{KLt4{e, n, t0, v0, b2, r1, ri}, k}},
         kfetch(fs, b2, 0))
    case 1n+p KCon{KLt4{e, n, t0, v0, b0, r1, r2}, k}
         Tuple{Tuple{fs, node}, ri}:
      +r1b = r1
      +r2b = r2
      +rib = ri
      km(p, k, kalloc_if(Bool.not(U32.is_eq(r1b, t0) && U32.is_eq(r2b, v0)
                                  && U32.is_eq(rib, b0)),
                         fs, T.ELet{n, r1b, r2b, rib}, e))
    case 1n+p KCon{KPj2{e, tn, ix, s0}, k} Tuple{Tuple{fs, node}, ri}:
      +rib = ri
      km(p, k, kalloc_if(Bool.not(U32.is_eq(rib, s0)), fs,
                         T.EProj{tn, ix, rib}, e))

# --- entry points ------------------------------------------------------------
def klift(fuel: Nat, fs: Array<T.Ex> & U32, +e: U32, +c: U32,
          +d: U32) -> (Array<T.Ex> & U32) & U32:
  km(fuel, KCon{KEvL{c, d, e}, KNil{}}, kfetch(fs, e, 0))

def kinst(fuel: Nat, fs: Array<T.Ex> & U32, +e: U32, +j: U32,
          +v: U32) -> (Array<T.Ex> & U32) & U32:
  km(fuel, KCon{KEvI{j, v, e}, KNil{}}, kfetch(fs, e, 0))
