# The kernel machine over the flat store -- M2 of docs/port-plan.md.
#
# The stores are affine Arrays, so they can never ride inside a Data record
# the way the tries ride in IS. The discipline that replaces it:
#   * the stores flow POSITIONALLY: one STATE tuple
#       ((Array<Ex> & nx) & (Array<LN> & nlx))
#     threaded through every call, every Array op's pair re-entering via a
#     parameter;
#   * control that must resume after a sub-walk is a FRAME: a Data record of
#     scalars (and lists -- lists are Data) pushed on an explicit stack,
#     dispatched by the entry match;
#   * scalar intermediates still use the old style -- Data records taken
#     apart by accessor defs.
#
# v2 carries the three substitution walks -- subst.bend's lift and inst and
# infer.bend's lsubst (universe substitution) -- validated expression by
# expression against the trie implementations by fsdiff.bend.

import Base
import ./scan.bend as S
import ./term.bend as T
import ./level.bend as L

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

# entering a binder bumps lift's cutoff and inst's target; lsubst ignores c
def wp_fu(+w: WP) -> U32:
  match w:
    case WP{op, c, d, v, ps, qs, fu}:
      fu

def wp_bump(+w: WP) -> WP:
  match w:
    case WP{op, c, d, v, ps, qs, fu}:
      WP{op, (c + 1 : U32), d, v, ps, qs, fu}

# --- frames ----------------------------------------------------------------
# KEvL/KEvI/KEvS: "the node just fetched is `e`'s; evaluate it under the
# op". The K*2/K*3/K*4 frames resume a parent after a child's result arrives
# in the machine's `ri` register.
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

# pick a frame by a flag (frames are Data, strictness is cheap)
def pick_kf(+z: Bool, +x: KF, +y: KF) -> KF:
  match z:
    case True{}:
      x
    case False{}:
      y

# the eval frame for a walk on target e
def kev(+wp: WP, +e: U32) -> KF:
  pick_kf(U32.is_eq(wp_fu(wp), 0), KKp{e},
    pick_kf(U32.is_eq(wp_op(wp), 0), KEvL{wp_c(wp), wp_d(wp), e, wp_fu(wp)},
            pick_kf(U32.is_eq(wp_op(wp), 1),
                    KEvI{wp_c(wp), wp_v(wp), e, wp_fu(wp)},
                    KEvS{wp_ps(wp), wp_qs(wp), e, wp_fu(wp)})))

# --- store shufflers --------------------------------------------------------
# STATE  = (Array<T.Ex> & U32) & (Array<L.LN> & U32)
# TIN    = (STATE & T.Ex) & U32   -- stores, fetched node, result register
def kfetch2(pr: Array<T.Ex> & T.Ex, +nx: U32, lv: Array<L.LN> & U32,
            +ri: U32)
    -> (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & T.Ex) & U32:
  match pr lv:
    case Tuple{ex, node} Tuple{ln, nlx}:
      ((((ex, nx), (ln, nlx)), node), ri)

def kfetch(st: (Array<T.Ex> & U32) & (Array<L.LN> & U32), +i: U32,
           +ri: U32)
    -> (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & T.Ex) & U32:
  match st:
    case Tuple{Tuple{ex, nx}, lv}:
      kfetch2(Array.get(T.Ex, ex, i), nx, lv, ri)

# allocate `node`, result register = fresh index
def kalloc2(ex: Array<T.Ex>, +nx: U32, ln: Array<L.LN>, +nlx: U32, +n: U32)
    -> (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & T.Ex) & U32:
  ((((ex, nx), (ln, nlx)), T.EBad{}), n)

def kalloc(st: (Array<T.Ex> & U32) & (Array<L.LN> & U32), +node: T.Ex)
    -> (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & T.Ex) & U32:
  match st:
    case Tuple{Tuple{ex, nx}, Tuple{ln, nlx}}:
      +n : U32 = nx
      kalloc2(Array.set(T.Ex, ex, n, node), (n + 1 : U32), ln, nlx, n)

# no allocation, result register = existing index
def kkeep(st: (Array<T.Ex> & U32) & (Array<L.LN> & U32), +e: U32)
    -> (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & T.Ex) & U32:
  ((st, T.EBad{}), e)

# allocate if changed, else keep e
def kalloc_if(+chg: Bool, st: (Array<T.Ex> & U32) & (Array<L.LN> & U32),
              +node: T.Ex, +e: U32)
    -> (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & T.Ex) & U32:
  match chg:
    case True{}:
      kalloc(st, node)
    case False{}:
      kkeep(st, e)

# lift's bvar leaf: shift a free index, keep a bound one
def kbv_lift(st: (Array<T.Ex> & U32) & (Array<L.LN> & U32), +i: U32,
             +e: U32, +c: U32, +d: U32)
    -> (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & T.Ex) & U32:
  kalloc_if(U32.is_ge(i, c), st, T.EBVar{(i + d : U32)}, e)

# inst's bvar leaf, after the sentinel walk: ri is the lifted value if the
# index matched; below the cutoff keeps, above it decrements
def kbv_fin(+iseq: Bool, +isgt: Bool,
            st: (Array<T.Ex> & U32) & (Array<L.LN> & U32), +ri: U32,
            +i: U32, +e: U32)
    -> (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & T.Ex) & U32:
  match iseq:
    case True{}:
      kkeep(st, ri)
    case False{}:
      kalloc_if(isgt, st, T.EBVar{(i - 1 : U32)}, e)

# --- lsubst leaves -----------------------------------------------------------
# A level is allocated by normal form alone (infer.bend's alloc_lvl): set
# ln[nlx], bump nlx.
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

# substitute every level in `us`, allocating each result; answers the level
# store and the fresh indices in order. INVARIANT: `pr` is the ln-read of
# us's head (a dummy read when us is empty).
def ksub_lvls(us: List<&2, U32>, +ps: List<&2, U32>, +qs: List<&2, L.LN>,
              +nlx: U32, acc: List<&2, U32>,
              pr: Array<L.LN> & L.LN) -> (Array<L.LN> & U32) & List<&2, U32>:
  match us pr:
    case Nil{} Tuple{ln, old}:
      ((ln, nlx), krev(acc, Nil{}))
    case Con{head, tail} Tuple{ln, old}:
      +nl : U32 = nlx
      +t2 : List<&2, U32> = tail
      ksub_lvls(t2, ps, qs, (nl + 1 : U32), Con{nl, acc},
                Array.get(L.LN,
                          Array.set(L.LN, ln, nl, L.ln_subst(old, ps, qs)),
                          head_u(t2, 0)))

# EConst under lsubst: substitute the levels, allocate the new constant
def ksub_const2(r: (Array<L.LN> & U32) & List<&2, U32>,
                exp: Array<T.Ex> & U32, +n: U32)
    -> (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & T.Ex) & U32:
  match r:
    case Tuple{lnp, xs}:
      kalloc((exp, lnp), T.EConst{n, xs})

def ksub_const(st: (Array<T.Ex> & U32) & (Array<L.LN> & U32), +n: U32,
               us: List<&2, U32>, +ps: List<&2, U32>, +qs: List<&2, L.LN>)
    -> (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & T.Ex) & U32:
  match st:
    case Tuple{exp, Tuple{ln, nlx}}:
      +u2 : List<&2, U32> = us
      ksub_const2(ksub_lvls(u2, ps, qs, nlx, Nil{},
                            Array.get(L.LN, ln, head_u(u2, 0))),
                  exp, n)

# ESort under lsubst: new sort only if the substitution changed the form
def kalloc_sort(st: (Array<T.Ex> & U32) & (Array<L.LN> & U32), +u: L.LN)
    -> (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & T.Ex) & U32:
  match st:
    case Tuple{exp, Tuple{ln, nlx}}:
      +nl : U32 = nlx
      kalloc((exp, (Array.set(L.LN, ln, nl, u), (nl + 1 : U32))),
             T.ESort{nl})

def ksub_sort3(+same: Bool, +u: L.LN,
               st: (Array<T.Ex> & U32) & (Array<L.LN> & U32), +e: U32)
    -> (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & T.Ex) & U32:
  match same:
    case True{}:
      kkeep(st, e)
    case False{}:
      kalloc_sort(st, u)

def ksub_sort2(pr: Array<L.LN> & L.LN, +nlx: U32, exp: Array<T.Ex> & U32,
               +ps: List<&2, U32>, +qs: List<&2, L.LN>, +e: U32)
    -> (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & T.Ex) & U32:
  match pr:
    case Tuple{ln, old}:
      +o : L.LN = old
      +u : L.LN = L.ln_subst(o, ps, qs)
      +u2 : L.LN = u
      ksub_sort3(L.tri_is_yes(L.ln_cmp(o, u2)), u2, (exp, (ln, nlx)), e)

def ksub_sort(st: (Array<T.Ex> & U32) & (Array<L.LN> & U32), +l: U32,
              +ps: List<&2, U32>, +qs: List<&2, L.LN>, +e: U32)
    -> (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & T.Ex) & U32:
  match st:
    case Tuple{exp, Tuple{ln, nlx}}:
      ksub_sort2(Array.get(L.LN, ln, l), nlx, exp, ps, qs, e)

# --- the machine -------------------------------------------------------------
# `tin` is ((STATE & node) & ri): the stores, the node the top eval frame
# asked for (EBad otherwise), and the last completed walk's result index.
# Rebuild frames compare child results against the original child indices so
# an unchanged subterm keeps its shared index (alloc_if).
def km(fuel: Nat, +stk: KS,
       tin: (((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & T.Ex) & U32)
    -> ((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & U32:
  match fuel stk tin:
    case 0n _ Tuple{Tuple{st, node}, ri}:
      (st, 4294967295)
    case 1n+p KNil{} Tuple{Tuple{st, node}, ri}:
      (st, ri)
    case 1n+p KCon{KKp{e}, k} Tuple{Tuple{st, node}, ri}:
      km(p, k, kkeep(st, e))
    # ---- eval: lift ----
    case 1n+p KCon{KEvL{c, d, e, fu}, k} Tuple{Tuple{st, node}, ri}:
      match node:
        case T.EBVar{i}:
          km(p, k, kbv_lift(st, i, e, c, d))
        case T.EApp{f, a}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +f2 : U32 = f
          km(p, KCon{kev(w, f2), KCon{KAp2{w, e, f2, a}, k}},
             kfetch(st, f2, ri))
        case T.ELam{n, t, b, bi}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLm2{w, e, n, t2, b, bi}, k}},
             kfetch(st, t2, ri))
        case T.EAll{n, t, b, bi}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KAl2{w, e, n, t2, b, bi}, k}},
             kfetch(st, t2, ri))
        case T.ELet{n, t, v, b}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLt2{w, e, n, t2, v, b}, k}},
             kfetch(st, t2, ri))
        case T.EProj{tn, i, s}:
          +w : WP = WP{0, c, d, 0, Nil{}, Nil{}, (fu - 1 : U32)}
          +s2 : U32 = s
          km(p, KCon{kev(w, s2), KCon{KPj2{e, tn, i, s2}, k}},
             kfetch(st, s2, ri))
        case _:
          km(p, k, kkeep(st, e))
    # ---- eval: inst ----
    case 1n+p KCon{KEvI{c, v, e, fu}, k} Tuple{Tuple{st, node}, ri}:
      match node:
        # Three-way branch on a computed comparison: run a lift walk on the
        # VALUE when the index matches, on a sentinel otherwise (EBad is a
        # 1-step keep), then let KBvI pick.
        case T.EBVar{i}:
          +c2 : U32 = c
          +i2 : U32 = i
          +v2 : U32 = v
          +iseq : Bool = U32.is_eq(i2, c2)
          +tgt : U32 = S.pick(iseq, v2, 4294967295)
          km(p, KCon{kev(WP{0, 0, c2, 0, Nil{}, Nil{}, 256}, tgt),
                     KCon{KBvI{iseq, U32.is_gt(i2, c2), i2, e}, k}},
             kfetch(st, tgt, ri))
        case T.EApp{f, a}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +f2 : U32 = f
          km(p, KCon{kev(w, f2), KCon{KAp2{w, e, f2, a}, k}},
             kfetch(st, f2, ri))
        case T.ELam{n, t, b, bi}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLm2{w, e, n, t2, b, bi}, k}},
             kfetch(st, t2, ri))
        case T.EAll{n, t, b, bi}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KAl2{w, e, n, t2, b, bi}, k}},
             kfetch(st, t2, ri))
        case T.ELet{n, t, vv, b}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLt2{w, e, n, t2, vv, b}, k}},
             kfetch(st, t2, ri))
        case T.EProj{tn, i, s}:
          +w : WP = WP{1, c, 0, v, Nil{}, Nil{}, (fu - 1 : U32)}
          +s2 : U32 = s
          km(p, KCon{kev(w, s2), KCon{KPj2{e, tn, i, s2}, k}},
             kfetch(st, s2, ri))
        case _:
          km(p, k, kkeep(st, e))
    # ---- eval: lsubst ----
    case 1n+p KCon{KEvS{ps, qs, e, fu}, k} Tuple{Tuple{st, node}, ri}:
      match node:
        case T.ESort{l}:
          km(p, k, ksub_sort(st, l, ps, qs, e))
        case T.EConst{n, us}:
          km(p, k, ksub_const(st, n, us, ps, qs))
        case T.EApp{f, a}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +f2 : U32 = f
          km(p, KCon{kev(w, f2), KCon{KAp2{w, e, f2, a}, k}},
             kfetch(st, f2, ri))
        case T.ELam{n, t, b, bi}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLm2{w, e, n, t2, b, bi}, k}},
             kfetch(st, t2, ri))
        case T.EAll{n, t, b, bi}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KAl2{w, e, n, t2, b, bi}, k}},
             kfetch(st, t2, ri))
        case T.ELet{n, t, v, b}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +t2 : U32 = t
          km(p, KCon{kev(w, t2), KCon{KLt2{w, e, n, t2, v, b}, k}},
             kfetch(st, t2, ri))
        case T.EProj{tn, i, s}:
          +w : WP = WP{2, 0, 0, 0, ps, qs, (fu - 1 : U32)}
          +s2 : U32 = s
          km(p, KCon{kev(w, s2), KCon{KPj2{e, tn, i, s2}, k}},
             kfetch(st, s2, ri))
        case _:
          km(p, k, kkeep(st, e))
    # ---- resume frames ----
    case 1n+p KCon{KBvI{iseq, isgt, i, e}, k} Tuple{Tuple{st, node}, ri}:
      km(p, k, kbv_fin(iseq, isgt, st, ri, i, e))
    case 1n+p KCon{KAp2{wp, e, f0, a0}, k} Tuple{Tuple{st, node}, ri}:
      +w : WP = wp
      +a2 : U32 = a0
      km(p, KCon{kev(w, a2), KCon{KAp3{e, f0, a2, ri}, k}},
         kfetch(st, a2, 0))
    case 1n+p KCon{KAp3{e, f0, a0, r1}, k} Tuple{Tuple{st, node}, ri}:
      +r1b : U32 = r1
      +rib : U32 = ri
      km(p, k, kalloc_if(Bool.not(U32.is_eq(r1b, f0) && U32.is_eq(rib, a0)),
                         st, T.EApp{r1b, rib}, e))
    case 1n+p KCon{KLm2{wp, e, n, t0, b0, bi}, k} Tuple{Tuple{st, node}, ri}:
      +b2 : U32 = b0
      km(p, KCon{kev(wp_bump(wp), b2), KCon{KLm3{e, n, t0, b2, bi, ri}, k}},
         kfetch(st, b2, 0))
    case 1n+p KCon{KLm3{e, n, t0, b0, bi, r1}, k} Tuple{Tuple{st, node}, ri}:
      +r1b : U32 = r1
      +rib : U32 = ri
      km(p, k, kalloc_if(Bool.not(U32.is_eq(r1b, t0) && U32.is_eq(rib, b0)),
                         st, T.ELam{n, r1b, rib, bi}, e))
    case 1n+p KCon{KAl2{wp, e, n, t0, b0, bi}, k} Tuple{Tuple{st, node}, ri}:
      +b2 : U32 = b0
      km(p, KCon{kev(wp_bump(wp), b2), KCon{KAl3{e, n, t0, b2, bi, ri}, k}},
         kfetch(st, b2, 0))
    case 1n+p KCon{KAl3{e, n, t0, b0, bi, r1}, k} Tuple{Tuple{st, node}, ri}:
      +r1b : U32 = r1
      +rib : U32 = ri
      km(p, k, kalloc_if(Bool.not(U32.is_eq(r1b, t0) && U32.is_eq(rib, b0)),
                         st, T.EAll{n, r1b, rib, bi}, e))
    case 1n+p KCon{KLt2{wp, e, n, t0, v0, b0}, k} Tuple{Tuple{st, node}, ri}:
      +w : WP = wp
      +v02 : U32 = v0
      km(p, KCon{kev(w, v02), KCon{KLt3{w, e, n, t0, v02, b0, ri}, k}},
         kfetch(st, v02, 0))
    case 1n+p KCon{KLt3{wp, e, n, t0, v0, b0, r1}, k}
         Tuple{Tuple{st, node}, ri}:
      +b2 : U32 = b0
      km(p, KCon{kev(wp_bump(wp), b2),
                 KCon{KLt4{e, n, t0, v0, b2, r1, ri}, k}},
         kfetch(st, b2, 0))
    case 1n+p KCon{KLt4{e, n, t0, v0, b0, r1, r2}, k}
         Tuple{Tuple{st, node}, ri}:
      +r1b : U32 = r1
      +r2b : U32 = r2
      +rib : U32 = ri
      km(p, k, kalloc_if(Bool.not(U32.is_eq(r1b, t0) && U32.is_eq(r2b, v0)
                                  && U32.is_eq(rib, b0)),
                         st, T.ELet{n, r1b, r2b, rib}, e))
    case 1n+p KCon{KPj2{e, tn, ix, s0}, k} Tuple{Tuple{st, node}, ri}:
      +rib : U32 = ri
      km(p, k, kalloc_if(Bool.not(U32.is_eq(rib, s0)), st,
                         T.EProj{tn, ix, rib}, e))

# --- entry points ------------------------------------------------------------
def klift(fuel: Nat, st: (Array<T.Ex> & U32) & (Array<L.LN> & U32), +e: U32,
          +c: U32, +d: U32,
          +fu: U32) -> ((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & U32:
  +e2 : U32 = e
  km(fuel, KCon{kev(WP{0, c, d, 0, Nil{}, Nil{}, fu}, e2), KNil{}},
     kfetch(st, e2, 0))

def kinst(fuel: Nat, st: (Array<T.Ex> & U32) & (Array<L.LN> & U32), +e: U32,
          +j: U32, +v: U32,
          +fu: U32) -> ((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & U32:
  +e2 : U32 = e
  km(fuel, KCon{kev(WP{1, j, 0, v, Nil{}, Nil{}, fu}, e2), KNil{}},
     kfetch(st, e2, 0))

def klsubst(fuel: Nat, st: (Array<T.Ex> & U32) & (Array<L.LN> & U32),
            +e: U32, +ps: List<&2, U32>, +qs: List<&2, L.LN>, +fu: U32)
    -> ((Array<T.Ex> & U32) & (Array<L.LN> & U32)) & U32:
  +e2 : U32 = e
  km(fuel, KCon{kev(WP{2, 0, 0, 0, ps, qs, fu}, e2), KNil{}},
     kfetch(st, e2, 0))
