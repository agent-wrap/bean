# Lifting and instantiation over the expression trie.
#
# These are the first operations that *build* terms, so they thread a growing
# trie and a next-free index. The trick that makes them ordinary recursive
# functions is that the result record is `Data`: it can be bound locally and
# taken apart with accessor defs, each of which matches its own parameter. A
# helper that destructured it and then called back would be mutual recursion,
# which Bend forbids -- accessors are not, because they do not recurse.
#
# New nodes are allocated above the highest index the export used, so the
# exporter's own numbering stays valid and shared subterms keep their
# identity.

import Base
import ./scan.bend as S
import ./term.bend as T
import ./trie.bend as R

type SR is Data:
  SR{t: R.Tr<T.Ex>, nx: U32, i: U32}

def sr_t(+r: SR) -> R.Tr<T.Ex>:
  match r:
    case SR{t, nx, i}:
      t

def sr_nx(+r: SR) -> U32:
  match r:
    case SR{t, nx, i}:
      nx

def sr_i(+r: SR) -> U32:
  match r:
    case SR{t, nx, i}:
      i

def pick_sr(+z: Bool, +x: SR, +y: SR) -> SR:
  match z:
    case True{}:
      x
    case False{}:
      y

def ex_at(+t: R.Tr<T.Ex>, +i: U32) -> T.Ex:
  R.get(T.Ex, 32n, t, i, T.EBad{})

def alloc(+t: R.Tr<T.Ex>, +nx: U32, +x: T.Ex) -> SR:
  SR{R.set(T.Ex, 32n, t, nx, x, T.EBad{}), (nx + 1 : U32), nx}

# Nothing to build: the index is already right.
def keep(+t: R.Tr<T.Ex>, +nx: U32, +i: U32) -> SR:
  SR{t, nx, i}

# Reuse the original index when nothing below changed. Without this, every
# lift and every instantiation copies a whole subterm, and the export is a
# DAG with heavy sharing -- one node in the magma test is named 1,615 times.
def alloc_if(+t: R.Tr<T.Ex>, +nx: U32, +x: T.Ex, +e: U32,
             +changed: Bool) -> SR:
  pick_sr(changed, alloc(t, nx, x), keep(t, nx, e))

# --- lift ----------------------------------------------------------------
# Shift every free de Bruijn index at or above `c` up by `d`.
#
# One self-recursive function: `lift -> lift_go -> lift` would be mutual. The
# node therefore arrives as a parameter, and each recursive call fetches its
# child from the trie as it stands after the previous call.
def lift_bvar(+t: R.Tr<T.Ex>, +nx: U32, +i: U32, +e: U32, +c: U32,
              +d: U32) -> SR:
  pick_sr(U32.is_ge(i, c), alloc(t, nx, T.EBVar{(i + d : U32)}),
          keep(t, nx, e))

def lift(+fuel: Nat, +t: R.Tr<T.Ex>, +nx: U32, +x: T.Ex, +e: U32, +c: U32,
         +d: U32) -> SR:
  match fuel x:
    case 0n _:
      keep(t, nx, e)
    case 1n+p T.EBVar{i}:
      lift_bvar(t, nx, i, e, c, d)
    case 1n+p T.EApp{f, a}:
      +pf = p
      +r1 = lift(pf, t, nx, ex_at(t, f), f, c, d)
      +r2 = lift(pf, sr_t(r1), sr_nx(r1), ex_at(sr_t(r1), a), a, c, d)
      alloc_if(sr_t(r2), sr_nx(r2), T.EApp{sr_i(r1), sr_i(r2)}, e,
               Bool.not(U32.is_eq(sr_i(r1), f) && U32.is_eq(sr_i(r2), a)))
    case 1n+p T.ELam{n, ty, b, bi}:
      +pf = p
      +r1 = lift(pf, t, nx, ex_at(t, ty), ty, c, d)
      +r2 = lift(pf, sr_t(r1), sr_nx(r1), ex_at(sr_t(r1), b), b,
                 (c + 1 : U32), d)
      alloc_if(sr_t(r2), sr_nx(r2), T.ELam{n, sr_i(r1), sr_i(r2), bi}, e,
               Bool.not(U32.is_eq(sr_i(r1), ty) && U32.is_eq(sr_i(r2), b)))
    case 1n+p T.EAll{n, ty, b, bi}:
      +pf = p
      +r1 = lift(pf, t, nx, ex_at(t, ty), ty, c, d)
      +r2 = lift(pf, sr_t(r1), sr_nx(r1), ex_at(sr_t(r1), b), b,
                 (c + 1 : U32), d)
      alloc_if(sr_t(r2), sr_nx(r2), T.EAll{n, sr_i(r1), sr_i(r2), bi}, e,
               Bool.not(U32.is_eq(sr_i(r1), ty) && U32.is_eq(sr_i(r2), b)))
    case 1n+p T.ELet{n, ty, v, b}:
      +pf = p
      +r1 = lift(pf, t, nx, ex_at(t, ty), ty, c, d)
      +r2 = lift(pf, sr_t(r1), sr_nx(r1), ex_at(sr_t(r1), v), v, c, d)
      +r3 = lift(pf, sr_t(r2), sr_nx(r2), ex_at(sr_t(r2), b), b,
                 (c + 1 : U32), d)
      alloc_if(sr_t(r3), sr_nx(r3),
               T.ELet{n, sr_i(r1), sr_i(r2), sr_i(r3)}, e,
               Bool.not(U32.is_eq(sr_i(r1), ty) && U32.is_eq(sr_i(r2), v)
                        && U32.is_eq(sr_i(r3), b)))
    case 1n+p T.EProj{tn, i, sx}:
      +pf = p
      +r1 = lift(pf, t, nx, ex_at(t, sx), sx, c, d)
      alloc_if(sr_t(r1), sr_nx(r1), T.EProj{tn, i, sr_i(r1)}, e,
               Bool.not(U32.is_eq(sr_i(r1), sx)))
    case 1n+p _:
      keep(t, nx, e)

# --- instantiate ---------------------------------------------------------
# Replace de Bruijn index `j` by the term `v`, and decrement the indices
# above it. `v` is lifted by `j` at the point of use rather than being lifted
# as the recursion descends, which is the standard formulation.
#
# The three-way comparison is matched rather than picked, because Bend is
# strict: a `pick` over three branches would run the lift on every bound
# variable below `j`, not just on the one that needs it.
def inst_bvar(+c: Cmp, +t: R.Tr<T.Ex>, +nx: U32, +i: U32, +e: U32, +j: U32,
              +v: U32) -> SR:
  match c:
    case LT{}:
      keep(t, nx, e)
    case EQ{}:
      lift(256n, t, nx, ex_at(t, v), v, 0, j)
    case GT{}:
      alloc(t, nx, T.EBVar{(i - 1 : U32)})

def inst(+fuel: Nat, +t: R.Tr<T.Ex>, +nx: U32, +x: T.Ex, +e: U32, +j: U32,
         +v: U32) -> SR:
  match fuel x:
    case 0n _:
      keep(t, nx, e)
    case 1n+p T.EBVar{i}:
      inst_bvar(U32.cmp(i, j), t, nx, i, e, j, v)
    case 1n+p T.EApp{f, a}:
      +pf = p
      +r1 = inst(pf, t, nx, ex_at(t, f), f, j, v)
      +r2 = inst(pf, sr_t(r1), sr_nx(r1), ex_at(sr_t(r1), a), a, j, v)
      alloc_if(sr_t(r2), sr_nx(r2), T.EApp{sr_i(r1), sr_i(r2)}, e,
               Bool.not(U32.is_eq(sr_i(r1), f) && U32.is_eq(sr_i(r2), a)))
    case 1n+p T.ELam{n, ty, b, bi}:
      +pf = p
      +r1 = inst(pf, t, nx, ex_at(t, ty), ty, j, v)
      +r2 = inst(pf, sr_t(r1), sr_nx(r1), ex_at(sr_t(r1), b), b,
                 (j + 1 : U32), v)
      alloc_if(sr_t(r2), sr_nx(r2), T.ELam{n, sr_i(r1), sr_i(r2), bi}, e,
               Bool.not(U32.is_eq(sr_i(r1), ty) && U32.is_eq(sr_i(r2), b)))
    case 1n+p T.EAll{n, ty, b, bi}:
      +pf = p
      +r1 = inst(pf, t, nx, ex_at(t, ty), ty, j, v)
      +r2 = inst(pf, sr_t(r1), sr_nx(r1), ex_at(sr_t(r1), b), b,
                 (j + 1 : U32), v)
      alloc_if(sr_t(r2), sr_nx(r2), T.EAll{n, sr_i(r1), sr_i(r2), bi}, e,
               Bool.not(U32.is_eq(sr_i(r1), ty) && U32.is_eq(sr_i(r2), b)))
    case 1n+p T.ELet{n, ty, vv, b}:
      +pf = p
      +r1 = inst(pf, t, nx, ex_at(t, ty), ty, j, v)
      +r2 = inst(pf, sr_t(r1), sr_nx(r1), ex_at(sr_t(r1), vv), vv, j, v)
      +r3 = inst(pf, sr_t(r2), sr_nx(r2), ex_at(sr_t(r2), b), b,
                 (j + 1 : U32), v)
      alloc_if(sr_t(r3), sr_nx(r3),
               T.ELet{n, sr_i(r1), sr_i(r2), sr_i(r3)}, e,
               Bool.not(U32.is_eq(sr_i(r1), ty) && U32.is_eq(sr_i(r2), vv)
                        && U32.is_eq(sr_i(r3), b)))
    case 1n+p T.EProj{tn, i, sx}:
      +pf = p
      +r1 = inst(pf, t, nx, ex_at(t, sx), sx, j, v)
      alloc_if(sr_t(r1), sr_nx(r1), T.EProj{tn, i, sr_i(r1)}, e,
               Bool.not(U32.is_eq(sr_i(r1), sx)))
    case 1n+p _:
      keep(t, nx, e)
