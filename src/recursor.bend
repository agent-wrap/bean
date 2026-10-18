# Deriving a recursor's type.
#
# The export supplies recursor types, and the format spec says so explicitly:
# that data is "redundant and would likely be ignored or only validated by a
# full external checker". Trusting it is unsound -- `bugs/rec-k-lie`,
# `bugs/nat-rec-k-lie` and `bugs/rec-missing-ih` are exports that lie about a
# recursor and then prove `False` with it. So the type is derived here and the
# export's claim is compared against it.
#
# This covers the base case: no parameters, no indices, and constructors with
# no fields -- enumerations like `Bool`, `PUnit` and `Empty`. For
#
#     I : Sort u        c_1 .. c_n : I
#
# the recursor is
#
#     I.rec : forall (motive : I -> Sort v) (m_1 .. m_n) (t : I), motive t
#
# with `m_j : motive c_j`. In de Bruijn the motive sits at index j-1 inside
# `m_j`'s type and at n+1 in the result, so the minors are built from the
# inside out with j counting down.

import Base
import ./scan.bend as S
import ./term.bend as T
import ./level.bend as L
import ./trie.bend as R
import ./subst.bend as U
import ./decode.bend as D
import ./infer.bend as I

# A level whose normal form is the single parameter atom for `nm`, matching
# how `T.LParam` is normalised elsewhere.
def param_lvl(+st: I.IS, +nm: U32) -> I.IR:
  I.alloc_lvl(st, L.LNmax{[L.At{(nm + 1 : U32), 0}]})

# The motive's universe. A recursor that eliminates into any sort takes an
# extra level PARAMETER for it; one that eliminates only into `Prop` does
# not, and its motive goes to `Sort 0`. The sentinel name says which.
#
# Without this, the derivation ran only for inductives that DO have large
# elimination, so every Prop-valued inductive that legitimately eliminates
# into Prop alone was never checked against the recursor the kernel would
# derive -- it just declined.
def motive_lvl(+st: I.IS, +nm: U32) -> I.IR:
  I.pick_ir(U32.is_eq(nm, 4294967295), I.alloc_lvl(st, L.ln_zero()),
            param_lvl(st, nm))

def param_lvls(ns: List<&2, U32>, +st: I.IS,
               acc: List<&2, U32>) -> I.LS:
  match ns:
    case Nil{}:
      I.LS{st, acc}
    case Con{head, tail}:
      +rl = param_lvl(st, head)
      param_lvls(tail, I.ir_st(rl), Con{I.ir_ty(rl), acc})

# `motive c_j` for the j-th minor premise, with the motive at index j-1.
def minor_type(+st: I.IS, +j: U32, +cj: U32) -> I.IR:
  +mv = I.alloc_ex(st, T.EBVar{(j - 1 : U32)})
  I.alloc_ex(I.ir_st(mv), T.EApp{I.ir_ty(mv), cj})

# Wrap the minors outward: the list arrives innermost-first, so `j` counts
# down and the last one wrapped is the first premise.
def wrap_minors(cs: List<&2, U32>, +st: I.IS, +j: U32,
                +inner: U32) -> I.IR:
  match cs:
    case Nil{}:
      I.IR{st, inner, True{}}
    case Con{head, tail}:
      +mt = minor_type(st, j, head)
      +al = I.alloc_ex(I.ir_st(mt), T.EAll{0, I.ir_ty(mt), inner, 0})
      wrap_minors(tail, I.ir_st(al), (j - 1 : U32), I.ir_ty(al))

# forall (t : I), motive t     -- motive is at n+1 once t is bound
def rec_core(+st: I.IS, +ic: U32, +n: U32) -> I.IR:
  +mv = I.alloc_ex(st, T.EBVar{(n + 1 : U32)})
  +tv = I.alloc_ex(I.ir_st(mv), T.EBVar{0})
  +ap = I.alloc_ex(I.ir_st(tv), T.EApp{I.ir_ty(mv), I.ir_ty(tv)})
  I.alloc_ex(I.ir_st(ap), T.EAll{0, ic, I.ir_ty(ap), 0})

# forall (_ : I), Sort v
def motive_type(+st: I.IS, +ic: U32, +vnm: U32) -> I.IR:
  +vl = motive_lvl(st, vnm)
  +so = I.alloc_ex(I.ir_st(vl), T.ESort{I.ir_ty(vl)})
  I.alloc_ex(I.ir_st(so), T.EAll{0, ic, I.ir_ty(so), 0})

# The whole type. `cs` is the constructor constants innermost-first, `n` their
# count, `ic` the inductive as a constant, `vnm` the motive universe's name.
def derive(+st: I.IS, +ic: U32, +cs: List<&2, U32>, +n: U32,
           +vnm: U32) -> I.IR:
  +core = rec_core(st, ic, n)
  +mins = wrap_minors(cs, I.ir_st(core), n, I.ir_ty(core))
  +mt = motive_type(I.ir_st(mins), ic, vnm)
  I.alloc_ex(I.ir_st(mt), T.EAll{0, I.ir_ty(mt), I.ir_ty(mins), 0})

# --- the general case: parameters, indices, non-recursive fields ---------
# For
#     I   : forall (a_1..a_p) (i_1..i_k), Sort u
#     c_j : forall (a_1..a_p) (f_1..f_m), I a-bar e-bar
# the recursor is
#     I.rec : forall (a_1..a_p)
#               (motive : forall (i_1..i_k) (t : I a-bar i-bar), Sort v)
#               (minor_1 .. minor_n)
#               (i_1..i_k) (t : I a-bar i-bar),
#               motive i-bar t
# with  minor_j : forall (f_1'..f_m'), motive e-bar' (c_j a-bar f-bar).
#
# The de Bruijn bookkeeping, all of it, with the binder sequence
# [a_1..a_p] [motive] [minor_1..minor_n] [i_1..i_k] [t]:
#
#   A_h               verbatim from I's telescope -- same context.
#   B_l (in motive)   verbatim -- also the same context.
#   I a-bar i-bar     a_h = bvar(k+p-h),  i_l = bvar(k-l).
#   F_h'              lift(F_h, h-1, j): the fields keep their relative
#                     indices, the parameters moved j further away because the
#                     motive and j-1 earlier minors now sit between them.
#   e_l'              lift(e_l, m, j), for the same reason.
#   c_j a-bar f-bar   a_h = bvar(m+j+p-h),  f_h = bvar(m-h).
#   motive in minor_j bvar(m+j-1).
#   B_l' (after)      lift(B_l, l-1, 1+n).
#   t's type          a_h = bvar(k+n+1+p-h),  i_l = bvar(k-l).
#   motive i-bar t    motive = bvar(k+n+1), i_l = bvar(k-l+1), t = bvar 0.
#
# Checked against the base case p=k=m=0, which these reduce to exactly: the
# motive lands at bvar(j-1) in minor_j and bvar(n+1) in the result, which is
# what the already-working base derivation uses.
#
# Recursive fields need an inductive hypothesis per field, whose own telescope
# shifts two ranges of indices by different amounts; that is not implemented
# and declines.

# [top, top-1, ..., top-n+1]
def args_desc(n: Nat, +top: U32, +i: U32,
              acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      args_desc(p, top, (i + 1 : U32), Con{(top - i : U32), acc})

def bvar_nodes(idxs: List<&2, U32>, +st: I.IS,
               acc: List<&2, U32>) -> I.LS:
  match idxs:
    case Nil{}:
      I.LS{st, acc}
    case Con{head, tail}:
      +b = I.alloc_ex(st, T.EBVar{head})
      bvar_nodes(tail, I.ir_st(b), Con{I.ir_ty(b), acc})

# forall T1 .. Tm, inner    (ts in order)
def wrap_alls(ts: List<&2, U32>, +st: I.IS, +inner: U32) -> I.IR:
  match ts:
    case Nil{}:
      I.IR{st, inner, True{}}
    case Con{head, tail}:
      +r = wrap_alls(tail, st, inner)
      I.alloc_ex(I.ir_st(r), T.EAll{0, head, I.ir_ty(r), 0})

# head a1 a2 ..   (args in order)
def apply_spine(args: List<&2, U32>, +st: I.IS, +head: U32) -> I.IR:
  match args:
    case Nil{}:
      I.IR{st, head, True{}}
    case Con{head2, tail}:
      +r = I.alloc_ex(st, T.EApp{head, head2})
      apply_spine(tail, I.ir_st(r), I.ir_ty(r))

# Lift a list of expressions, each with its own cutoff: cutoff = base + its
# position, which is what the field and index types need.
def lift_each(xs: List<&2, U32>, +st: I.IS, +base: U32, +amt: U32,
              +i: U32, acc: List<&2, U32>) -> I.LS:
  match xs:
    case Nil{}:
      I.LS{st, acc}
    case Con{head, tail}:
      +ph = head
      +r = U.lift(256n, I.is_ex(st), I.is_nx(st),
                  U.ex_at(I.is_ex(st), ph), ph, (base + i : U32), amt)
      +s2 : I.IS = I.IS{U.sr_t(r), U.sr_nx(r), I.is_lnt(st),
                        I.is_nlx(st), I.is_wm(st), I.is_ht(st),
                        I.is_natn(st), I.is_strn(st), I.is_qt_t(st)}
      lift_each(tail, s2, base, amt, (i + 1 : U32),
                Con{U.sr_i(r), acc})

# All of them lifted at one cutoff.
def lift_all(xs: List<&2, U32>, +st: I.IS, +cut: U32, +amt: U32,
             acc: List<&2, U32>) -> I.LS:
  match xs:
    case Nil{}:
      I.LS{st, acc}
    case Con{head, tail}:
      +ph = head
      +r = U.lift(256n, I.is_ex(st), I.is_nx(st),
                  U.ex_at(I.is_ex(st), ph), ph, cut, amt)
      +s2 : I.IS = I.IS{U.sr_t(r), U.sr_nx(r), I.is_lnt(st),
                        I.is_nlx(st), I.is_wm(st), I.is_ht(st),
                        I.is_natn(st), I.is_strn(st), I.is_qt_t(st)}
      lift_all(tail, s2, cut, amt, Con{U.sr_i(r), acc})

def take_last(xs: List<&2, U32>, +n: U32, +len: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{head, tail}:
      +pt = tail
      S.pick_l(U32.is_gt(len, n), take_last(pt, n, (len - 1 : U32)),
               Con{head, pt})

def list_len_u(xs: List<&2, U32>, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      list_len_u(tail, (acc + 1 : U32))

def take_first(xs: List<&2, U32>, +n: U32,
               +acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      D.rev_u32(acc, Nil{})
    case Con{head, tail}:
      S.pick_l(U32.is_eq(n, 0), D.rev_u32(acc, Nil{}),
               take_first(tail, (n - 1 : U32), Con{head, acc}))

def desc(+n: U32, +top: U32) -> List<&2, U32>:
  D.rev_u32(args_desc(U32.to_nat(n), top, 0, Nil{}), Nil{})

# `I a-bar i-bar`, with the parameters starting at de Bruijn index `abase`.
def ind_app(+st: I.IS, +nm: U32, +us: List<&2, U32>, +p: U32, +k: U32,
            +abase: U32) -> I.IR:
  +bn = bvar_nodes(List.append(&2, U32, desc(p, (abase + p - 1 : U32)),
                               desc(k, (k - 1 : U32))),
                   st, Nil{})
  +ic = I.alloc_ex(I.ls_st(bn), T.EConst{nm, us})
  apply_spine(D.rev_u32(I.ls_xs(bn), Nil{}), I.ir_st(ic), I.ir_ty(ic))

# forall (i_1..i_k) (t : I a-bar i-bar), Sort v
def motive_ty(+st: I.IS, +nm: U32, +us: List<&2, U32>, +p: U32, +k: U32,
              +bs: List<&2, U32>, +vnm: U32) -> I.IR:
  +ia = ind_app(st, nm, us, p, k, k)
  +vl = motive_lvl(I.ir_st(ia), vnm)
  +so = I.alloc_ex(I.ir_st(vl), T.ESort{I.ir_ty(vl)})
  +tb = I.alloc_ex(I.ir_st(so), T.EAll{0, I.ir_ty(ia), I.ir_ty(so), 0})
  wrap_alls(bs, I.ir_st(tb), I.ir_ty(tb))

# forall (f_1'..f_m'), motive e-bar' (c_j a-bar f-bar)
def minor_ty(+st: I.IS, +cnm: U32, +us: List<&2, U32>, +p: U32, +k: U32,
             +m: U32, +j: U32, +cdoms: List<&2, U32>,
             +cargs: List<&2, U32>) -> I.IR:
  +fl = lift_each(take_last(cdoms, m, list_len_u(cdoms, 0)), st, 0, j, 0,
                  Nil{})
  +el = lift_all(take_last(cargs, k, list_len_u(cargs, 0)),
                 I.ls_st(fl), m, j, Nil{})
  +bn = bvar_nodes(List.append(&2, U32,
                               desc(p, (m + j + p - 1 : U32)),
                               desc(m, (m - 1 : U32))),
                   I.ls_st(el), Nil{})
  +cc = I.alloc_ex(I.ls_st(bn), T.EConst{cnm, us})
  +capp = apply_spine(D.rev_u32(I.ls_xs(bn), Nil{}), I.ir_st(cc),
                      I.ir_ty(cc))
  +mv = I.alloc_ex(I.ir_st(capp), T.EBVar{(m + j - 1 : U32)})
  +body = apply_spine(List.append(&2, U32,
                                  D.rev_u32(I.ls_xs(el), Nil{}),
                                  [I.ir_ty(capp)]),
                      I.ir_st(mv), I.ir_ty(mv))
  wrap_alls(D.rev_u32(I.ls_xs(fl), Nil{}), I.ir_st(body), I.ir_ty(body))

# forall (i_1..i_k) (t : I a-bar i-bar), motive i-bar t
def rec_tail(+st: I.IS, +nm: U32, +us: List<&2, U32>, +p: U32, +k: U32,
             +n: U32, +bs: List<&2, U32>) -> I.IR:
  +bl = lift_each(bs, st, 0, (1 + n : U32), 0, Nil{})
  +ta = ind_app(I.ls_st(bl), nm, us, p, k, (k + n + 1 : U32))
  +mv = I.alloc_ex(I.ir_st(ta), T.EBVar{(k + n + 1 : U32)})
  +bn = bvar_nodes(desc((k + 1 : U32), k), I.ir_st(mv), Nil{})
  +res = apply_spine(D.rev_u32(I.ls_xs(bn), Nil{}), I.ls_st(bn),
                     I.ir_ty(mv))
  +tb = I.alloc_ex(I.ir_st(res), T.EAll{0, I.ir_ty(ta), I.ir_ty(res), 0})
  wrap_alls(D.rev_u32(I.ls_xs(bl), Nil{}), I.ir_st(tb), I.ir_ty(tb))

# The whole recursor type. `minors` are the already-built minor premise types,
# in order; `idoms` is the inductive's telescope domains [A_1..A_p, B_1..B_k].
def derive_gen(+st: I.IS, +nm: U32, +us: List<&2, U32>, +p: U32, +k: U32,
               +n: U32, +idoms: List<&2, U32>, +minors: List<&2, U32>,
               +vnm: U32) -> I.IR:
  +bs = take_last(idoms, k, list_len_u(idoms, 0))
  +mt = motive_ty(st, nm, us, p, k, bs, vnm)
  +tl = rec_tail(I.ir_st(mt), nm, us, p, k, n, bs)
  +mn = wrap_alls(minors, I.ir_st(tl), I.ir_ty(tl))
  +mb = I.alloc_ex(I.ir_st(mn), T.EAll{0, I.ir_ty(mt), I.ir_ty(mn), 0})
  wrap_alls(take_first(idoms, p, Nil{}), I.ir_st(mb), I.ir_ty(mb))
