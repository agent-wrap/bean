# Prints one line per declaration:
#   <verdict> <name-index> <kind>
# where verdict is A (accept), R (reject) or D (decline).
#
# `judge` combines every declaration's verdict into one answer, so a single
# declining declaration makes a whole file decline and the arena sees only
# "decline". This runs the same `ck_one` over the same incrementally built
# environment and reports each declaration separately, which is the only way
# to find out *which* declaration a 300-declaration file is stuck on.
#
# tools/why-decline.py groups the output across the corpus.

import Base
import ./scan.bend as S
import ./decode.bend as D
import ./term.bend as T
import ./level.bend as L
import ./store.bend as K
import ./trie.bend as R
import ./subst.bend as U
import ./infer.bend as I
import ./tables.bend as B
import ./recursor.bend as W
import ./check.bend as C

def vshow(+v: C.V) -> String:
  match v:
    case C.VAccept{}:
      "A"
    case C.VReject{}:
      "R"
    case C.VDecline{}:
      "D"

def kshow(+d: K.Dcl) -> String:
  match d:
    case K.DNone{}:
      "none"
    case K.DAxiom{n, lps, t}:
      "axiom"
    case K.DDef{n, lps, t, v}:
      "def"
    case K.DThm{n, lps, t, v}:
      "thm"
    case K.DQuot{n, lps, t}:
      "quot"
    case K.DInd{nms, items}:
      "inductive"
    case _:
      "other"

# The name of a DInd block is the first inductive's name; `dcl_name` has no
# case for it, so it is taken from the block's own name list.
def ind_first(+xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      4294967295
    case Con{head, tail}:
      head

def dname(+d: K.Dcl) -> U32:
  match d:
    case K.DInd{nms, items}:
      ind_first(nms)
    case _:
      K.dcl_name(d)


# --- expression printer --------------------------------------------------
# The instrument this project lacked. Declines were being diagnosed by
# reading de Bruijn arithmetic by eye, twice, wrongly. Printing the term is
# cheaper than arguing about it.
def pick_s(+z: Bool, x: String, y: String) -> String:
  match z:
    case True{}:
      x
    case False{}:
      y

def show_us(xs: List<&2, U32>, acc: String) -> String:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      show_us(tail, acc ++ " " ++ U32.show(head))

# The node arrives as a parameter, never as `U.ex_at(...)` in the scrutinee:
# Bend cannot match a computed value, and a helper that matched it would need
# to call back here, which would be mutual recursion. So the recursive calls
# do the lookup and hand the node down.
def show_ex(+fuel: Nat, +ex: R.Tr<T.Ex>, +x: T.Ex) -> String:
  match fuel x:
    case 0n _:
      "..."
    case 1n+q T.EBad{}:
      "BAD"
    case 1n+q T.EBVar{j}:
      "#" ++ U32.show(j)
    case 1n+q T.ESort{l}:
      "Sort(l" ++ U32.show(l) ++ ")"
    case 1n+q T.EConst{n, us}:
      "C" ++ U32.show(n) ++ "[" ++ show_us(us, "") ++ "]"
    case 1n+q T.EApp{f, a}:
      "(" ++ show_ex(q, ex, U.ex_at(ex, f)) ++ " "
      ++ show_ex(q, ex, U.ex_at(ex, a)) ++ ")"
    case 1n+q T.ELam{n, t, b, bi}:
      "(fun:" ++ show_ex(q, ex, U.ex_at(ex, t)) ++ " => "
      ++ show_ex(q, ex, U.ex_at(ex, b)) ++ ")"
    case 1n+q T.EAll{n, t, b, bi}:
      "(all:" ++ show_ex(q, ex, U.ex_at(ex, t)) ++ " -> "
      ++ show_ex(q, ex, U.ex_at(ex, b)) ++ ")"
    case 1n+q T.ELet{n, t, v, b}:
      "(let " ++ show_ex(q, ex, U.ex_at(ex, v)) ++ " in "
      ++ show_ex(q, ex, U.ex_at(ex, b)) ++ ")"
    case 1n+q T.EProj{tn, j, sx}:
      "proj<" ++ U32.show(tn) ++ "," ++ U32.show(j) ++ ">("
      ++ show_ex(q, ex, U.ex_at(ex, sx)) ++ ")"
    case 1n+q T.ENat{d}:
      "nat"
    case 1n+q T.EStr{d}:
      "str"

def show_atoms(xs: List<&2, L.Atom>, acc: String) -> String:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case L.At{base, off}:
          show_atoms(tail, acc ++ " " ++ U32.show(base) ++ "+"
                           ++ U32.show(off))

def show_ln(+a: L.LN) -> String:
  match a:
    case L.LNun{}:
      "UNKNOWN"
    case L.LNsym{}:
      "SYMBOLIC"
    case L.LNmax{xs}:
      "max{" ++ show_atoms(xs, "") ++ " }"
    case L.LNimax{a2, b2, o}:
      "imax+" ++ U32.show(o) ++ "(?,?)"
    case L.LNmx{xs, y, r}:
      "max{" ++ show_atoms(xs, "") ++ " imax(?,?) }"

def show_tri(+t: L.Tri) -> String:
  match t:
    case L.TYes{}:
      "yes"
    case L.TNo{}:
      "no"
    case L.TUnk{}:
      "unknown"

# For a declaration that declines: print the declared type, and the type
# `infer` computes for its value, side by side. If they differ, the printed
# pair says exactly how.
# The name of the constant at the head of a value: through lambdas, then
# down the application spine. Used to report whether that constant's type is
# registered in the environment at the point the declaration is checked.
def head_const(+fuel: Nat, +ex: R.Tr<T.Ex>, +x: T.Ex) -> U32:
  match fuel x:
    case 0n _:
      4294967295
    case 1n+q T.ELam{n, t, b, bi}:
      head_const(q, ex, U.ex_at(ex, b))
    case 1n+q T.EApp{f, a}:
      head_const(q, ex, U.ex_at(ex, f))
    case 1n+q T.EConst{n, us}:
      n
    case 1n+q _:
      4294967295

# The index of the head node, so `infer` can be run on the `const` itself.
def head_ix(+fuel: Nat, +ex: R.Tr<T.Ex>, +x: T.Ex, +i: U32) -> U32:
  match fuel x:
    case 0n _:
      i
    case 1n+q T.ELam{n, t, b, bi}:
      head_ix(q, ex, U.ex_at(ex, b), b)
    case 1n+q T.EApp{f, a}:
      head_ix(q, ex, U.ex_at(ex, f), f)
    case 1n+q _:
      i

# The universe of the type at index `ti`, the way `ck_typed` computes it:
# infer its type, reduce, and read the level off the resulting Sort.
def univ_of(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
            +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +ti: U32) -> L.LN:
  +wt = I.whd(st, mt, lp, vt, ti)
  +st1 = I.ir_st(wt)
  +ri = I.infer(8192n, st1, mt, nt, lp, vt,
                U.ex_at(I.is_ex(st1), I.ir_ty(wt)), I.ir_ty(wt), Nil{})
  +wk = I.whd(I.ir_st(ri), mt, lp, vt, I.ir_ty(ri))
  +st2 = I.ir_st(wk)
  +kx = U.ex_at(I.is_ex(st2), I.ir_ty(wk))
  L.pick_ln(I.ir_ok(ri) && I.is_sortx(kx),
            R.get(L.LN, 64n, I.is_lnt(st2), I.sort_lvl_of(kx), L.LNun{}),
            L.LNun{})

# `infer` applied to the head `const` of a value, which is where the level
# substitution happens.
def headr(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
          +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +vi: U32) -> I.IR:
  +hi = head_ix(32n, I.is_ex(st), U.ex_at(I.is_ex(st), vi), vi)
  I.infer(8192n, st, mt, nt, lp, vt, U.ex_at(I.is_ex(st), hi), hi, Nil{})

# `infer` on the body of the outermost lambda, in the context that lambda
# introduces. `ELam` answers BAD whenever its body does, so the body's own
# result is the only way to see where an application chain actually breaks.
def bodyr(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
          +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +x: T.Ex) -> I.IR:
  match x:
    case T.ELam{n, t, b, bi}:
      I.infer(8192n, st, mt, nt, lp, vt, U.ex_at(I.is_ex(st), b), b,
              Con{t, Nil{}})
    case _:
      I.IR{st, 4294967295, False{}}

# Deep normal form (delta on), printed. Single self-recursive: the node to
# print arrives already weak-head-reduced as a parameter, and each child is
# whnf'd then recursed, so there is no match-on-computed-value and no mutual
# recursion. Diagnostic only -- used to see whether two constants that `defeq`
# calls "unknown" actually reduce to distinguishable terms.
def nf_show(+fuel: Nat, +st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
            +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +node: T.Ex) -> String:
  match fuel node:
    case 0n _:
      "..."
    case 1n+p T.EApp{f, a}:
      +rs = I.rec_stuck(st, mt, nt, lp, vt, T.EApp{f, a})
      +wf = I.whd(st, mt, lp, vt, f)
      +sf = I.ir_st(wf)
      +wa = I.whd(sf, mt, lp, vt, a)
      +sa = I.ir_st(wa)
      pick_s(rs, "STUCKREC", "") ++ "("
      ++ nf_show(p, sf, mt, nt, lp, vt, U.ex_at(I.is_ex(sf), I.ir_ty(wf)))
      ++ " " ++ nf_show(p, sa, mt, nt, lp, vt, U.ex_at(I.is_ex(sa), I.ir_ty(wa)))
      ++ ")"
    case 1n+p T.ELam{n, t, b, bi}:
      +wb = I.whd(st, mt, lp, vt, b)
      +sb = I.ir_st(wb)
      "(fun => " ++ nf_show(p, sb, mt, nt, lp, vt,
                            U.ex_at(I.is_ex(sb), I.ir_ty(wb))) ++ ")"
    case 1n+p T.EAll{n, t, b, bi}:
      +wb = I.whd(st, mt, lp, vt, b)
      +sb = I.ir_st(wb)
      "(all => " ++ nf_show(p, sb, mt, nt, lp, vt,
                            U.ex_at(I.is_ex(sb), I.ir_ty(wb))) ++ ")"
    case 1n+p T.EProj{tn, j, sx}:
      +ws = I.whd(st, mt, lp, vt, sx)
      +ss = I.ir_st(ws)
      "proj<" ++ U32.show(j) ++ ">(" ++ nf_show(p, ss, mt, nt, lp, vt,
                 U.ex_at(I.is_ex(ss), I.ir_ty(ws))) ++ ")"
    case 1n+p T.EConst{n, us}:
      "C" ++ U32.show(n)
    case 1n+p T.EBVar{j}:
      "#" ++ U32.show(j)
    case 1n+p T.ESort{l}:
      "Sort(l" ++ U32.show(l) ++ ")"
    case 1n+p T.ELet{n, t, v, b}:
      "let"
    case 1n+p T.ENat{d}:
      "nat"
    case 1n+p T.EStr{d}:
      "str"
    case 1n+p T.EBad{}:
      "BAD"

def nf_root(+fuel: Nat, +st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
            +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +i: U32) -> String:
  +w = I.whd(st, mt, lp, vt, i)
  +s1 = I.ir_st(w)
  nf_show(fuel, s1, mt, nt, lp, vt, U.ex_at(I.is_ex(s1), I.ir_ty(w)))

def show_cmp(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
             +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +d: K.Dcl) -> String:
  +ti = K.dcl_type(d)
  +vi = K.dcl_value(d)
  +ri = I.infer(8192n, st, mt, nt, lp, vt, U.ex_at(I.is_ex(st), vi), vi, Nil{})
  +st2 = I.ir_st(ri)
  "\n    declared: " ++ show_ex(14n, I.is_ex(st2), U.ex_at(I.is_ex(st2), ti))
  ++ "\n    value:    " ++ show_ex(14n, I.is_ex(st2), U.ex_at(I.is_ex(st2), vi))
  ++ "\n    inferred: " ++ show_ex(14n, I.is_ex(st2), U.ex_at(I.is_ex(st2), I.ir_ty(ri)))
  ++ "\n    nf(declared): " ++ nf_root(12n, st2, mt, nt, lp, vt, ti)
  ++ "\n    nf(inferred): " ++ nf_root(12n, st2, mt, nt, lp, vt, I.ir_ty(ri))
  ++ "\n    infer-ok: " ++ pick_s(I.ir_ok(ri), "yes", "no")
  # The universe of the DECLARED type, and whether it is a Prop: the theorem
  # rule and the Sort comparison both hinge on these two answers.
  ++ "\n    univ(ty): " ++ show_ln(univ_of(st, mt, nt, lp, vt, ti))
  ++ "  is-prop: " ++ show_tri(L.ln_is_zero(univ_of(st, mt, nt, lp, vt, ti)))
  # When the type is a Pi, the two halves of its `imax` separately, so a
  # SYMBOLIC answer can be attributed to one side or the other.
  # What `ck_infer` actually concludes: reduce both sides and compare.
  ++ "\n    defeq(inferred, declared): "
  ++ show_tri(I.dr_r(I.defeq(64n,
                U32.is_eq(I.ir_ty(ri), ti),
                I.ir_st(I.whd(I.ir_st(I.whd(st2, mt, lp, vt,
                                            I.ir_ty(ri))),
                              mt, lp, vt, ti)),
                mt, nt, lp, vt, Nil{},
                U.ex_at(I.is_ex(st2), I.ir_ty(I.whd(st2, mt, lp, vt,
                                                    I.ir_ty(ri)))),
                U.ex_at(I.is_ex(st2), I.ir_ty(I.whd(st2, mt, lp, vt,
                                                    ti))))))
  # The two halves of `ck_one`'s non-inductive branch, separately.
  ++ "\n    self-ref: " ++ vshow(C.self_ref_v(I.is_ex(st), d))
  ++ "  ck-typed: "
  ++ vshow(C.ck_typed(8192n, st, mt, nt, lp, vt, K.dcl_is_theorem(d),
                      K.dcl_type(d), K.dcl_value(d)))
  ++ "  ck-value: "
  ++ vshow(C.ck_value(8192n, st, mt, nt, lp, vt, K.dcl_type(d),
                      K.dcl_value(d)))
  ++ "\n    head-const: "
  ++ U32.show(head_const(32n, I.is_ex(st2),
                         U.ex_at(I.is_ex(st2), vi)))
  ++ "  its type-ix: "
  ++ U32.show(R.get(U32, 64n, nt,
                    head_const(32n, I.is_ex(st2),
                               U.ex_at(I.is_ex(st2), vi)), 4294967295))
  # The head constant's type as declared, and the type `infer` gives its
  # `const` node (which applies the level substitution). If the second is BAD
  # while the first is a Pi, the level substitution is what failed.
  ++ "\n    head-ty:  "
  ++ show_ex(10n, I.is_ex(st2),
             U.ex_at(I.is_ex(st2),
                     R.get(U32, 64n, nt,
                           head_const(32n, I.is_ex(st2),
                                      U.ex_at(I.is_ex(st2), vi)),
                           4294967295)))
  ++ "\n    head-inferred: "
  ++ show_ex(10n, I.is_ex(I.ir_st(headr(st2, mt, nt, lp, vt, vi))),
             U.ex_at(I.is_ex(I.ir_st(headr(st2, mt, nt, lp, vt, vi))),
                     I.ir_ty(headr(st2, mt, nt, lp, vt, vi))))
  ++ "  ok: "
  ++ pick_s(I.ir_ok(headr(st2, mt, nt, lp, vt, vi)), "yes", "no")
  ++ "\n    lam-body-inferred: "
  ++ show_ex(12n,
             I.is_ex(I.ir_st(bodyr(st2, mt, nt, lp, vt,
                                   U.ex_at(I.is_ex(st2), vi)))),
             U.ex_at(I.is_ex(I.ir_st(bodyr(st2, mt, nt, lp, vt,
                                           U.ex_at(I.is_ex(st2), vi)))),
                     I.ir_ty(bodyr(st2, mt, nt, lp, vt,
                                   U.ex_at(I.is_ex(st2), vi)))))
  ++ "  ok: "
  ++ pick_s(I.ir_ok(bodyr(st2, mt, nt, lp, vt,
                          U.ex_at(I.is_ex(st2), vi))), "yes", "no")
  ++ "\n    univ(dom): "
  ++ show_ln(univ_of(st, mt, nt, lp, vt,
                     I.all_dom(U.ex_at(I.is_ex(st), ti))))
  ++ "  univ(cod): "
  ++ show_ln(univ_of(st, mt, nt, lp, vt,
                     I.all_cod(U.ex_at(I.is_ex(st), ti))))

# For a declining inductive block: the five sub-checks of `ck_one`'s DInd
# branch, reported separately. The block's verdict is their conjunction, so
# this says which one is undecided.
# The three inputs to the large-elimination decision, which is what
# `rec-count` and `derived` both hinge on.
# Per-field: the universe `sl` computes for the field's type, and whether
# the index exception applies. `fields_prop` is a conjunction, so one
# unknown field hides the rest.
def show_fields(doms: List<&2, U32>, +ex: R.Tr<T.Ex>, +ln: R.Tr<L.LN>,
                +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +nskip: U32,
                +i: U32, +ctx: List<&2, U32>, +idxs: List<&2, U32>,
                +nf: U32, +acc: String) -> String:
  match doms:
    case Nil{}:
      acc
    case Con{head, tail}:
      +pi = i
      +ph = head
      +isidx = U32.is_ge(pi, nskip) && U32.is_gt(nf, 0)
               && C.occurs_in_any(idxs, ex,
                                  (nf - 1 - (pi - nskip : U32) : U32))
      show_fields(tail, ex, ln, nt, lp, nskip, (pi + 1 : U32),
                  Con{ph, ctx}, idxs, nf,
                  acc ++ "\n      field " ++ U32.show(pi) ++ ": univ="
                  ++ show_ln(I.sl(256n, ex, ln, nt, lp, U.ex_at(ex, ph),
                                  ctx))
                  ++ "  is-index=" ++ pick_s(isidx, "yes", "no")
                  ++ "  param=" ++ pick_s(U32.is_lt(pi, nskip), "yes", "no"))

def show_ctor_fields(items: List<&2, K.IItem>, +ind: U32, +ex: R.Tr<T.Ex>,
                     +ln: R.Tr<L.LN>, +nt: R.Tr<U32>,
                     +lp: R.Tr<List<&2, U32>>, +acc: String) -> String:
  match items:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case K.ICtor{nm, lps, ty, ind2, np, nf, ci}:
          +pnp = np
          +pty = ty
          +pnf = nf
          show_ctor_fields(tail, ind, ex, ln, nt, lp,
            acc ++ pick_s(U32.is_eq(ind2, ind),
              show_fields(D.rev_u32(C.tele_doms(256n, ex,
                                               U.ex_at(ex, pty), Nil{}),
                                    Nil{}),
                          ex, ln, nt, lp, pnp, 0, Nil{},
                          I.skip_u(I.spine_ar(256n, ex,
                                              C.tele_res(256n, ex,
                                                U.ex_at(ex, pty)), Nil{}),
                                   pnp),
                          pnf, ""), ""))
        case _:
          show_ctor_fields(tail, ind, ex, ln, nt, lp, acc)

# The recursor type this checker DERIVES, beside the one the export
# DECLARES. `cmp_derived` compares them and declines when it cannot tell, so
# seeing both is the only way to find out which part disagrees.
def show_derived(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
                 +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
                 +ind: K.IItem, +items: List<&2, K.IItem>) -> String:
  match ind:
    case K.IInd{nm, lps, ty, np, ni, nn, cs}:
      +pnm = nm
      +its = items
      +ex = I.is_ex(st)
      +rc = C.rec_of(its, K.IOther{})
      +theirs = C.rec_ty_of(rc)
      +nc = C.count_ctors(its, pnm, 0)
      +ul = W.param_lvls(lps, st, Nil{})
      +us = D.rev_u32(I.ls_xs(ul), Nil{})
      +mn = C.build_minors(U32.to_nat(nc), 1, its, pnm, us, np, ni, ex,
                           I.ls_st(ul), mt, lp, vt, Nil{})
      +d = W.derive_gen(I.ls_st(mn), pnm, us, np, ni, nc,
                        D.rev_u32(C.tele_doms(256n, ex, U.ex_at(ex, ty),
                                              Nil{}), Nil{}),
                        I.ls_xs(mn), C.head_u(C.rec_lps_of(rc), 0))
      "\n    DERIVED:  "
      ++ show_ex(18n, I.is_ex(I.ir_st(d)),
                 U.ex_at(I.is_ex(I.ir_st(d)), I.ir_ty(d)))
      ++ "\n    DECLARED: "
      ++ show_ex(18n, I.is_ex(I.ir_st(d)),
                 U.ex_at(I.is_ex(I.ir_st(d)), theirs))
    case _:
      ""

def show_le(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
            +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
            +ind: K.IItem, +items: List<&2, K.IItem>) -> String:
  match ind:
    case K.IInd{nm, lps, ty, np, ni, nn, cs}:
      +pnm = nm
      +its = items
      +res = C.tele_res(256n, I.is_ex(st), U.ex_at(I.is_ex(st), ty))
      +isprop = L.pick_tri(I.is_sortx(res),
                           L.ln_is_zero(R.get(L.LN, 64n, I.is_lnt(st),
                                              I.sort_lvl_of(res),
                                              L.LNun{})),
                           L.TUnk{})
      +nc = C.count_ctors(its, pnm, 0)
      +fp = C.ctor_fields_prop(its, pnm, I.is_ex(st), I.is_lnt(st),
                               B.add_items_nt(its, nt), lp,
                               L.TYes{})
      "\n    isprop: " ++ show_tri(isprop) ++ "  nctors: " ++ U32.show(nc)
      ++ "  fields-prop: " ++ show_tri(fp)
      ++ "  large-elim: " ++ show_tri(C.large_elim(isprop, nc, fp))
      ++ "  nested: " ++ U32.show(nn)
      ++ show_ctor_fields(its, pnm, I.is_ex(st), I.is_lnt(st),
                          B.add_items_nt(its, nt), lp, "")
      ++ show_derived(st, mt, nt, lp, vt,
                      K.IInd{pnm, lps, ty, np, ni, nn, cs}, its)
    case _:
      ""

def show_ind(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
             +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +nmt: R.Tr<T.Nm>,
             +items: List<&2, K.IItem>) -> String:
  +its = items
  "\n    telescope: "
  ++ vshow(C.ind_items(its, I.is_ex(st), nt, vt, C.VAccept{}))
  ++ "  ctors: "
  ++ vshow(C.ctor_all(its, I.is_ex(st), C.ind_names_of(its, Nil{}),
                      C.VAccept{}))
  ++ "  rec-count: "
  ++ vshow(C.block_rec_v(its, I.is_ex(st), I.is_lnt(st), B.add_items_nt(its, nt), lp))
  ++ "  derived: "
  ++ vshow(C.block_derive_v(its, st, mt, vt, I.is_lnt(st), B.add_items_nt(its, nt), lp))
  ++ "  names: "
  ++ vshow(C.block_names_v(its, nmt))
  ++ show_le(st, mt, nt, lp, vt,
             C.head_item(C.ind_only(its, Nil{})), its)

def maybe_cmp(+show: Bool, +v: C.V, +st: I.IS, +mt: R.Tr<I.Meta>,
              +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
              +nmt: R.Tr<T.Nm>, +d: K.Dcl) -> String:
  match show:
    case False{}:
      ""
    case True{}:
      match v:
        case C.VDecline{}:
          match d:
            case K.DInd{nms, items}:
              show_ind(st, mt, nt, lp, vt, nmt, items)
            case K.DNone{}:
              ""
            case _:
              show_cmp(st, mt, nt, lp, vt, d)
        case _:
          ""

# Mirrors `C.ck_all` exactly -- same environment threading, same fuel -- but
# emits a line per declaration instead of folding the verdicts together.
def walk(ds: List<&2, K.Dcl>, +fuel: Nat, +st: I.IS,
         +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
         +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +nmt: R.Tr<T.Nm>,
         +verbose: Bool, +acc: String) -> String:
  match ds:
    case Nil{}:
      acc
    case Con{head, tail}:
      +h = head
      +vd = C.ck_one(fuel, st, mt, nt, lp, vt, nmt, h)
      +line = vshow(vd) ++ " " ++ U32.show(dname(h)) ++ " " ++ kshow(h)
              ++ maybe_cmp(verbose, vd, st, mt, nt, lp, vt, nmt, h) ++ "\n"
      walk(tail, fuel, st, mt, B.add_nt(h, nt), B.add_lp(h, lp),
           B.add_vt(h, vt), nmt, verbose, acc ++ line)

def report(+bs: List<&2, U32>, +verbose: Bool) -> String:
  +recs = D.decode(bs, S.Sc.start(), D.Acc.start(), Nil{})
  +nlv = U32.to_nat((K.max_lvl_ix(recs, 0) + 1 : U32))
  +nx = (K.max_any_ix(recs, 0) + 1 : U32)
  +ds = K.decls_of(recs, Nil{})
  +ex = B.build_ex(recs, R.TNil{})
  +ln = B.lv_resolve(32n, nlv, B.build_lv(recs, R.TNil{}), R.TNil{})
  +st : I.IS = I.IS{ex, nx, ln, nx, R.TNil{}, K.build_ht(recs, R.TNil{}),
                    K.find_name(recs, [78, 97, 116], 4294967295),
                    K.find_name(recs,
                                [83, 116, 114, 105, 110, 103], 4294967295),
                    K.build_wk2(recs, R.TNil{})}
  walk(ds, 8192n, st, C.build_meta(ds, ex, ln, R.TNil{}), R.TNil{},
       R.TNil{}, R.TNil{}, K.build_nm(recs, R.TNil{}), verbose, "")

# Verbose mode is "a second argument was given at all" -- Bend's Base has no
# String equality, and the flag's value does not matter.
def has_arg(m: Maybe<&1, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{value}:
      True{}

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

def show_read(pr: File & Result<&1, &1, U32 & String, List<&2, U32>>,
              +verbose: Bool) -> IO(Unit):
  match pr:
    case Tuple{f, r}:
      do IO<Unit>:
        bs : List<&2, U32> <- IO.pass(List<&2, U32>, r)
        IO.print(report(bs, verbose))

# `av` is affine, so the path and the verbose flag are taken in one pass
# rather than with two `List.get` calls.
def arg_pair(av: List<&1, String>) -> String & Bool:
  match av:
    case Nil{}:
      Tuple{"", False{}}
    case Con{head, tail}:
      match tail:
        case Nil{}:
          Tuple{"", False{}}
        case Con{head2, tail2}:
          match tail2:
            case Nil{}:
              Tuple{head2, False{}}
            case Con{head3, tail3}:
              Tuple{head2, True{}}

def go(ab: String & Bool) -> IO(Unit):
  match ab:
    case Tuple{path, verbose}:
      do IO<Unit>:
        oh : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
        f : File <- open_or_fail(oh)
        pr : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 33554432)
        show_read(pr, verbose)

def main() -> IO(Unit):
  do IO<Unit>:
    av : List<&1, String> <- IO.args()
    go(arg_pair(av))
