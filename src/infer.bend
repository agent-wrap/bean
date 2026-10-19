# Type inference.
#
# The shape here is forced by Bend and by one observation. A match cannot
# scrutinise a computed value, so after normalising a function's type there
# is no way to *match* on whether the answer is a Pi. But accessor defs can:
# `is_all`, `all_dom`, `all_cod` each match their own parameter and do not
# recurse, so they are not mutual recursion. Together with a `Data` result
# record -- which can be bound locally and taken apart by accessors -- that
# is enough to write inference as one ordinary self-recursive function.
#
# Inferred types are new terms, so this grows both the expression trie and
# the level-normal-form trie. New indices start above everything the export
# used, so the exporter's numbering and its sharing stay intact.

import Base
import ./scan.bend as S
import ./term.bend as T
import ./level.bend as L
import ./trie.bend as R
import ./subst.bend as U

# What whnf needs to know about a name to perform iota: whether it is a
# recursor (and its arities), or a constructor (and which of its fields are
# recursive, so the inductive hypotheses can be rebuilt).
type Meta is Data:
  MNone{}
  MRec{p: U32, k: U32, n: U32, ind: U32}
  MCtor{ci: U32, p: U32, nf: U32, ind: U32, recs: List<&2, U32>}
  # A structure: one constructor, no indices. `cty` is that constructor's
  # type, which is where the field types come from for projection typing.
  # `ppx` bounds projections out of a PROP structure: a projection is
  # allowed only at an index strictly below it. See the note at the
  # projection rule in `infer`.
  MInd{p: U32, nf: U32, cty: U32, pr: U32, ppx: U32}

def meta_is_rec(+m: Meta) -> Bool:
  match m:
    case MRec{p, k, n, ind}:
      True{}
    case _:
      False{}

def meta_is_ctor(+m: Meta) -> Bool:
  match m:
    case MCtor{ci, p, nf, ind, recs}:
      True{}
    case _:
      False{}

def meta_p(+m: Meta) -> U32:
  match m:
    case MRec{p, k, n, ind}:
      p
    case MCtor{ci, p, nf, ind, recs}:
      p
    case MInd{p, nf, cty, pr, ppx}:
      p
    case _:
      0

def meta_is_ind(+m: Meta) -> Bool:
  match m:
    case MInd{p, nf, cty, pr, ppx}:
      True{}
    case _:
      False{}

def meta_nf(+m: Meta) -> U32:
  match m:
    case MCtor{ci, p, nf, ind, recs}:
      nf
    case MInd{p, nf, cty, pr, ppx}:
      nf
    case _:
      0

# 0 means the structure's universe is provably not Prop. Projection typing
# is restricted to those: `tutorial/089_projProp1` and `091_projProp3`
# project from a Prop-valued structure and were being wrongly rejected, and
# Lean's rules for projecting out of a Prop are more delicate than the
# plain field-type substitution used here.
def meta_pr(+m: Meta) -> U32:
  match m:
    case MInd{p, nf, cty, pr, ppx}:
      pr
    case _:
      1

def meta_ppx(+m: Meta) -> U32:
  match m:
    case MInd{p, nf, cty, pr, ppx}:
      ppx
    case _:
      0

def meta_cty(+m: Meta) -> U32:
  match m:
    case MInd{p, nf, cty, pr, ppx}:
      cty
    case _:
      4294967295

def meta_k(+m: Meta) -> U32:
  match m:
    case MRec{p, k, n, ind}:
      k
    case _:
      0

def meta_n(+m: Meta) -> U32:
  match m:
    case MRec{p, k, n, ind}:
      n
    case _:
      0

def meta_ind(+m: Meta) -> U32:
  match m:
    case MRec{p, k, n, ind}:
      ind
    case MCtor{ci, p, nf, ind, recs}:
      ind
    case _:
      0

def meta_ci(+m: Meta) -> U32:
  match m:
    case MCtor{ci, p, nf, ind, recs}:
      ci
    case _:
      0

def meta_recs(+m: Meta) -> List<&2, U32>:
  match m:
    case MCtor{ci, p, nf, ind, recs}:
      recs
    case _:
      Nil{}

# `ht` is the reducibility-height table, read-only. It rides in the state
# rather than being threaded as a parameter because the state already reaches
# every function that needs it -- `whnf` for the delta decision and `defeq`
# for the order of it -- and adding a parameter would touch forty signatures.
# `natn` and `strn` are the export's name indices for `Nat` and `String`,
# needed to give a literal a type. They are 4294967295 when the file never
# names them, in which case a literal cannot be typed and declines.
type IS is Data:
  IS{ex: R.Tr<T.Ex>, nx: U32, lnt: R.Tr<L.LN>, nlx: U32,
     wm: R.Tr<U32>, ht: R.Tr<U32>, natn: U32, strn: U32,
     qt: R.Tr<U32>}

type IR is Data:
  IR{st: IS, ty: U32, ok: Bool}

def is_ex(+s: IS) -> R.Tr<T.Ex>:
  match s:
    case IS{ex, nx, lnt, nlx, wm, ht, natn, strn, qt}:
      ex

def is_nx(+s: IS) -> U32:
  match s:
    case IS{ex, nx, lnt, nlx, wm, ht, natn, strn, qt}:
      nx

def is_lnt(+s: IS) -> R.Tr<L.LN>:
  match s:
    case IS{ex, nx, lnt, nlx, wm, ht, natn, strn, qt}:
      lnt

def is_nlx(+s: IS) -> U32:
  match s:
    case IS{ex, nx, lnt, nlx, wm, ht, natn, strn, qt}:
      nlx

# Memo for weak head normalisation, keyed by expression index. Terms are
# immutable once built, so an entry never needs invalidating.
def is_wm(+s: IS) -> R.Tr<U32>:
  match s:
    case IS{ex, nx, lnt, nlx, wm, ht, natn, strn, qt}:
      wm

def is_ht(+s: IS) -> R.Tr<U32>:
  match s:
    case IS{ex, nx, lnt, nlx, wm, ht, natn, strn, qt}:
      ht

def is_natn(+s: IS) -> U32:
  match s:
    case IS{ex, nx, lnt, nlx, wm, ht, natn, strn, qt}:
      natn

def is_strn(+s: IS) -> U32:
  match s:
    case IS{ex, nx, lnt, nlx, wm, ht, natn, strn, qt}:
      strn

def is_qt_t(+s: IS) -> R.Tr<U32>:
  match s:
    case IS{ex, nx, lnt, nlx, wm, ht, natn, strn, qt}:
      qt

# The quotient names: 0 = `Quot.lift`, 1 = `Quot.ind`, 2 = `Quot.mk`.
def is_qt(+s: IS, +i: U32) -> U32:
  R.get(U32, 32n, is_qt_t(s), i, 4294967295)

def ir_st(+r: IR) -> IS:
  match r:
    case IR{st, ty, ok}:
      st

def ir_ty(+r: IR) -> U32:
  match r:
    case IR{st, ty, ok}:
      ty

def ir_ok(+r: IR) -> Bool:
  match r:
    case IR{st, ty, ok}:
      ok

def ir_bad(+s: IS) -> IR:
  IR{s, 4294967295, False{}}

def is_sortx(+x: T.Ex) -> Bool:
  match x:
    case T.ESort{l}:
      True{}
    case _:
      False{}

def sort_lvl_of(+x: T.Ex) -> U32:
  match x:
    case T.ESort{l}:
      l
    case _:
      4294967295

def nth_u(xs: List<&2, U32>, +i: U32, +dflt: U32) -> U32:
  match xs:
    case Nil{}:
      dflt
    case Con{head, tail}:
      S.pick(U32.is_eq(i, 0), head, nth_u(tail, (i - 1 : U32), dflt))

def drop_u(xs: List<&2, U32>, +i: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{head, tail}:
      +pt = tail
      S.pick_l(U32.is_eq(i, 0), pt, drop_u(pt, (i - 1 : U32)))

def lns_of(us: List<&2, U32>, +ln: R.Tr<L.LN>) -> List<&2, L.LN>:
  match us:
    case Nil{}:
      Nil{}
    case Con{head, tail}:
      Con{R.get(L.LN, 32n, ln, head, L.LNun{}), lns_of(tail, ln)}

# A bound variable's type is its context entry; its universe is that entry's
# level when the entry is a Sort. Anything else needs reduction.
def sl_bvar(+ex: R.Tr<T.Ex>, +ln: R.Tr<L.LN>, +ctx: List<&2, U32>,
            +i: U32) -> L.LN:
  +tx = R.get(T.Ex, 64n, ex, nth_u(ctx, i, 4294967295), T.EBad{})
  L.pick_ln(is_sortx(tx),
            R.get(L.LN, 32n, ln, sort_lvl_of(tx), L.LNun{}), L.LNun{})

# A constant's type is the declared type of the name, read under the level
# substitution the `const` carries.
def sl_const(+ex: R.Tr<T.Ex>, +ln: R.Tr<L.LN>, +nt: R.Tr<U32>,
             +lp: R.Tr<List<&2, U32>>, +n: U32,
             +us: List<&2, U32>) -> L.LN:
  +tx = R.get(T.Ex, 64n, ex, R.get(U32, 32n, nt, n, 4294967295), T.EBad{})
  L.pick_ln(is_sortx(tx),
            L.ln_subst(R.get(L.LN, 32n, ln, sort_lvl_of(tx), L.LNun{}),
                       R.get(List<&2, U32>, 32n, lp, n, Nil{}),
                       lns_of(us, ln)),
            L.LNun{})

# --- the universe of an application -------------------------------------
# `sl` had no rule for applications, and that one gap decided several
# questions wrongly by declining them. A constructor field's type routinely
# ends in an application of the inductive itself -- `Acc`'s field is
# `forall y, r y x -> Acc r y` -- so "is every field a proposition", and
# through it large elimination and the recursor's universe count, came back
# "cannot decide" for every such inductive.
#
# A level never depends on a term argument, only on level arguments, so the
# universe of `C a_1 .. a_n` is the level of the Sort that `C`'s declared
# type ends in once `n` binders are peeled, under the `const`'s own level
# substitution. These helpers sit above `sl` because `sl` may not call the
# ones further down the file, and they must not call `sl` either -- that
# would be mutual recursion.
def sl_spine_hd(+fuel: Nat, +ex: R.Tr<T.Ex>, +x: T.Ex) -> T.Ex:
  match fuel x:
    case 0n _:
      T.EBad{}
    case 1n+p T.EApp{f, a}:
      sl_spine_hd(p, ex, R.get(T.Ex, 64n, ex, f, T.EBad{}))
    case 1n+p y:
      y

def sl_nargs(+fuel: Nat, +ex: R.Tr<T.Ex>, +x: T.Ex, +acc: U32) -> U32:
  match fuel x:
    case 0n _:
      acc
    case 1n+p T.EApp{f, a}:
      sl_nargs(p, ex, R.get(T.Ex, 64n, ex, f, T.EBad{}), (acc + 1 : U32))
    case 1n+p _:
      acc

def sl_tele_after(n: Nat, +ex: R.Tr<T.Ex>, +x: T.Ex) -> T.Ex:
  match n x:
    case 0n y:
      y
    case 1n+q T.EAll{nm, t, b, bi}:
      sl_tele_after(q, ex, R.get(T.Ex, 64n, ex, b, T.EBad{}))
    case 1n+q _:
      T.EBad{}

def sl_const_nm(+x: T.Ex) -> U32:
  match x:
    case T.EConst{n, us}:
      n
    case _:
      4294967295

def sl_const_us(+x: T.Ex) -> List<&2, U32>:
  match x:
    case T.EConst{n, us}:
      us
    case _:
      Nil{}

# The head of an application may be a BOUND VARIABLE, not just a constant.
# `Acc.intro`'s second field has type `forall y, r y x -> Acc r y`, where `r`
# is a binder of the constructor's own telescope. Reading only constant heads
# left `r y x` with an unknown universe, which made "is every field a
# proposition" undecidable and declined `Acc` -- the very inductive the index
# exception above was added for.
#
# A bound variable's type comes from the context. It is NOT lifted here:
# lifting shifts de Bruijn indices and a level is unaffected by that, and
# only the level of the telescope's final Sort is read.
def sl_head_ty(+hd: T.Ex, +nt: R.Tr<U32>, +ctx: List<&2, U32>) -> U32:
  match hd:
    case T.EConst{n, us}:
      R.get(U32, 32n, nt, n, 4294967295)
    case T.EBVar{i}:
      nth_u(ctx, i, 4294967295)
    case _:
      4294967295

def sl_app(+ex: R.Tr<T.Ex>, +ln: R.Tr<L.LN>, +nt: R.Tr<U32>,
           +lp: R.Tr<List<&2, U32>>, +ctx: List<&2, U32>,
           +x: T.Ex) -> L.LN:
  +hd = sl_spine_hd(256n, ex, x)
  +nm = sl_const_nm(hd)
  +ti = sl_head_ty(hd, nt, ctx)
  +res = sl_tele_after(U32.to_nat(sl_nargs(256n, ex, x, 0)), ex,
                       R.get(T.Ex, 64n, ex, ti, T.EBad{}))
  L.pick_ln(Bool.not(U32.is_eq(ti, 4294967295)) && is_sortx(res),
            L.ln_subst(R.get(L.LN, 32n, ln, sort_lvl_of(res), L.LNun{}),
                       R.get(List<&2, U32>, 32n, lp, nm, Nil{}),
                       lns_of(sl_const_us(hd), ln)),
            L.LNun{})

def sl(fuel: Nat, +ex: R.Tr<T.Ex>, +ln: R.Tr<L.LN>, +nt: R.Tr<U32>,
       +lp: R.Tr<List<&2, U32>>, +x: T.Ex, +ctx: List<&2, U32>) -> L.LN:
  match fuel x:
    case 0n _:
      L.LNun{}
    case 1n+p T.ESort{l}:
      L.ln_succ(R.get(L.LN, 32n, ln, l, L.LNun{}))
    case 1n+p T.EAll{n, t, b, bi}:
      +pt = t
      +pf = p
      L.ln_imax(
        sl(pf, ex, ln, nt, lp, R.get(T.Ex, 64n, ex, pt, T.EBad{}), ctx),
        sl(pf, ex, ln, nt, lp, R.get(T.Ex, 64n, ex, b, T.EBad{}),
           Con{pt, ctx}))
    case 1n+p T.EBVar{i}:
      sl_bvar(ex, ln, ctx, i)
    case 1n+p T.EConst{n, us}:
      sl_const(ex, ln, nt, lp, n, us)
    case 1n+p T.EApp{f, a}:
      sl_app(ex, ln, nt, lp, ctx, T.EApp{f, a})
    case 1n+p _:
      L.LNun{}

# Definitely not a type. A lambda's type is a Pi and a literal's is `Nat` or
# `String`, so neither is a Sort however far it is reduced; and a Pi is
# already in normal form, so a constant whose declared type is a Pi is a
# function, not a type.
#
# `sl` cannot express this: it answers a universe or "unknown", and unknown
# declines. Dropping this test lost `tutorial/010_nonTypeType` and
# `011_nonTypeAxiom`, whose declared type is `constType : Type -> Type ->
# Type`. Knowing a thing is *not* a type is a separate question from knowing
# which universe it lives in.
def head_not_sort(+x: T.Ex) -> Bool:
  match x:
    case T.EAll{n, t, b, bi}:
      True{}
    case T.ELam{n, t, b, bi}:
      True{}
    case T.ENat{d}:
      True{}
    case T.EStr{d}:
      True{}
    case _:
      False{}

def not_a_type(+ex: R.Tr<T.Ex>, +nt: R.Tr<U32>, +x: T.Ex) -> Bool:
  match x:
    case T.ELam{n, t, b, bi}:
      True{}
    case T.ENat{d}:
      True{}
    case T.EStr{d}:
      True{}
    case T.EConst{n, us}:
      head_not_sort(R.get(T.Ex, 64n, ex,
                          R.get(U32, 32n, nt, n, 4294967295), T.EBad{}))
    case _:
      False{}

def is_un_ln(+a: L.LN) -> Bool:
  match a:
    case L.LNun{}:
      True{}
    case _:
      False{}

# "Is this expression a type?" -- now answered by whether it has a universe,
# rather than by a shallow syntactic test.
def type_tri(+nat: Bool, +u: L.LN) -> L.Tri:
  match nat:
    case True{}:
      L.TNo{}
    case False{}:
      L.pick_tri(is_un_ln(u), L.TUnk{}, L.TYes{})


# --- bidirectional checking ---------------------------------------------
# Checking a value against a declared type, rather than inferring a type and
# comparing. For a lambda against a Pi this needs no substitution at all:
# both descend one binder together, so their de Bruijn indices stay aligned
# and the body can be checked against the codomain directly. Only `app`
# needs instantiation, and that is not here yet.
#
# `eq_ex` answers TYes or TUnk and never TNo: two structurally different
# expressions may still be definitionally equal, so "not syntactically equal"
# is not evidence of anything.
def tri_and(+a: L.Tri, +b: L.Tri) -> L.Tri:
  match a b:
    case L.TNo{} _:
      L.TNo{}
    case _ L.TNo{}:
      L.TNo{}
    case L.TUnk{} _:
      L.TUnk{}
    case _ L.TUnk{}:
      L.TUnk{}
    case _ _:
      L.TYes{}

def eq_lvls(us: List<&2, U32>, vs: List<&2, U32>, +ln: R.Tr<L.LN>) -> L.Tri:
  match us vs:
    case Nil{} Nil{}:
      L.TYes{}
    case Con{a, as} Con{b, bs}:
      tri_and(L.ln_cmp(R.get(L.LN, 32n, ln, a, L.LNun{}),
                       R.get(L.LN, 32n, ln, b, L.LNun{})),
              eq_lvls(as, bs, ln))
    case _ _:
      L.TUnk{}

# One self-recursive function, not three: `eq_ex -> eq_node -> eq_struct ->
# eq_ex` is mutual recursion and Bend forbids it. The two nodes therefore
# arrive as parameters, and the recursive calls fetch the children in their
# own argument positions. `same` short-circuits identical indices, which
# matters because the export is a DAG with heavy sharing.
def eq_ex(+fuel: Nat, +same: Bool, +ex: R.Tr<T.Ex>, +ln: R.Tr<L.LN>,
          +x: T.Ex, +y: T.Ex) -> L.Tri:
  match fuel same x y:
    case 0n _ _ _:
      L.TUnk{}
    case 1n+p True{} _ _:
      L.TYes{}
    case 1n+p False{} T.ESort{a} T.ESort{b}:
      L.ln_cmp(R.get(L.LN, 32n, ln, a, L.LNun{}),
               R.get(L.LN, 32n, ln, b, L.LNun{}))
    case 1n+p False{} T.EBVar{a} T.EBVar{b}:
      L.pick_tri(U32.is_eq(a, b), L.TYes{}, L.TUnk{})
    case 1n+p False{} T.EConst{a, us} T.EConst{b, vs}:
      L.pick_tri(U32.is_eq(a, b), eq_lvls(us, vs, ln), L.TUnk{})
    case 1n+p False{} T.EApp{f1, a1} T.EApp{f2, a2}:
      +pf = p
      tri_and(eq_ex(pf, U32.is_eq(f1, f2), ex, ln,
                    R.get(T.Ex, 64n, ex, f1, T.EBad{}),
                    R.get(T.Ex, 64n, ex, f2, T.EBad{})),
              eq_ex(pf, U32.is_eq(a1, a2), ex, ln,
                    R.get(T.Ex, 64n, ex, a1, T.EBad{}),
                    R.get(T.Ex, 64n, ex, a2, T.EBad{})))
    case 1n+p False{} T.EAll{n1, t1, b1, i1} T.EAll{n2, t2, b2, i2}:
      +pf = p
      tri_and(eq_ex(pf, U32.is_eq(t1, t2), ex, ln,
                    R.get(T.Ex, 64n, ex, t1, T.EBad{}),
                    R.get(T.Ex, 64n, ex, t2, T.EBad{})),
              eq_ex(pf, U32.is_eq(b1, b2), ex, ln,
                    R.get(T.Ex, 64n, ex, b1, T.EBad{}),
                    R.get(T.Ex, 64n, ex, b2, T.EBad{})))
    case 1n+p False{} T.ELam{n1, t1, b1, i1} T.ELam{n2, t2, b2, i2}:
      +pf = p
      tri_and(eq_ex(pf, U32.is_eq(t1, t2), ex, ln,
                    R.get(T.Ex, 64n, ex, t1, T.EBad{}),
                    R.get(T.Ex, 64n, ex, t2, T.EBad{})),
              eq_ex(pf, U32.is_eq(b1, b2), ex, ln,
                    R.get(T.Ex, 64n, ex, b1, T.EBad{}),
                    R.get(T.Ex, 64n, ex, b2, T.EBad{})))
    case 1n+p False{} _ _:
      L.TUnk{}

# --- accessors used instead of matching a computed node -----------------
def is_all(+x: T.Ex) -> Bool:
  match x:
    case T.EAll{n, t, b, bi}:
      True{}
    case _:
      False{}

def all_name(+x: T.Ex) -> U32:
  match x:
    case T.EAll{n, t, b, bi}:
      n
    case _:
      0

def all_dom(+x: T.Ex) -> U32:
  match x:
    case T.EAll{n, t, b, bi}:
      t
    case _:
      4294967295

def all_cod(+x: T.Ex) -> U32:
  match x:
    case T.EAll{n, t, b, bi}:
      b
    case _:
      4294967295

def all_bi(+x: T.Ex) -> U32:
  match x:
    case T.EAll{n, t, b, bi}:
      bi
    case _:
      0

# --- allocation ----------------------------------------------------------
# A level is allocated by its normal form alone: every comparison goes
# through the normal form, so the raw `Level` tree is never needed for a
# level this checker builds itself.
def alloc_lvl(+s: IS, +u: L.LN) -> IR:
  match s:
    case IS{ex, nx, lnt, nlx, wm, ht, natn, strn, qt}:
      IR{IS{ex, nx, R.set(L.LN, 32n, lnt, nlx, u, L.LNun{}),
            (nlx + 1 : U32), wm, ht, natn, strn, qt}, nlx, True{}}

def alloc_ex(+s: IS, +x: T.Ex) -> IR:
  match s:
    case IS{ex, nx, lnt, nlx, wm, ht, natn, strn, qt}:
      IR{IS{R.set(T.Ex, 64n, ex, nx, x, T.EBad{}), (nx + 1 : U32), lnt,
            nlx, wm, ht, natn, strn, qt}, nx, True{}}

# `Sort u` for a universe given as a normal form.
def alloc_sort(+s: IS, +u: L.LN) -> IR:
  +rl = alloc_lvl(s, u)
  alloc_ex(ir_st(rl), T.ESort{ir_ty(rl)})

def pick_ir(+z: Bool, +x: IR, +y: IR) -> IR:
  match z:
    case True{}:
      x
    case False{}:
      y

def sort_of(+s: IS, +u: L.LN) -> IR:
  pick_ir(L.is_un(u), ir_bad(s), alloc_sort(s, u))

# --- universe substitution inside a term --------------------------------
# A polymorphic constant's type is its declared type with the declaration's
# universe parameters replaced by the constant's universe arguments. Without
# this, every `const` carrying levels is uninferable -- and those are
# everywhere, so it is the difference between checking the monomorphic
# fragment and checking real code.
#
# Levels are rebuilt by normal form alone: a fresh level index is allocated
# and its normal form recorded, because every comparison goes through the
# normal form and the raw `Level` tree is never consulted for a level this
# checker builds.
type LS is Data:
  LS{st: IS, xs: List<&2, U32>}

def ls_st(+r: LS) -> IS:
  match r:
    case LS{st, xs}:
      st

def ls_xs(+r: LS) -> List<&2, U32>:
  match r:
    case LS{st, xs}:
      xs

def lsub_lvls(us: List<&2, U32>, +st: IS, +ps: List<&2, U32>,
              +qs: List<&2, L.LN>) -> LS:
  match us:
    case Nil{}:
      LS{st, Nil{}}
    case Con{head, tail}:
      +rl = alloc_lvl(st, L.ln_subst(R.get(L.LN, 32n, is_lnt(st), head,
                                           L.LNun{}), ps, qs))
      +rest = lsub_lvls(tail, ir_st(rl), ps, qs)
      LS{ls_st(rest), Con{ir_ty(rl), ls_xs(rest)}}

def keep_ir(+st: IS, +e: U32) -> IR:
  IR{st, e, True{}}

def lsubst(+fuel: Nat, +st: IS, +x: T.Ex, +e: U32, +ps: List<&2, U32>,
           +qs: List<&2, L.LN>) -> IR:
  match fuel x:
    case 0n _:
      keep_ir(st, e)
    case 1n+p T.ESort{l}:
      +old = R.get(L.LN, 32n, is_lnt(st), l, L.LNun{})
      +u = L.ln_subst(old, ps, qs)
      pick_ir(L.tri_is_yes(L.ln_cmp(old, u)), keep_ir(st, e),
              alloc_sort(st, u))
    case 1n+p T.EConst{n, us}:
      +rl = lsub_lvls(us, st, ps, qs)
      alloc_ex(ls_st(rl), T.EConst{n, ls_xs(rl)})
    case 1n+p T.EApp{f, a}:
      +pf = p
      +r1 = lsubst(pf, st, U.ex_at(is_ex(st), f), f, ps, qs)
      +r2 = lsubst(pf, ir_st(r1), U.ex_at(is_ex(ir_st(r1)), a), a, ps, qs)
      pick_ir(U32.is_eq(ir_ty(r1), f) && U32.is_eq(ir_ty(r2), a),
              keep_ir(ir_st(r2), e),
              alloc_ex(ir_st(r2), T.EApp{ir_ty(r1), ir_ty(r2)}))
    case 1n+p T.ELam{n, ty, b, bi}:
      +pf = p
      +r1 = lsubst(pf, st, U.ex_at(is_ex(st), ty), ty, ps, qs)
      +r2 = lsubst(pf, ir_st(r1), U.ex_at(is_ex(ir_st(r1)), b), b, ps, qs)
      pick_ir(U32.is_eq(ir_ty(r1), ty) && U32.is_eq(ir_ty(r2), b),
              keep_ir(ir_st(r2), e),
              alloc_ex(ir_st(r2), T.ELam{n, ir_ty(r1), ir_ty(r2), bi}))
    case 1n+p T.EAll{n, ty, b, bi}:
      +pf = p
      +r1 = lsubst(pf, st, U.ex_at(is_ex(st), ty), ty, ps, qs)
      +r2 = lsubst(pf, ir_st(r1), U.ex_at(is_ex(ir_st(r1)), b), b, ps, qs)
      pick_ir(U32.is_eq(ir_ty(r1), ty) && U32.is_eq(ir_ty(r2), b),
              keep_ir(ir_st(r2), e),
              alloc_ex(ir_st(r2), T.EAll{n, ir_ty(r1), ir_ty(r2), bi}))
    case 1n+p T.ELet{n, ty, v, b}:
      +pf = p
      +r1 = lsubst(pf, st, U.ex_at(is_ex(st), ty), ty, ps, qs)
      +r2 = lsubst(pf, ir_st(r1), U.ex_at(is_ex(ir_st(r1)), v), v, ps, qs)
      +r3 = lsubst(pf, ir_st(r2), U.ex_at(is_ex(ir_st(r2)), b), b, ps, qs)
      pick_ir(U32.is_eq(ir_ty(r1), ty) && U32.is_eq(ir_ty(r2), v)
              && U32.is_eq(ir_ty(r3), b),
              keep_ir(ir_st(r3), e),
              alloc_ex(ir_st(r3),
                       T.ELet{n, ir_ty(r1), ir_ty(r2), ir_ty(r3)}))
    case 1n+p T.EProj{tn, i, sx}:
      +pf = p
      +r1 = lsubst(pf, st, U.ex_at(is_ex(st), sx), sx, ps, qs)
      pick_ir(U32.is_eq(ir_ty(r1), sx), keep_ir(ir_st(r1), e),
              alloc_ex(ir_st(r1), T.EProj{tn, i, ir_ty(r1)}))
    case 1n+p _:
      keep_ir(st, e)

# --- iota helpers -------------------------------------------------------
def app_args(args: List<&2, U32>, +st: IS, +head: U32) -> IR:
  match args:
    case Nil{}:
      IR{st, head, True{}}
    case Con{a, rest}:
      +r = alloc_ex(st, T.EApp{head, a})
      app_args(rest, ir_st(r), ir_ty(r))

def rev_u(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      rev_u(tail, Con{head, acc})

def take_u(xs: List<&2, U32>, +n: U32, +acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      rev_u(acc, Nil{})
    case Con{head, tail}:
      S.pick_l(U32.is_eq(n, 0), rev_u(acc, Nil{}),
               take_u(tail, (n - 1 : U32), Con{head, acc}))

def skip_u(xs: List<&2, U32>, +n: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{head, tail}:
      +pt = tail
      S.pick_l(U32.is_eq(n, 0), Con{head, pt}, skip_u(pt, (n - 1 : U32)))

def len_u(xs: List<&2, U32>, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      len_u(tail, (acc + 1 : U32))

# One inductive hypothesis argument per recursive field: the recursor applied
# to the same parameters, motive and minor premises, then that field.
def build_ihs(poss: List<&2, U32>, +st: IS, +recnm: U32,
              +us: List<&2, U32>, +pre: List<&2, U32>,
              +fields: List<&2, U32>, acc: List<&2, U32>) -> LS:
  match poss:
    case Nil{}:
      LS{st, rev_u(acc, Nil{})}
    case Con{head, tail}:
      +rc = alloc_ex(st, T.EConst{recnm, us})
      +ap = app_args(List.append(&2, U32, pre,
                                 [nth_u(fields, (head - 1 : U32),
                                        4294967295)]),
                     ir_st(rc), ir_ty(rc))
      build_ihs(tail, ir_st(ap), recnm, us, pre, fields,
                Con{ir_ty(ap), acc})

def spine_hd(+fuel: Nat, +ex: R.Tr<T.Ex>, +x: T.Ex) -> T.Ex:
  match fuel x:
    case 0n _:
      T.EBad{}
    case 1n+p T.EApp{f, a}:
      spine_hd(p, ex, U.ex_at(ex, f))
    case 1n+p y:
      y

def spine_ar(+fuel: Nat, +ex: R.Tr<T.Ex>, +x: T.Ex,
             acc: List<&2, U32>) -> List<&2, U32>:
  match fuel x:
    case 0n _:
      acc
    case 1n+p T.EApp{f, a}:
      spine_ar(p, ex, U.ex_at(ex, f), Con{a, acc})
    case 1n+p _:
      acc

def const_nm2(+x: T.Ex) -> U32:
  match x:
    case T.EConst{n, us}:
      n
    case _:
      0

# The iota reduct, or the delta unfolding, chosen by `match` so that only
# the one that applies is built.
#
# Bend is strict, so writing both and selecting with `pick_ir` built the
# recursor reduct -- `build_ihs` and `app_args`, both of which allocate -- on
# every single constant in the file, recursor or not, and `unfold_const` on
# every recursor application. Constants are the commonest node there is, so
# that was the dominant cost of reduction.
# --- weak head normal form ----------------------------------------------
# Beta, zeta and delta, as ONE self-recursive function. Instead of
# normalising a function and then asking whether the answer was a lambda --
# which needs a helper that calls back -- arguments are pushed onto a spine
# and a lambda consumes one directly.
#
# Delta now unfolds POLYMORPHIC constants too, by substituting the universe
# arguments into the value with `lsubst`. Without that, every definition with
# a universe parameter stayed stuck, and those are everywhere:
# `tutorial/018_levelParams` declares its type as `levelParamF.{1} Prop ...`,
# which never reduced.
def list_empty(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{head, tail}:
      False{}

# `args` comes first because the termination checker reads arguments left to
# right and requires every one before the shrinking argument to be unchanged.
def rebuild(args: List<&2, U32>, +st: IS, +h: U32) -> IR:
  match args:
    case Nil{}:
      IR{st, h, True{}}
    case Con{a, rest}:
      +r = alloc_ex(st, T.EApp{h, a})
      rebuild(rest, ir_st(r), ir_ty(r))

def unfold_const(+st: IS, +lp: R.Tr<List<&2, U32>>, +n: U32, +vi: U32,
                 +us: List<&2, U32>) -> IR:
  lsubst(256n, st, U.ex_at(is_ex(st), vi), vi,
         R.get(List<&2, U32>, 32n, lp, n, Nil{}), lns_of(us, is_lnt(st)))

def iota_tgt(+ok2: Bool, +can: Bool, +st: IS, +lp: R.Tr<List<&2, U32>>,
             +n: U32, +us: List<&2, U32>, +vi: U32,
             +recs: List<&2, U32>, +args: List<&2, U32>,
             +need: U32, +fields: List<&2, U32>, +ci: U32,
             +pp: U32) -> IR:
  match ok2:
    case True{}:
      +ihs = build_ihs(recs, st, n, us, take_u(args, need, Nil{}), fields,
                       Nil{})
      app_args(List.append(&2, U32, fields, ls_xs(ihs)), ls_st(ihs),
               nth_u(args, (pp + 1 + ci : U32), 4294967295))
    case False{}:
      pick_ir(can, unfold_const(st, lp, n, vi, us),
              IR{st, 4294967295, True{}})

# Quotient reduction.
#
#   Quot.lift a r b f h (Quot.mk a r v)  ~>  f v
#   Quot.ind  a r b f   (Quot.mk a r v)  ~>  f v
#
# Both are "apply the function argument to the value inside the `mk`", and
# both are recognised by NAME: the quotient package is built into the kernel
# rather than declared as an inductive, so there is no `Meta` entry to match
# on and no recursor to derive. `Quot.lift` takes its major premise sixth and
# `Quot.ind` fifth; the function is the fourth of either, and `Quot.mk` holds
# the value third.
#
# A `match`, so nothing is built unless the rule fires.
def quot_tgt(+ok: Bool, +st: IS, +f: U32, +v: U32) -> IR:
  match ok:
    case False{}:
      IR{st, 4294967295, False{}}
    case True{}:
      alloc_ex(st, T.EApp{f, v})

# --- literal arithmetic --------------------------------------------------
# Lean's kernel computes `Nat.add`, `Nat.sub` and the comparisons DIRECTLY on
# literals rather than through the recursor, and it has to: `other/nat-lit-add`
# is 123456789 + 987654321, so unary reduction is not a slow path, it is an
# impossibility. These do the same on the decimal digits the exporter wrote.
#
# Digits are ASCII, most significant first. Each operation reverses, works
# least-significant-first with a carry or borrow, and conses -- which yields
# most-significant-first again.
def dec_add_r(fuel: Nat, xs: List<&2, U32>, ys: List<&2, U32>, +c: U32,
              acc: List<&2, U32>) -> List<&2, U32>:
  match fuel xs ys:
    case 0n _ _:
      acc
    case 1n+p Nil{} Nil{}:
      +pa2 = acc
      S.pick_l(U32.is_eq(c, 0), pa2, Con{(c + 48 : U32), pa2})
    case 1n+p Con{a, ta} Nil{}:
      +sm = (a - 48 + c : U32)
      dec_add_r(p, ta, Nil{}, S.pick(U32.is_lt(sm, 10), 0, 1),
                Con{((sm % 10 : U32) + 48 : U32), acc})
    case 1n+p Nil{} Con{b, tb}:
      +sm = (b - 48 + c : U32)
      dec_add_r(p, Nil{}, tb, S.pick(U32.is_lt(sm, 10), 0, 1),
                Con{((sm % 10 : U32) + 48 : U32), acc})
    case 1n+p Con{a, ta} Con{b, tb}:
      +sm = (a - 48 + (b - 48 : U32) + c : U32)
      dec_add_r(p, ta, tb, S.pick(U32.is_lt(sm, 10), 0, 1),
                Con{((sm % 10 : U32) + 48 : U32), acc})

def dec_add(+a: List<&2, U32>, +b: List<&2, U32>) -> List<&2, U32>:
  dec_add_r(256n, rev_u(a, Nil{}), rev_u(b, Nil{}), 0, Nil{})

# `a - b`, least-significant-first, with a borrow. Only called when b <= a.
def dec_sub_r(fuel: Nat, xs: List<&2, U32>, ys: List<&2, U32>, +bo: U32,
              acc: List<&2, U32>) -> List<&2, U32>:
  match fuel xs ys:
    case 0n _ _:
      acc
    case 1n+p Nil{} _:
      acc
    case 1n+p Con{a, ta} Nil{}:
      +dv = (a - 48 : U32)
      dec_sub_r(p, ta, Nil{}, S.pick(U32.is_lt(dv, bo), 1, 0),
                Con{(((dv + 10 - bo : U32) % 10 : U32) + 48 : U32), acc})
    case 1n+p Con{a, ta} Con{b, tb}:
      +dv = (a - 48 : U32)
      +sb = (b - 48 + bo : U32)
      dec_sub_r(p, ta, tb, S.pick(U32.is_lt(dv, sb), 1, 0),
                Con{(((dv + 10 - sb : U32) % 10 : U32) + 48 : U32), acc})

def dec_strip(fuel: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match fuel xs:
    case 0n _:
      xs
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{head, tail}:
      +ph = head
      +pt = tail
      S.pick_l(U32.is_eq(ph, 48), dec_strip(p, pt), Con{ph, pt})

# `a <= b` on most-significant-first digits: shorter wins, else first
# differing digit decides.
def dec_lex(fuel: Nat, xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match fuel xs ys:
    case 0n _ _:
      True{}
    case 1n+p Nil{} _:
      True{}
    case 1n+p Con{a, ta} Con{b, tb}:
      +pa = a
      +pb = b
      S.pick_b(U32.is_eq(pa, pb), dec_lex(p, ta, tb), U32.is_lt(pa, pb))
    case 1n+p _ _:
      False{}

def dec_le(+a: List<&2, U32>, +b: List<&2, U32>) -> Bool:
  +sa = dec_strip(256n, a)
  +sb = dec_strip(256n, b)
  +la = len_u(sa, 0)
  +lb = len_u(sb, 0)
  U32.is_lt(la, lb) || (U32.is_eq(la, lb) && dec_lex(256n, sa, sb))

def dec_sub(+a: List<&2, U32>, +b: List<&2, U32>) -> List<&2, U32>:
  S.pick_l(dec_le(b, a),
           dec_sub_r(256n, rev_u(a, Nil{}), rev_u(b, Nil{}), 0, Nil{}),
           [48])

# --- literals against numerals -------------------------------------------
# `ENat 3` and `Nat.succ (Nat.succ (Nat.succ Nat.zero))` are the same number
# written two ways, and `defeq` has to see that: `103_natLitEq` states
# exactly that equality. The literal is expanded ONE step at a time --
# `ENat 0` to `Nat.zero`, `ENat n` to `Nat.succ (ENat (n-1))` -- so the
# comparison proceeds structurally and the recursion fuel bounds the depth.
#
# The digits are the ASCII bytes the exporter wrote, most significant first,
# so the decrement is decimal with a borrow. Leading zeros are left in place:
# nothing reads these as text, and `dec_is_zero` tolerates them.
def dec_is_zero(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{head, tail}:
      U32.is_eq(head, 48) && dec_is_zero(tail)

# `xs` least-significant-first; consing while walking yields
# most-significant-first again.
def dec_sub1(xs: List<&2, U32>, +bor: Bool,
             acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      +ph = head
      dec_sub1(tail, bor && U32.is_eq(ph, 48),
               Con{S.pick(bor, S.pick(U32.is_eq(ph, 48), 57,
                                      (ph - 1 : U32)), ph), acc})

def nat_succ_of(+st: IS, +sn: U32, +d: List<&2, U32>) -> IR:
  +sc = alloc_ex(st, T.EConst{sn, Nil{}})
  +lt = alloc_ex(ir_st(sc), T.ENat{d})
  alloc_ex(ir_st(lt), T.EApp{ir_ty(sc), ir_ty(lt)})

def nat_expand(+st: IS, +d: List<&2, U32>, +zn: U32, +sn: U32) -> IR:
  +pd = d
  pick_ir(dec_is_zero(pd), alloc_ex(st, T.EConst{zn, Nil{}}),
          nat_succ_of(st, sn,
                      dec_sub1(rev_u(pd, Nil{}), True{}, Nil{})))

# The three literal operations, computed directly. Each needs both arguments
# already reduced to literals; `ok` says so, and a `match` keeps the digits
# work out of every other constant's path.
def lit_op(+which: U32, +st: IS, +a: List<&2, U32>, +b: List<&2, U32>,
           +tn: U32, +fn2: U32) -> IR:
  match which:
    case 0:
      alloc_ex(st, T.ENat{dec_add(a, b)})
    case 1:
      alloc_ex(st, T.ENat{dec_sub(a, b)})
    case _:
      alloc_ex(st, T.EConst{S.pick(dec_le(a, b), tn, fn2), Nil{}})

def lit_arith(+ok: Bool, +which: U32, +st: IS, +a: List<&2, U32>,
              +b: List<&2, U32>, +tn: U32, +fn2: U32) -> IR:
  match ok:
    case False{}:
      IR{st, 4294967295, False{}}
    case True{}:
      lit_op(which, st, a, b, tn, fn2)

def nat_digits(+x: T.Ex) -> List<&2, U32>:
  match x:
    case T.ENat{d}:
      d
    case _:
      Nil{}

def is_nat_lit(+x: T.Ex) -> Bool:
  match x:
    case T.ENat{d}:
      True{}
    case _:
      False{}

# A recursor's major premise may be a LITERAL where the constructor form is
# needed: `Nat.add` is defined by `Nat.rec`, and `Nat.add 2 3` has `3` as a
# literal, which matches no constructor. Expanding it one step -- `ENat 0` to
# `Nat.zero`, `ENat n` to `Nat.succ (ENat (n-1))` -- lets iota fire, and the
# recursive call expands the next step, so the whole reduction proceeds.
#
# Only for `Nat`: the inductive the recursor eliminates must be the one the
# literal belongs to.
def lit_major(+ok: Bool, +st: IS, +d: List<&2, U32>, +orig: U32,
              +zn: U32, +sn: U32) -> IR:
  match ok:
    case False{}:
      IR{st, orig, True{}}
    case True{}:
      nat_expand(st, d, zn, sn)

def whnf(+fuel: Nat, +delta: Bool, +st: IS, +mt: R.Tr<Meta>,
         +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +x: T.Ex, +e: U32,
         +args: List<&2, U32>) -> IR:
  match fuel x args:
    case 0n _ _:
      rebuild(args, st, e)
    case 1n+p T.EApp{f, a} _:
      whnf(p, delta, st, mt, lp, vt, U.ex_at(is_ex(st), f), f, Con{a, args})
    case 1n+p T.ELam{n, ty, b, bi} Con{a, rest}:
      +pf = p
      +r = U.inst(256n, is_ex(st), is_nx(st), U.ex_at(is_ex(st), b), b, 0,
                  a)
      +s2 : IS = IS{U.sr_t(r), U.sr_nx(r), is_lnt(st), is_nlx(st), is_wm(st), is_ht(st), is_natn(st), is_strn(st), is_qt_t(st)}
      whnf(pf, delta, s2, mt, lp, vt, U.ex_at(is_ex(s2), U.sr_i(r)), U.sr_i(r), rest)
    case 1n+p T.ELet{n, ty, v, b} _:
      +pf = p
      +r = U.inst(256n, is_ex(st), is_nx(st), U.ex_at(is_ex(st), b), b, 0,
                  v)
      +s2 : IS = IS{U.sr_t(r), U.sr_nx(r), is_lnt(st), is_nlx(st), is_wm(st), is_ht(st), is_natn(st), is_strn(st), is_qt_t(st)}
      whnf(pf, delta, s2, mt, lp, vt, U.ex_at(is_ex(s2), U.sr_i(r)), U.sr_i(r), args)
    # A constant with no unfolding leaves `e` alone and reads as EBad next
    # round, which falls through to rebuild: one wasted step rather than the
    # whole fuel budget.
    # Iota, then delta. For a recursor applied to its parameters, motive,
    # minor premises and a major premise that reduces to `c_j a-bar f-bar`,
    # the reduct is `minor_j f-bar ih-bar`, with one inductive hypothesis per
    # recursive field: the recursor applied to the same parameters, motive and
    # minors, then that field.
    #
    # Restricted to inductives with no indices, which covers Nat, Bool and
    # List; with indices the inductive hypotheses need the field's own index
    # arguments and this does not build them.
    case 1n+p T.EConst{n, us} _:
      +pf = p
      +mi = R.get(Meta, 32n, mt, n, MNone{})
      +pp = meta_p(mi)
      +need = (pp + 1 + meta_n(mi) : U32)
      # Iota is ON. It was gated off for a long time because, measured
      # alone, it changed no verdict: the tests that need reduction were
      # blocked upstream in `defeq`. Once `defeq` could answer *yes* -- eta,
      # proof irrelevance -- and the application rule could type a recursor
      # application, the three together were worth four tests. None of them
      # is worth anything without the others.
      +canio = meta_is_rec(mi) && U32.is_eq(meta_k(mi), 0)
               && U32.is_gt(len_u(args, 0), need)
      # Bend is strict, so this sub-reduction runs on every constant unless
      # the index is forced to a sentinel when iota does not apply -- a
      # sentinel reads as EBad and returns at once. Without the guard every
      # constant lookup speculatively normalised an argument.
      +maj = S.pick(canio, nth_u(args, need, 4294967295), 4294967295)
      +wm0 = whnf(pf, delta, st, mt, lp, vt, U.ex_at(is_ex(st), maj), maj,
                  Nil{})
      +mraw = U.ex_at(is_ex(ir_st(wm0)), ir_ty(wm0))
      +wm = lit_major(is_nat_lit(mraw)
                      && U32.is_eq(meta_ind(mi), is_natn(st)),
                      ir_st(wm0), nat_digits(mraw), ir_ty(wm0),
                      is_qt(st, 3), is_qt(st, 4))
      +exm = is_ex(ir_st(wm))
      +mnode = U.ex_at(exm, ir_ty(wm))
      +cmi = R.get(Meta, 32n, mt,
                   const_nm2(spine_hd(256n, exm, mnode)), MNone{})
      +ok2 = canio && meta_is_ctor(cmi)
             && U32.is_eq(meta_ind(cmi), meta_ind(mi))
      +vi = R.get(U32, 32n, vt, n, 4294967295)
      # Delta happens only when the caller allows it. `defeq` turns it
      # off so it can drive unfolding itself, by height.
      +can = delta && U32.is_ne(vi, 4294967295)
      # --- literal arithmetic --------------------------------------------
      # `Nat.add`, `Nat.sub` and `Nat.ble` on two literals are computed on
      # the digits. Without this they would have to go through the recursor,
      # and `other/nat-lit-add` is 123456789 + 987654321.
      +aw = S.pick(U32.is_eq(n, is_qt(st, 5)), 0,
                   S.pick(U32.is_eq(n, is_qt(st, 6)), 1,
                          S.pick(U32.is_eq(n, is_qt(st, 7)), 2, 3)))
      +isar = U32.is_lt(aw, 3) && U32.is_gt(len_u(args, 0), 1)
      +a0 = S.pick(isar, nth_u(args, 0, 4294967295), 4294967295)
      +a1 = S.pick(isar, nth_u(args, 1, 4294967295), 4294967295)
      +wa = whnf(pf, delta, st, mt, lp, vt, U.ex_at(is_ex(st), a0), a0,
                 Nil{})
      +wb = whnf(pf, delta, ir_st(wa), mt, lp, vt,
                 U.ex_at(is_ex(ir_st(wa)), a1), a1, Nil{})
      +na = U.ex_at(is_ex(ir_st(wb)), ir_ty(wa))
      +nb = U.ex_at(is_ex(ir_st(wb)), ir_ty(wb))
      +arok = isar && is_nat_lit(na) && is_nat_lit(nb)
      +ar = lit_arith(arok, aw, ir_st(wb), nat_digits(na), nat_digits(nb),
                      is_qt(st, 8), is_qt(st, 9))
      # --- quotients -----------------------------------------------------
      +isql = U32.is_eq(n, is_qt(st, 0)) && U32.is_gt(len_u(args, 0), 5)
      +isqi = U32.is_eq(n, is_qt(st, 1)) && U32.is_gt(len_u(args, 0), 4)
      +qneed = S.pick(isql, 5, 4)
      +qmaj = S.pick(isql || isqi, nth_u(args, qneed, 4294967295),
                     4294967295)
      +qw = whnf(pf, delta, ir_st(wm), mt, lp, vt,
                 U.ex_at(is_ex(ir_st(wm)), qmaj), qmaj, Nil{})
      +qex = is_ex(ir_st(qw))
      +qargs = spine_ar(256n, qex, U.ex_at(qex, ir_ty(qw)), Nil{})
      +qok = (isql || isqi)
             && U32.is_eq(const_nm2(spine_hd(256n, qex,
                                             U.ex_at(qex, ir_ty(qw)))),
                          is_qt(st, 2))
             && U32.is_gt(len_u(qargs, 0), 2)
      +qt2 = quot_tgt(qok, ir_st(qw), nth_u(args, 3, 4294967295),
                      nth_u(qargs, 2, 4294967295))
      +tgt0 = iota_tgt(ok2, can, ir_st(qt2), lp, n, us, vi, meta_recs(cmi),
                       args, need,
                       S.pick_l(ok2, skip_u(spine_ar(256n, exm, mnode,
                                                     Nil{}), pp), Nil{}),
                       meta_ci(cmi), pp)
      +tgt = pick_ir(arok, ar, pick_ir(qok, qt2, tgt0))
      +s4 = ir_st(tgt)
      whnf(pf, delta, s4, mt, lp, vt, U.ex_at(is_ex(s4), ir_ty(tgt)),
           S.pick(arok || qok, ir_ty(tgt),
                  S.pick(ok2, ir_ty(tgt), S.pick(can, ir_ty(tgt), e))),
           S.pick_l(arok, skip_u(args, 2),
                    S.pick_l(qok, skip_u(args, (qneed + 1 : U32)),
                             S.pick_l(ok2, skip_u(args, (need + 1 : U32)),
                                      args))))
    # Projection reduction: `(c a-bar f-bar).i` is the matching field.
    case 1n+p T.EProj{tn, idx, sx} _:
      +pf = p
      +ws = whnf(pf, delta, st, mt, lp, vt, U.ex_at(is_ex(st), sx), sx, Nil{})
      +exz = is_ex(ir_st(ws))
      +snode = U.ex_at(exz, ir_ty(ws))
      +cmi = R.get(Meta, 32n, mt,
                   const_nm2(spine_hd(256n, exz, snode)), MNone{})
      # Off, on measurement -- the one feature here whose cost is real and
      # not an artefact. Reduction re-reduces the same structure for every
      # projection of it, and these tests project repeatedly:
      # `perf/magma-string-n4` 48 s -> 305 s against a 70 s limit, and the
      # reduction memo only brings that to 256 s. It buys `098_projRed`.
      # Typing stays on; only the reduction is off.
      +okp = meta_is_ctor(cmi)
      +fld = nth_u(spine_ar(256n, exz, snode, Nil{}),
                   (meta_p(cmi) + idx : U32), 4294967295)
      whnf(pf, delta, ir_st(ws), mt, lp, vt,
           U.ex_at(exz, S.pick(okp, fld, 4294967295)),
           S.pick(okp, fld, e), args)
    case 1n+p _ _:
      rebuild(args, st, e)

# Reduce an index to weak head normal form, carrying the state.
# Memoised. `match` is what makes this work: `pick` would evaluate both
# branches, so the reduction would run even on a hit and the memo would buy
# nothing. Measurement said memoising reduction is the prerequisite for iota
# to pay for itself.
def whd_store(+i: U32, r: IR) -> IR:
  match r:
    case IR{st, ty, ok}:
      match st:
        case IS{ex, nx, lnt, nlx, wm, ht, natn, strn, qt}:
          +pty = ty
          IR{IS{ex, nx, lnt, nlx, R.set(U32, 64n, wm, i, pty, 4294967295), ht,
             natn, strn, qt},
             pty, ok}

def whd_sel(+hit: Bool, +h: U32, +st: IS, +mt: R.Tr<Meta>,
            +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +i: U32) -> IR:
  match hit:
    case True{}:
      IR{st, h, True{}}
    case False{}:
      # The store is back on, under a narrower claim than the one that
      # failed. `defeq` and `infer` thread state linearly: every allocation
      # bumps `nx` and returns a new `IS`, and `wm` rides inside that same
      # `IS`. So an entry is only ever visible to states descended from the
      # one that stored it, and a descendant's trie is a superset. The
      # earlier hang was a blowup, not an unsoundness -- see the test below.
      # The store is off while iota is off: measured 26.7 s against 23.5 s on
      # `perf/grind-ring-5`, so with no iota to amortise it is a small net
      # cost. It is correct, though, and it is what makes iota affordable --
      # see the note there. The earlier claim that it *hung*
      # `bugs/nested-unused-param` was wrong: re-measured at 0.21 s. Iota was
      # the hang, not the memo.
      whd_store(i, whnf(256n, True{}, st, mt, lp, vt,
                        U.ex_at(is_ex(st), i), i, Nil{}))

def whd(+st: IS, +mt: R.Tr<Meta>, +lp: R.Tr<List<&2, U32>>,
        +vt: R.Tr<U32>, +i: U32) -> IR:
  +h = R.get(U32, 64n, is_wm(st), i, 4294967295)
  whd_sel(U32.is_ne(h, 4294967295), h, st, mt, lp, vt, i)

# Weak head normal form WITHOUT delta: beta, zeta, iota and projection only.
# This is Lean's `whnfCore`, and having it is what lets `defeq` unfold one
# side at a time in height order instead of normalising both sides first.
#
# Deliberately not memoised: the memo is keyed by expression index and the
# two modes give different answers for the same index, so they must not share
# it.
def whd_core(+st: IS, +mt: R.Tr<Meta>, +lp: R.Tr<List<&2, U32>>,
             +vt: R.Tr<U32>, +i: U32) -> IR:
  whnf(256n, False{}, st, mt, lp, vt, U.ex_at(is_ex(st), i), i, Nil{})

def dr_wh(+r: IR) -> IS:
  ir_st(r)

def tele_doms_i(+fuel: Nat, +ex: R.Tr<T.Ex>, +x: T.Ex,
                acc: List<&2, U32>) -> List<&2, U32>:
  match fuel x:
    case 0n _:
      acc
    case 1n+p T.EAll{n, t, b, bi}:
      tele_doms_i(p, ex, U.ex_at(ex, b), Con{t, acc})
    case 1n+p _:
      acc

# --- projection typing --------------------------------------------------
# For `s : S a-bar` with the single constructor
# `c : forall a-bar (f_0..f_{m-1}), S a-bar`, the type of `s.i` is the
# (i+1)-th field type with the parameters replaced by `a-bar` and each
# earlier field replaced by the corresponding projection of `s`.
#
# This is done by peeling the constructor's telescope from the OUTSIDE,
# instantiating `bvar 0` of each Pi body in turn -- the `instantiate1` of
# every real kernel -- and *not* by extracting the field type and
# substituting into it afterwards.
#
# The difference is not cosmetic; the second way is wrong, and it was the
# bug here. `U.inst` decrements the indices above the one it replaces, which
# is correct for one substitution but not for a sequence: once a substituted
# *value* is embedded in the term, the next substitution in the sequence
# shifts it again. `Prod.snd`'s field type `#1` went
#
#     #1  --[subst f_0]-->  #0  --[subst beta]-->  #1  --[subst alpha]-->  #0
#
# where the answer is `#1`. `Prod.fst` needed one substitution fewer and
# never re-shifted an embedded value, so it came out right -- which is why
# every `*.fst` in the corpus passed and every `*.snd` declined.
#
# Peeling outside-in has no such step: each `inst` substitutes the bvar 0 of
# a Pi body with a value from the surrounding context, and no binders remain
# outside to shift it.
def peel_tele(n: Nat, +st: IS, +tyi: U32, vals: List<&2, U32>) -> IR:
  match n vals:
    case 0n _:
      IR{st, tyi, True{}}
    case 1n+q Nil{}:
      IR{st, tyi, True{}}
    case 1n+q Con{v, rest}:
      +node = U.ex_at(is_ex(st), tyi)
      +cod = all_cod(node)
      +r = U.inst(256n, is_ex(st), is_nx(st), U.ex_at(is_ex(st), cod), cod,
                  0, v)
      +nst : IS = IS{U.sr_t(r), U.sr_nx(r), is_lnt(st), is_nlx(st),
                     is_wm(st), is_ht(st), is_natn(st), is_strn(st), is_qt_t(st)}
      +rec = peel_tele(q, nst, U.sr_i(r), rest)
      pick_ir(is_all(node), rec, ir_bad(ir_st(rec)))

# `s.0, s.1, .., s.(i-1)` in ascending order, to be peeled after the
# parameters -- the same order the constructor binds them in.
def proj_nodes(n: Nat, +i: U32, +tn: U32, +sx: U32, +st: IS,
               acc: List<&2, U32>) -> LS:
  match n:
    case 0n:
      LS{st, rev_u(acc, Nil{})}
    case 1n+q:
      +pr = alloc_ex(st, T.EProj{tn, i, sx})
      proj_nodes(q, (i + 1 : U32), tn, sx, ir_st(pr),
                 Con{ir_ty(pr), acc})

# Byte-list equality, for literal payloads.
def eq_u32s(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{h1, t1} Con{h2, t2}:
      U32.is_eq(h1, h2) && eq_u32s(t1, t2)
    case _ _:
      False{}

# --- definitional equality ----------------------------------------------
# Both arguments are already in weak head normal form; the recursive calls
# normalise the children before descending. Same shape as `eq_ex`: the nodes
# arrive as parameters because a match cannot scrutinise a computed value.
#
# When it may answer NO is the delicate part. Two terms in normal form with
# different head constructors are not definitionally equal -- but only if the
# normal form is genuine. This whnf implements beta, zeta and delta and NOT
# iota, projection or literal reduction, so a term headed by a constant or an
# application may merely be stuck on something unimplemented, and comparing
# those can only answer "cannot decide".
#
# So NO is restricted to pairs whose heads are Sort, Pi or lambda: those are
# rigid, none of them reduces further under any rule, and the one way a
# lambda can equal a non-lambda -- eta -- is excluded by requiring both heads
# to be in that set. Proof irrelevance is not implemented, which is sound
# here for the same reason: it would only ever turn a NO into a YES, and no
# NO this returns involves a proposition.
type DR is Data:
  DR{st: IS, r: L.Tri}

def dr_st(+d: DR) -> IS:
  match d:
    case DR{st, r}:
      st

def dr_r(+d: DR) -> L.Tri:
  match d:
    case DR{st, r}:
      r

# Where `defeq` may answer NO, now that it actually reaches real
# comparisons. Without proof irrelevance and eta it can only answer no about
# **types**, never about terms:
#
#   * A Sort and a Pi are never proofs -- a Sort's type is a Sort, a Pi's type
#     is a Sort -- so proof irrelevance cannot make two of them equal, and eta
#     does not apply to either. Two of them with different heads, or two Sorts
#     at different levels, are genuinely unequal.
#   * A lambda MAY be a proof, so a lambda against anything else could be
#     equal by eta, and two lambdas could be equal by proof irrelevance under
#     the binder -- which is `tutorial/107_proofIrrelevanceUnderBinder`.
#   * Likewise two applications, or two different bound variables, may be two
#     proofs of the same proposition.
#
# So the term paths are softened: they may confirm equality but never deny
# it. Denying it there rejected `104_proofIrrelevance`, all three `unitEta`
# tests, and three of the big perf files.
def rigid(+x: T.Ex) -> Bool:
  match x:
    case T.ESort{l}:
      True{}
    case T.EAll{n, t, b, bi}:
      True{}
    case _:
      False{}

def soften(+t: L.Tri) -> L.Tri:
  L.pick_tri(L.tri_is_no(t), L.TUnk{}, t)

# Disabled, with measurement behind it. With iota switched on this path
# produced wrong REJECTS -- `tutorial/070_nRec` and `081_listRecReduction` --
# because reduction is incomplete: iota only fires for inductives without
# indices, so one side of a comparison can reduce while the other stays
# stuck, and two differently-stuck terms look like a genuine mismatch.
#
# Turning it off costs nothing measurable: with it on, `defeq` contributed
# **zero** of the 42 reject tests caught -- every one of those comes from a
# structural or inductive check. So this was carrying risk without carrying
# score, and it can come back once reduction is complete enough that a
# normal form really is one.
def mismatch(+x: T.Ex, +y: T.Ex) -> L.Tri:
  L.pick_tri(False{} && rigid(x) && rigid(y), L.TNo{}, L.TUnk{})

# --- structure eta -------------------------------------------------------
# `S.mk s.0 .. s.(k-1)` equals `s` for a structure `S`. Rather than looping
# over the fields and comparing each -- a loop that would call `defeq` while
# `defeq` called it, which Bend forbids -- the eta-expansion is *built* as a
# term and handed to `defeq` as a single comparison. Its own application case
# then compares the spines pairwise, which is exactly the field-by-field
# check.
#
# Both builders are pure allocation; neither compares anything.
def app_build(n: Nat, args: List<&2, U32>, +st: IS, +acc: U32) -> IR:
  match n args:
    case 0n _:
      IR{st, acc, True{}}
    case 1n+q Nil{}:
      IR{st, acc, True{}}
    case 1n+q Con{a, rest}:
      +r = alloc_ex(st, T.EApp{acc, a})
      app_build(q, rest, ir_st(r), ir_ty(r))

def proj_build(n: Nat, +i: U32, +tn: U32, +yi: U32, +st: IS,
               +acc: U32) -> IR:
  match n:
    case 0n:
      IR{st, acc, True{}}
    case 1n+q:
      +pj = alloc_ex(st, T.EProj{tn, i, yi})
      +ap = alloc_ex(ir_st(pj), T.EApp{acc, ir_ty(pj)})
      proj_build(q, (i + 1 : U32), tn, yi, ir_st(ap), ir_ty(ap))

def pick_dr(+z: Bool, +a: DR, +b: DR) -> DR:
  match z:
    case True{}:
      a
    case False{}:
      b

# `nt` and `ctx` are carried so that the bound-variable case can look up a
# variable's TYPE. Two questions need it, and both are answered there:
# proof irrelevance (two proofs of the same proposition are equal) and
# unit-like eta (any two elements of a no-field structure are equal). Both
# are about terms that are not syntactically equal and have no reduct --
# bare bound variables -- so no amount of reduction reaches them.
#
# `sl` is defined above this point, so the universe of a context type is
# available without calling `infer`, which Bend would not allow.
# --- a type oracle for `defeq` ------------------------------------------
# Proof irrelevance needs the TYPE of each side, and `defeq` sits above
# `infer` in this file because Bend forbids the two calling each other. So
# this computes the type of the shapes that irrelevance actually meets:
# a constant, a bound variable, or an application whose head is one of those.
# Anything else answers "unknown" and the rule simply does not fire.
#
# That is enough for the real cases. `107_proofIrrelevanceUnderBinder`
# compares `f anElem` with `f anotherElem`, where `f : aType -> aProp`: the
# two *arguments* are elements of a Type and are genuinely different, but the
# two *applications* are both proofs of `aProp`, and that is what makes them
# equal. Comparing them argument-wise, as the application rule does, can only
# fail.
def dq_head_ty(+st: IS, +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>,
               +ctx: List<&2, U32>, +h: T.Ex) -> IR:
  match h:
    case T.EConst{n, us}:
      +ti = R.get(U32, 32n, nt, n, 4294967295)
      pick_ir(U32.is_eq(ti, 4294967295), IR{st, 4294967295, False{}},
              lsubst(256n, st, U.ex_at(is_ex(st), ti), ti,
                     R.get(List<&2, U32>, 32n, lp, n, Nil{}),
                     lns_of(us, is_lnt(st))))
    case T.EBVar{i}:
      +ti = nth_u(ctx, i, 4294967295)
      +lr = U.lift(256n, is_ex(st), is_nx(st), U.ex_at(is_ex(st), ti), ti,
                   0, (i + 1 : U32))
      IR{IS{U.sr_t(lr), U.sr_nx(lr), is_lnt(st), is_nlx(st), is_wm(st), is_ht(st), is_natn(st), is_strn(st), is_qt_t(st)},
         U.sr_i(lr), Bool.not(U32.is_eq(ti, 4294967295))}
    case _:
      IR{st, 4294967295, False{}}

def dq_type_of(+st: IS, +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>,
               +ctx: List<&2, U32>, +x: T.Ex) -> IR:
  +hd = spine_hd(256n, is_ex(st), x)
  +ht = dq_head_ty(st, nt, lp, ctx, hd)
  +pt = peel_tele(256n, ir_st(ht), ir_ty(ht),
                  spine_ar(256n, is_ex(ir_st(ht)), x, Nil{}))
  pick_ir(ir_ok(ht), pt, IR{ir_st(pt), 4294967295, False{}})

# Proof irrelevance, as a fallback after a structural comparison has failed:
# two terms are equal when both have a type, those types are the same, and
# that type is a proposition. Structural only -- it may not call `defeq`,
# which calls this.
def dq_irrel(+st: IS, +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>,
             +ctx: List<&2, U32>, +x: T.Ex, +y: T.Ex) -> DR:
  +rx = dq_type_of(st, nt, lp, ctx, x)
  +ry = dq_type_of(ir_st(rx), nt, lp, ctx, y)
  +s2 : IS = ir_st(ry)
  +both = ir_ok(rx) && ir_ok(ry)
  +tx = U.ex_at(is_ex(s2), ir_ty(rx))
  +same = L.tri_is_yes(eq_ex(256n, U32.is_eq(ir_ty(rx), ir_ty(ry)),
                             is_ex(s2), is_lnt(s2), tx,
                             U.ex_at(is_ex(s2), ir_ty(ry))))
  +isprop = L.tri_is_yes(L.ln_is_zero(sl(256n, is_ex(s2), is_lnt(s2), nt,
                                         lp, tx, ctx)))
  DR{s2, L.pick_tri(both && same && isprop, L.TYes{}, L.TUnk{})}

# A cheap gate on the expensive rule: both spines must have the SAME head.
# That is the shape irrelevance is for -- `f anElem` against `f anotherElem`,
# where the head carries the type and only the arguments differ -- and it
# costs two spine walks instead of two telescope peels.
#
# Without the gate the rule fired on every failed application comparison and
# took `perf/grind-ring-5` from about 60 s to 490 s.
def dq_head_key(+x: T.Ex) -> U32:
  match x:
    case T.EConst{n, us}:
      n
    case T.EBVar{i}:
      (i + 2147483648 : U32)
    case _:
      4294967295

def dq_same_head(+st: IS, +x: T.Ex, +y: T.Ex) -> Bool:
  +kx = dq_head_key(spine_hd(256n, is_ex(st), x))
  Bool.not(U32.is_eq(kx, 4294967295))
  && U32.is_eq(kx, dq_head_key(spine_hd(256n, is_ex(st), y)))

def dq_gate(+ok: Bool, +st: IS, +nt: R.Tr<U32>,
            +lp: R.Tr<List<&2, U32>>, +ctx: List<&2, U32>,
            +x: T.Ex, +y: T.Ex) -> DR:
  match ok:
    case False{}:
      DR{st, L.TUnk{}}
    case True{}:
      dq_irrel(st, nt, lp, ctx, x, y)

# A `match`, so the fallback is not computed when the structural comparison
# already succeeded -- Bend is strict and a `pick` would pay for it always.
def dq_or_irrel(+t: L.Tri, +st: IS, +nt: R.Tr<U32>,
                +lp: R.Tr<List<&2, U32>>, +ctx: List<&2, U32>,
                +x: T.Ex, +y: T.Ex) -> DR:
  match t:
    case L.TYes{}:
      DR{st, L.TYes{}}
    case _:
      dq_gate(dq_same_head(st, x, y), st, nt, lp, ctx, x, y)

def defeq(+fuel: Nat, +same: Bool, +st: IS, +mt: R.Tr<Meta>,
          +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
          +ctx: List<&2, U32>, +x: T.Ex, +y: T.Ex) -> DR:
  match fuel same x y:
    case 0n _ _ _:
      DR{st, L.TUnk{}}
    case 1n+p True{} _ _:
      DR{st, L.TYes{}}
    case 1n+p False{} T.ESort{a} T.ESort{b}:
      DR{st, L.ln_cmp(R.get(L.LN, 32n, is_lnt(st), a, L.LNun{}),
                      R.get(L.LN, 32n, is_lnt(st), b, L.LNun{}))}
    # Two bound variables. Equal indices are equal. Different indices are
    # still equal in two cases, and both are decided from their types:
    #
    #   * proof irrelevance -- the two have the same type and that type is a
    #     proposition. `104_proofIrrelevance` is `forall (P : Prop) (p q : P),
    #     Eq p q`, which needs `#1 == #0` and has no reduct at all.
    #   * unit-like eta -- the type is a structure with no fields, so it has
    #     at most one element. `108_unitEta1` needs exactly this.
    #
    # The types come from `ctx` and are lifted by `i + 1`, the same way
    # `infer`'s bound-variable case lifts them, so the two land in a common
    # context and can be compared structurally.
    case 1n+p False{} T.EBVar{a} T.EBVar{b}:
      +pa2 = a
      +pb2 = b
      +ta = nth_u(ctx, pa2, 4294967295)
      +tb = nth_u(ctx, pb2, 4294967295)
      +la = U.lift(256n, is_ex(st), is_nx(st), U.ex_at(is_ex(st), ta), ta,
                   0, (pa2 + 1 : U32))
      +s1 : IS = IS{U.sr_t(la), U.sr_nx(la), is_lnt(st), is_nlx(st),
                    is_wm(st), is_ht(st), is_natn(st), is_strn(st), is_qt_t(st)}
      +lb = U.lift(256n, is_ex(s1), is_nx(s1), U.ex_at(is_ex(s1), tb), tb,
                   0, (pb2 + 1 : U32))
      +s2 : IS = IS{U.sr_t(lb), U.sr_nx(lb), is_lnt(s1), is_nlx(s1),
                    is_wm(s1), is_ht(s1), is_natn(s1), is_strn(s1), is_qt_t(s1)}
      # The two types are REDUCED before being compared and before their
      # universe is asked for. `106_proofIrrelevanceWhnf` is the case: the
      # variables' type is `constType (Sort u) Prop`, which is a proposition
      # only after unfolding, and `sl` does not unfold.
      +wa2 = whd(s2, mt, lp, vt, U.sr_i(la))
      +wb2 = whd(ir_st(wa2), mt, lp, vt, U.sr_i(lb))
      +s3 : IS = ir_st(wb2)
      +samety = L.tri_is_yes(eq_ex(256n,
                                   U32.is_eq(ir_ty(wa2), ir_ty(wb2)),
                                   is_ex(s3), is_lnt(s3),
                                   U.ex_at(is_ex(s3), ir_ty(wa2)),
                                   U.ex_at(is_ex(s3), ir_ty(wb2))))
      +tynode = U.ex_at(is_ex(s3), ir_ty(wa2))
      # "Is this a proposition?" is answered by taking the type OF the type
      # and reducing it, not by `sl` -- which cannot reduce, and so could not
      # see through `106_proofIrrelevanceWhnf`, where the variables' type is
      # a bound variable `P` whose own type is `constType (Sort u) Prop`.
      # The type oracle already handles a const- or bvar-headed spine, which
      # is every shape this meets.
      +rt = dq_type_of(s3, nt, lp, ctx, tynode)
      +wrt = whd(ir_st(rt), mt, lp, vt, ir_ty(rt))
      +s4 : IS = ir_st(wrt)
      +ks = U.ex_at(is_ex(s4), ir_ty(wrt))
      +isprop = (ir_ok(rt) && is_sortx(ks)
                 && L.tri_is_yes(L.ln_is_zero(R.get(L.LN, 32n, is_lnt(s4),
                                                    sort_lvl_of(ks),
                                                    L.LNun{}))))
                || L.tri_is_yes(L.ln_is_zero(sl(256n, is_ex(s4),
                                                is_lnt(s4), nt, lp,
                                                tynode, ctx)))
      +smi = R.get(Meta, 32n, mt, const_nm2(spine_hd(256n, is_ex(s4),
                                                     tynode)), MNone{})
      +isunit = meta_is_ind(smi) && U32.is_eq(meta_nf(smi), 0)
      +both = U32.is_lt(pa2, 4294967295) && U32.is_lt(pb2, 4294967295)
              && Bool.not(U32.is_eq(ta, 4294967295))
              && Bool.not(U32.is_eq(tb, 4294967295))
      DR{s4, L.pick_tri(U32.is_eq(pa2, pb2), L.TYes{},
                        L.pick_tri(both && samety && (isprop || isunit),
                                   L.TYes{}, L.TUnk{}))}
    # Two constants. The same name with equal level arguments is equal.
    # Different names are still equal when both are proofs of the same
    # proposition -- proof irrelevance again, but for constants, where the
    # type comes from `nt` rather than from the context.
    # `107_proofIrrelevanceUnderBinder` compares `f C9` with `f C10`, where
    # `C9` and `C10` are two axioms of the same Prop.
    case 1n+p False{} T.EConst{a, us} T.EConst{b, vs}:
      +pa3 = a
      +pb3 = b
      +ta3 = R.get(U32, 32n, nt, pa3, 4294967295)
      +tb3 = R.get(U32, 32n, nt, pb3, 4294967295)
      +known = Bool.not(U32.is_eq(ta3, 4294967295))
               && Bool.not(U32.is_eq(tb3, 4294967295))
      +tn3 = U.ex_at(is_ex(st), ta3)
      +samety3 = L.tri_is_yes(eq_ex(256n, U32.is_eq(ta3, tb3), is_ex(st),
                                    is_lnt(st), tn3,
                                    U.ex_at(is_ex(st), tb3)))
      +isprop3 = L.tri_is_yes(L.ln_is_zero(sl(256n, is_ex(st), is_lnt(st),
                                              nt, lp, tn3, ctx)))
      DR{st, L.pick_tri(U32.is_eq(pa3, pb3), eq_lvls(us, vs, is_lnt(st)),
                        L.pick_tri(known && samety3 && isprop3,
                                   L.TYes{}, L.TUnk{}))}
    case 1n+p False{} T.EAll{n1, t1, b1, i1} T.EAll{n2, t2, b2, i2}:
      +pf = p
      +w1 = whd(st, mt, lp, vt, t1)
      +w2 = whd(dr_wh(w1), mt, lp, vt, t2)
      +d1 = defeq(pf, U32.is_eq(t1, t2), dr_wh(w2), mt, nt, lp, vt, ctx,
                  U.ex_at(is_ex(dr_wh(w2)), ir_ty(w1)),
                  U.ex_at(is_ex(dr_wh(w2)), ir_ty(w2)))
      # The body is compared with the binder in scope, so the
      # bound-variable case below can find a variable's type.
      +pt1 = t1
      +w3 = whd(dr_st(d1), mt, lp, vt, b1)
      +w4 = whd(dr_wh(w3), mt, lp, vt, b2)
      +d2 = defeq(pf, U32.is_eq(b1, b2), dr_wh(w4), mt, nt, lp, vt,
                  Con{pt1, ctx},
                  U.ex_at(is_ex(dr_wh(w4)), ir_ty(w3)),
                  U.ex_at(is_ex(dr_wh(w4)), ir_ty(w4)))
      DR{dr_st(d2), tri_and(dr_r(d1), dr_r(d2))}
    case 1n+p False{} T.ELam{n1, t1, b1, i1} T.ELam{n2, t2, b2, i2}:
      +pf = p
      +plt = t1
      +w3 = whd(st, mt, lp, vt, b1)
      +w4 = whd(dr_wh(w3), mt, lp, vt, b2)
      +d2 = defeq(pf, U32.is_eq(b1, b2), dr_wh(w4), mt, nt, lp, vt,
                  Con{plt, ctx},
                  U.ex_at(is_ex(dr_wh(w4)), ir_ty(w3)),
                  U.ex_at(is_ex(dr_wh(w4)), ir_ty(w4)))
      DR{dr_st(d2), soften(dr_r(d2))}
    case 1n+p False{} T.EApp{f1, a1} T.EApp{f2, a2}:
      +pf = p
      +w1 = whd(st, mt, lp, vt, f1)
      +w2 = whd(dr_wh(w1), mt, lp, vt, f2)
      +d1 = defeq(pf, U32.is_eq(f1, f2), dr_wh(w2), mt, nt, lp, vt, ctx,
                  U.ex_at(is_ex(dr_wh(w2)), ir_ty(w1)),
                  U.ex_at(is_ex(dr_wh(w2)), ir_ty(w2)))
      +w3 = whd(dr_st(d1), mt, lp, vt, a1)
      +w4 = whd(dr_wh(w3), mt, lp, vt, a2)
      +d2 = defeq(pf, U32.is_eq(a1, a2), dr_wh(w4), mt, nt, lp, vt, ctx,
                  U.ex_at(is_ex(dr_wh(w4)), ir_ty(w3)),
                  U.ex_at(is_ex(dr_wh(w4)), ir_ty(w4)))
      dq_or_irrel(soften(tri_and(dr_r(d1), dr_r(d2))), dr_st(d2), nt, lp,
                  ctx, x, y)
    # Eta for functions: `fun x => b` equals `t` exactly when `b` equals
    # `t x`. The lambda supplies the binder, so this needs no type inference
    # -- which matters, because `defeq` sits above `infer` in this file and
    # Bend forbids the two calling each other.
    #
    # `t`'s index is not a parameter (callers pass nodes), so the node is
    # re-allocated to get one, lifted past the binder and applied to
    # `bvar 0`. Written out twice rather than factored into a helper: a
    # helper would call `defeq` and `defeq` would call it, which is mutual
    # recursion.
    case 1n+p False{} T.ELam{n1, t1, b1, i1} _:
      +pf = p
      +py : T.Ex = y
      +ay = alloc_ex(st, py)
      +sy : IS = ir_st(ay)
      +lr = U.lift(256n, is_ex(sy), is_nx(sy),
                   U.ex_at(is_ex(sy), ir_ty(ay)), ir_ty(ay), 0, 1)
      +s1 : IS = IS{U.sr_t(lr), U.sr_nx(lr), is_lnt(sy), is_nlx(sy),
                    is_wm(sy), is_ht(sy), is_natn(sy), is_strn(sy), is_qt_t(sy)}
      +bv = alloc_ex(s1, T.EBVar{0})
      +ap = alloc_ex(ir_st(bv), T.EApp{U.sr_i(lr), ir_ty(bv)})
      +s2 : IS = ir_st(ap)
      +w1 = whd(s2, mt, lp, vt, b1)
      +w2 = whd(ir_st(w1), mt, lp, vt, ir_ty(ap))
      +s3 : IS = ir_st(w2)
      +d = defeq(pf, False{}, s3, mt, nt, lp, vt, ctx,
                 U.ex_at(is_ex(s3), ir_ty(w1)),
                 U.ex_at(is_ex(s3), ir_ty(w2)))
      DR{dr_st(d), soften(dr_r(d))}
    case 1n+p False{} _ T.ELam{n2, t2, b2, i2}:
      +pf = p
      +px : T.Ex = x
      +ax = alloc_ex(st, px)
      +sx : IS = ir_st(ax)
      +lr = U.lift(256n, is_ex(sx), is_nx(sx),
                   U.ex_at(is_ex(sx), ir_ty(ax)), ir_ty(ax), 0, 1)
      +s1 : IS = IS{U.sr_t(lr), U.sr_nx(lr), is_lnt(sx), is_nlx(sx),
                    is_wm(sx), is_ht(sx), is_natn(sx), is_strn(sx), is_qt_t(sx)}
      +bv = alloc_ex(s1, T.EBVar{0})
      +ap = alloc_ex(ir_st(bv), T.EApp{U.sr_i(lr), ir_ty(bv)})
      +s2 : IS = ir_st(ap)
      +w1 = whd(s2, mt, lp, vt, ir_ty(ap))
      +w2 = whd(ir_st(w1), mt, lp, vt, b2)
      +s3 : IS = ir_st(w2)
      +d = defeq(pf, False{}, s3, mt, nt, lp, vt, ctx,
                 U.ex_at(is_ex(s3), ir_ty(w1)),
                 U.ex_at(is_ex(s3), ir_ty(w2)))
      DR{dr_st(d), soften(dr_r(d))}
    # Literals: two `Nat` or `String` literals are equal exactly when their
    # digits are. Without this they fell to the catch-all and compared as
    # "cannot decide", so even a literal against itself was undecided.
    case 1n+p False{} T.ENat{d1} T.ENat{d2}:
      DR{st, L.pick_tri(eq_u32s(d1, d2), L.TYes{}, L.TUnk{})}
    case 1n+p False{} T.EStr{d1} T.EStr{d2}:
      DR{st, L.pick_tri(eq_u32s(d1, d2), L.TYes{}, L.TUnk{})}
    # A literal against a numeral in constructor form: expand the literal one
    # step and compare again. `ENat` against `ENat` is handled above, so this
    # cannot loop on two literals, and the fuel bounds the depth.
    case 1n+p False{} T.ENat{d} _:
      +pf = p
      +nx2 = nat_expand(st, d, is_qt(st, 3), is_qt(st, 4))
      +sn2 : IS = ir_st(nx2)
      +dz = defeq(pf, False{}, sn2, mt, nt, lp, vt, ctx,
                  U.ex_at(is_ex(sn2), ir_ty(nx2)), y)
      DR{dr_st(dz), soften(dr_r(dz))}
    case 1n+p False{} _ T.ENat{d}:
      +pf = p
      +nx2 = nat_expand(st, d, is_qt(st, 3), is_qt(st, 4))
      +sn2 : IS = ir_st(nx2)
      +dz = defeq(pf, False{}, sn2, mt, nt, lp, vt, ctx, x,
                  U.ex_at(is_ex(sn2), ir_ty(nx2)))
      DR{dr_st(dz), soften(dr_r(dz))}
    # Structure eta, with the constructor application on the left. A
    # structure's constructor is recognised from `mt`, so no type inference
    # is needed; the parameters are taken from the left spine, where they
    # already are.
    case 1n+p False{} _ _:
      +pf = p
      +px : T.Ex = x
      +py : T.Ex = y
      +hd = spine_hd(256n, is_ex(st), px)
      +cmi = R.get(Meta, 32n, mt, const_nm2(hd), MNone{})
      # The inductive must be a registered STRUCTURE -- one constructor,
      # no indices -- which is what `MInd` means here. That restriction is
      # the whole safety of this rule: `bugs`-side `111_indexedUnitEta` and
      # `113_indexedStructEta` are eta applied to *indexed* families, where
      # it does not hold.
      #
      # Zero fields is allowed and is the unit-like case: every element of a
      # no-field structure equals its constructor.
      +eok = meta_is_ctor(cmi)
             && meta_is_ind(R.get(Meta, 32n, mt, meta_ind(cmi), MNone{}))
      +ahd = alloc_ex(st, hd)
      +pre = app_build(64n,
                       take_u(spine_ar(256n, is_ex(ir_st(ahd)), px, Nil{}),
                              meta_p(cmi), Nil{}),
                       ir_st(ahd), ir_ty(ahd))
      +ay = alloc_ex(ir_st(pre), py)
      +eta = proj_build(U32.to_nat(meta_nf(cmi)), 0, meta_ind(cmi),
                        ir_ty(ay), ir_st(ay), ir_ty(pre))
      +se : IS = ir_st(eta)
      +de = defeq(pf, False{}, se, mt, nt, lp, vt, ctx, px,
                  U.ex_at(is_ex(se), ir_ty(eta)))
      pick_dr(eok, DR{dr_st(de), soften(dr_r(de))},
              DR{st, mismatch(px, py)})


# Argument-versus-domain equality, cheapest first: structural, then one
# `whd` per side and structural again, then `defeq`. See the long note at the
# application rule in `infer` for why reducing here is needed at all, and
# docs/measurements.md for the cost of each tier.
def arg_eq2(+mid: L.Tri, +fuel: Nat, +st: IS, +mt: R.Tr<Meta>,
            +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
            +ctx: List<&2, U32>, +xi: U32, +yi: U32) -> DR:
  match mid:
    case L.TYes{}:
      DR{st, L.TYes{}}
    case _:
      defeq(fuel, U32.is_eq(xi, yi), st, mt, nt, lp, vt, ctx,
            U.ex_at(is_ex(st), xi), U.ex_at(is_ex(st), yi))

def arg_eq(+cheap: L.Tri, +fuel: Nat, +st: IS, +mt: R.Tr<Meta>,
           +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
           +ctx: List<&2, U32>, +xi: U32, +yi: U32) -> DR:
  match cheap:
    case L.TYes{}:
      DR{st, L.TYes{}}
    case _:
      +w1 = whd(st, mt, lp, vt, xi)
      +w2 = whd(ir_st(w1), mt, lp, vt, yi)
      +s2 : IS = ir_st(w2)
      arg_eq2(eq_ex(256n, U32.is_eq(ir_ty(w1), ir_ty(w2)), is_ex(s2),
                    is_lnt(s2), U.ex_at(is_ex(s2), ir_ty(w1)),
                    U.ex_at(is_ex(s2), ir_ty(w2))),
              fuel, s2, mt, nt, lp, vt, ctx, ir_ty(w1), ir_ty(w2))

# --- infer ---------------------------------------------------------------
# One self-recursive function. The application case is the reason accessor
# defs exist above: after normalising the function's type there is no way to
# *match* on whether it is a Pi, because the normalised node is a computed
# value, so `is_all`, `all_dom` and `all_cod` are consulted instead.
#
# Argument equality uses the structural comparison, which answers TYes or
# TUnk and never TNo, so an application whose argument type is not
# syntactically recognisable comes back "cannot infer" rather than wrong.
def infer(+fuel: Nat, +s: IS, +mt: R.Tr<Meta>, +nt: R.Tr<U32>,
          +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +x: T.Ex, +e: U32,
          +ctx: List<&2, U32>) -> IR:
  match fuel x:
    case 0n _:
      ir_bad(s)
    case 1n+p T.ESort{l}:
      sort_of(s, L.ln_succ(R.get(L.LN, 32n, is_lnt(s), l, L.LNun{})))
    # `infer (forall x:A, B) = Sort (imax (univ A) (univ B))`, with each
    # universe obtained by inferring and reducing rather than by `sl`, which
    # has no rule for applications and so failed on any Pi with one in it.
    case 1n+p T.EAll{n, ty, b, bi}:
      +pf = p
      +pty = ty
      +ra = infer(pf, s, mt, nt, lp, vt, U.ex_at(is_ex(s), pty), pty, ctx)
      +wa = whd(ir_st(ra), mt, lp, vt, ir_ty(ra))
      +sa = ir_st(wa)
      +ka = U.ex_at(is_ex(sa), ir_ty(wa))
      +rb = infer(pf, sa, mt, nt, lp, vt, U.ex_at(is_ex(sa), b), b,
                  Con{pty, ctx})
      +wb = whd(ir_st(rb), mt, lp, vt, ir_ty(rb))
      +sb = ir_st(wb)
      +kb = U.ex_at(is_ex(sb), ir_ty(wb))
      pick_ir(ir_ok(ra) && ir_ok(rb) && is_sortx(ka) && is_sortx(kb),
              sort_of(sb,
                      L.ln_imax(R.get(L.LN, 32n, is_lnt(sb),
                                      sort_lvl_of(ka), L.LNun{}),
                                R.get(L.LN, 32n, is_lnt(sb),
                                      sort_lvl_of(kb), L.LNun{}))),
              ir_bad(sb))
    case 1n+p T.ELam{n, ty, b, bi}:
      +pf = p
      +pty = ty
      +rb = infer(pf, s, mt, nt, lp, vt, U.ex_at(is_ex(s), b), b,
                  Con{pty, ctx})
      pick_ir(ir_ok(rb),
              alloc_ex(ir_st(rb), T.EAll{n, pty, ir_ty(rb), bi}),
              ir_bad(ir_st(rb)))
    case 1n+p T.EBVar{i}:
      +ti = nth_u(ctx, i, 4294967295)
      +sr = U.lift(256n, is_ex(s), is_nx(s), U.ex_at(is_ex(s), ti), ti, 0,
                   (i + 1 : U32))
      IR{IS{U.sr_t(sr), U.sr_nx(sr), is_lnt(s), is_nlx(s), is_wm(s), is_ht(s), is_natn(s), is_strn(s), is_qt_t(s)}, U.sr_i(sr),
         U32.is_ne(ti, 4294967295)}
    # A literal's type is the constant `Nat` or `String`. Without this,
    # `infer` had no case for literals at all and answered BAD.
    case 1n+p T.ENat{d}:
      pick_ir(U32.is_eq(is_natn(s), 4294967295), ir_bad(s),
              alloc_ex(s, T.EConst{is_natn(s), Nil{}}))
    case 1n+p T.EStr{d}:
      pick_ir(U32.is_eq(is_strn(s), 4294967295), ir_bad(s),
              alloc_ex(s, T.EConst{is_strn(s), Nil{}}))
    case 1n+p T.EConst{n, us}:
      +ti = R.get(U32, 32n, nt, n, 4294967295)
      pick_ir(U32.is_eq(ti, 4294967295), ir_bad(s),
              lsubst(256n, s, U.ex_at(is_ex(s), ti), ti,
                     R.get(List<&2, U32>, 32n, lp, n, Nil{}),
                     lns_of(us, is_lnt(s))))
    case 1n+p T.ELet{n, ty, v, b}:
      +pf = p
      +rz = U.inst(256n, is_ex(s), is_nx(s), U.ex_at(is_ex(s), b), b, 0, v)
      +s2 : IS = IS{U.sr_t(rz), U.sr_nx(rz), is_lnt(s), is_nlx(s), is_wm(s), is_ht(s), is_natn(s), is_strn(s), is_qt_t(s)}
      infer(pf, s2, mt, nt, lp, vt, U.ex_at(is_ex(s2), U.sr_i(rz)),
            U.sr_i(rz), ctx)
    case 1n+p T.EApp{f, a} :
      +pf = p
      +pa = a
      +rf = infer(pf, s, mt, nt, lp, vt, U.ex_at(is_ex(s), f), f, ctx)
      +w = whnf(256n, True{}, ir_st(rf), mt, lp, vt,
                U.ex_at(is_ex(ir_st(rf)), ir_ty(rf)), ir_ty(rf), Nil{})
      +s2 : IS = ir_st(w)
      +node = U.ex_at(is_ex(s2), ir_ty(w))
      +ra = infer(pf, s2, mt, nt, lp, vt, U.ex_at(is_ex(s2), pa), pa, ctx)
      # Argument equality is STRUCTURAL, and that is a known limitation
      # rather than an oversight. `eq_ex` answers TYes or TUnk and never
      # TNo, so an application whose argument type is not syntactically
      # recognisable comes back "cannot infer" rather than wrong.
      #
      # What it cannot do is accept a recursor application. Every minor
      # premise's domain mentions `motive (c ..)`, which once the motive is
      # substituted is a beta-redex, so it matches the argument's type only
      # after reduction -- and a recursor's second argument has domain
      # `motive N.zero` = `(fun _ => N -> N) N.zero`, an application,
      # against an argument type that is already a Pi. So `N.add`, `count`,
      # `Nat.below`, `Nat.brecOn`, every `*.match_1` and `*._f` and
      # everything built on them decline: about 40 declining declarations,
      # the largest single cluster.
      #
      # Reducing here fixes all of them, and was measured three ways:
      # `defeq` alone, a `whd`-then-retry tier, and both behind a cheap
      # structural pre-test. Every version scored *exactly* 104/205 -- the
      # same as this one -- while turning declines into timeouts
      # (`grind-ring-5` 24 s -> 77 s against 60 s, `magma-string-n4`
      # 45 s -> 82 s against 70 s, plus `fueled-chain`). The reason it buys
      # no test is that every file in the cluster also has a theorem whose
      # check needs `defeq` to *prove* an equality, which it still cannot
      # do. Reduction here is the second half of that fix, so it belongs
      # with the first half, not before it. See docs/measurements.md.
      +ex2 = is_ex(ir_st(ra))
      +dq = arg_eq(eq_ex(256n, U32.is_eq(ir_ty(ra), all_dom(node)), ex2,
                         is_lnt(ir_st(ra)), U.ex_at(ex2, ir_ty(ra)),
                         U.ex_at(ex2, all_dom(node))),
                   24n, ir_st(ra), mt, nt, lp, vt, ctx, ir_ty(ra),
                   all_dom(node))
      +sd : IS = dr_st(dq)
      +rz = U.inst(256n, is_ex(sd), is_nx(sd),
                   U.ex_at(is_ex(sd), all_cod(node)), all_cod(node), 0, pa)
      IR{IS{U.sr_t(rz), U.sr_nx(rz), is_lnt(sd), is_nlx(sd), is_wm(sd), is_ht(sd), is_natn(sd), is_strn(sd), is_qt_t(sd)},
         U.sr_i(rz),
         ir_ok(rf) && ir_ok(ra) && is_all(node)
         && L.tri_is_yes(dr_r(dq))}
    # `s.i` has the (i+1)-th field type of the structure's constructor, with
    # the parameters and the earlier fields substituted.
    case 1n+p T.EProj{tn, idx, sx}:
      +pf = p
      +pidx = idx
      +ptn = tn
      +rs = infer(pf, s, mt, nt, lp, vt, U.ex_at(is_ex(s), sx), sx, ctx)
      +ws = whd(ir_st(rs), mt, lp, vt, ir_ty(rs))
      +sst = ir_st(ws)
      +sty = U.ex_at(is_ex(sst), ir_ty(ws))
      +mi = R.get(Meta, 32n, mt, ptn, MNone{})
      +ok = ir_ok(rs) && meta_is_ind(mi)
            && U32.is_lt(pidx, meta_nf(mi))
            && U32.is_eq(const_nm2(spine_hd(256n, is_ex(sst), sty)), ptn)
      # `spine_ar` already returns the arguments left to right, which is the
      # order the constructor binds its parameters in, so no reversal.
      # The constructor's type is read under the STRUCTURE's level
      # arguments. Without this the field type comes back carrying the
      # inductive's own level parameters instead of the instance's, and the
      # levels no longer match: `089_projProp1` projects field 0 of a
      # six-field Prop structure whose fields have six different `PUnit`
      # levels, and the arena pairs each index with its correct level in a
      # `good` test and with a wrong one in a `bad` test. Getting the
      # substitution wrong fails both directions at once.
      +lsr = lsubst(256n, sst, U.ex_at(is_ex(sst), meta_cty(mi)),
                    meta_cty(mi),
                    R.get(List<&2, U32>, 32n, lp, ptn, Nil{}),
                    lns_of(sl_const_us(spine_hd(256n, is_ex(sst), sty)),
                           is_lnt(sst)))
      +pn = proj_nodes(U32.to_nat(pidx), 0, ptn, sx, ir_st(lsr), Nil{})
      +pt = peel_tele(256n, ls_st(pn), ir_ty(lsr),
                      List.append(&2, U32,
                                  spine_ar(256n, is_ex(ls_st(pn)), sty,
                                           Nil{}),
                                  ls_xs(pn)))
      # What is left is the Pi whose domain is the field's type. The node is
      # bound once: a `+` binding is inlined at every use, so naming it
      # three times would rebuild the whole peel three times.
      +pnode : T.Ex = U.ex_at(is_ex(ir_st(pt)), ir_ty(pt))
      # Projecting out of a PROP structure is legal only when the field's own
      # type is a proposition. Otherwise the projection would extract a
      # Type-valued component from a proof, and proof irrelevance makes all
      # proofs of it equal -- so the component could be anything.
      #
      # The arena pins this down with six near-identical files.
      # `PropStructure : Prop` has six `PUnit.{...}` fields, and `PUnit.{0}`
      # is a Prop while `PUnit.{u}` for a parameter is not: `089_projProp1`
      # and `091_projProp3` project the Prop-valued fields and must be
      # ACCEPTED, while `090`, `092` and `094` project the others and must
      # not. The two directions fail together, so neither a blanket ban nor
      # a blanket allowance passes.
      +fldty : U32 = all_dom(pnode)
      +fldprop = L.tri_is_yes(L.ln_is_zero(sl(256n, is_ex(ir_st(pt)),
                                              is_lnt(ir_st(pt)), nt, lp,
                                              U.ex_at(is_ex(ir_st(pt)),
                                                      fldty), ctx)))
      # Back to the conservative gate: no projection out of a possibly-Prop
      # structure at all. "The field's type must be a Prop" is NOT the rule
      # -- see docs/measurements.md for the six-file table that disproves it
      # -- and shipping it produced a WRONG ACCEPT on `094_projProp6`.
      # Declining all six is the honest answer until the rule is known.
      # Projecting out of a PROP structure, by the rule the arena states in
      # its own test descriptions:
      #
      #   "The lean kernel allows projections out of propositions if they
      #    precede all dependent data fields. Non-dependent data fields are
      #    not relevant."
      #   "...rejects any projections out of a proposition that come after a
      #    dependent data field, even if that is not used by the present
      #    projection."
      #
      # So two conditions: the field taken must itself be a proof -- a data
      # projection out of a proposition is never allowed -- and its index
      # must precede every DEPENDENT data field, meaning a data field that
      # some later field's type mentions. `ppx` carries that bound, computed
      # where the field types are already being walked.
      #
      # The arena's six `projProp` files pin this down exactly: fields are
      # Prop, data, Prop, data, Prop-depending-on-field-3, Prop, and the
      # first dependent data field is 3 -- so 0 and 2 are accepted and
      # 1, 3, 4, 5 are not. Three simpler rules each get at least one of
      # those wrong; see docs/measurements.md.
      +ri : IR = IR{ir_st(pt), fldty,
                    ir_ok(pt) && is_all(pnode)
                    && (U32.is_eq(meta_pr(mi), 0)
                        || (fldprop && U32.is_lt(pidx, meta_ppx(mi))))}
      # GATED OFF for performance, on the same grounds as iota. With this
      # on, `perf/magma-string-n4` and `perf/magma-string-pair-n9` TIMED OUT
      # (70 s and 130 s against their limits), turning two declines into two
      # errors -- and it bought no tests. The typing itself is correct and
      # restricted properly; it is the cost of running `infer` on the
      # structure, plus a telescope walk, at every projection, with nothing
      # memoised.
      # Off, on measurement. The typing is right and the Prop restriction
      # (via `large_elim`, the subsingleton condition) is right, but running
      # `infer` on the structure plus a telescope walk at every projection
      # costs three timeouts and buys nothing: the projection tests still
      # decline, because what blocks them is upstream of here.
      pick_ir(ok, ri, ir_bad(ir_st(ri)))
    case 1n+p _:
      ir_bad(s)
