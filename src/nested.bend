# Recursors of mutual and nested inductive blocks, derived the way Lean's
# kernel derives them and compared with the export's.
#
# The algorithm is tools/recref.py (validated against every mutual and
# nested block of init-prelude, std, con-leche and cedar: all recursor types
# and rules equal, structurally). It is locally nameless: parameters,
# motives, minor premises, fields and index variables are FRESH CONSTANTS
# (names from FVB up), and binders are made by abstracting them at the end.
# No de Bruijn arithmetic by hand.
#
#   specs   the block's own types, then every nested occurrence `J As` of
#           an external inductive J whose parameters As mention the block,
#           discovered breadth-first through constructor fields (Lean's
#           auxiliary types, in Lean's order)
#   motives one per spec:  motive_j : (indices) -> (t : spec_j indices) -> Sort v
#   minors  one per constructor of each spec, in spec order: fields (their
#           types with optParam/autoParam/outParam annotations dropped),
#           then an IH for every field whose type -- in whnf at each Pi --
#           ends in a spec
#   rec_j   params, motives, minors, spec_j's indices, the major premise
#   rule    rec_j on constructor c:  fun params motives minors fields =>
#           minor_c fields (fun zs => rec_k params motives minors idx (f zs))

import Base
import ./scan.bend as S
import ./term.bend as T
import ./level.bend as L
import ./trie.bend as R
import ./subst.bend as U
import ./decode.bend as D
import ./infer.bend as I
import ./store.bend as K
import ./recursor.bend as W

def fvb() -> U32:
  4026531840

def mem(+v: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{head, tail}:
      U32.is_eq(head, v) || mem(v, tail)

def is_fv(+n: U32) -> Bool:
  U32.is_ge(n, fvb())

# --- the state record: store, fresh counter, a result index -------------
type NR is Data:
  NR{st: I.IS, kc: U32, x: U32}

def nr_st(+r: NR) -> I.IS:
  match r:
    case NR{st, kc, x}:
      st

def nr_kc(+r: NR) -> U32:
  match r:
    case NR{st, kc, x}:
      kc

def nr_x(+r: NR) -> U32:
  match r:
    case NR{st, kc, x}:
      x

def nr_of(+r: I.IR, +kc: U32) -> NR:
  NR{I.ir_st(r), kc, I.ir_ty(r)}

def ex_of(+st: I.IS) -> R.Tr<T.Ex>:
  I.is_ex(st)

def node(+st: I.IS, +i: U32) -> T.Ex:
  U.ex_at(I.is_ex(st), i)

# a subst.bend result back into the inference state
def st_of_sr(+st: I.IS, +r: U.SR) -> I.IS:
  I.IS{U.sr_t(r), U.sr_nx(r), I.is_lnt(st), I.is_nlx(st), I.is_wm(st),
       I.is_ht(st), I.is_natn(st), I.is_strn(st), I.is_qt_t(st)}

# body with its bound variable 0 replaced by v
def inst0(+st: I.IS, +b: U32, +v: U32) -> I.IR:
  +r = U.inst(256n, I.is_ex(st), I.is_nx(st), node(st, b), b, 0, v)
  I.IR{st_of_sr(st, r), U.sr_i(r), True{}}

# --- free variables ------------------------------------------------------
# A free variable is listed as the flat triple [name, node, type].
def fv_new(+st: I.IS, +kc: U32) -> NR:
  +r = I.alloc_ex(st, T.EConst{(fvb() + kc : U32), Nil{}})
  NR{I.ir_st(r), (kc + 1 : U32), I.ir_ty(r)}

# Peel up to `n` Pi binders of `ty`, each instantiated with a fresh free
# variable. Returns the free variables (outermost first) and what is left.
type TL is Data:
  TL{st: I.IS, kc: U32, fvs: List<&2, U32>, ty: U32}

def tl_st(+r: TL) -> I.IS:
  match r:
    case TL{st, kc, fvs, ty}:
      st

def tl_kc(+r: TL) -> U32:
  match r:
    case TL{st, kc, fvs, ty}:
      kc

def tl_fvs(+r: TL) -> List<&2, U32>:
  match r:
    case TL{st, kc, fvs, ty}:
      fvs

def tl_ty(+r: TL) -> U32:
  match r:
    case TL{st, kc, fvs, ty}:
      ty

# `go` = more binders wanted; `nd` = the node of `ty`
def tele_go(fuel: Nat, +go: Bool, +st: I.IS, +kc: U32, +ty: U32, +n: U32,
            +acc: List<&2, U32>, +nd: T.Ex) -> TL:
  match fuel go nd:
    case 0n _ _:
      TL{st, kc, I.rev_u(acc, Nil{}), ty}
    case 1n+p False{} _:
      TL{st, kc, I.rev_u(acc, Nil{}), ty}
    case 1n+p True{} T.EAll{nm, d, b, bi}:
      +f = fv_new(st, kc)
      +bd = inst0(nr_st(f), b, nr_x(f))
      +n2 : U32 = (n - 1 : U32)
      # `acc` is reversed: [type, node, name] per variable
      tele_go(p, U32.is_ne(n2, 0), I.ir_st(bd), nr_kc(f), I.ir_ty(bd), n2,
              Con{d, Con{nr_x(f), Con{(fvb() + kc : U32), acc}}},
              node(I.ir_st(bd), I.ir_ty(bd)))
    case 1n+p True{} _:
      TL{st, kc, I.rev_u(acc, Nil{}), ty}

# all binders (n = "infinite")
def tele(+st: I.IS, +kc: U32, +ty: U32) -> TL:
  tele_go(512n, True{}, st, kc, ty, 4294967295, Nil{}, node(st, ty))

def tele_n(+st: I.IS, +kc: U32, +ty: U32, +n: U32) -> TL:
  tele_go(512n, U32.is_ne(n, 0), st, kc, ty, n, Nil{}, node(st, ty))

# the k-th name / node / type of a flat fv list
def fv_names(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{a, Con{b, Con{c, t}}}:
      fv_names(t, Con{a, acc})
    case _:
      I.rev_u(acc, Nil{})

def fv_nodes(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{a, Con{b, Con{c, t}}}:
      fv_nodes(t, Con{b, acc})
    case _:
      I.rev_u(acc, Nil{})

# --- abstraction: the free variable `nm` becomes bound variable `d` ------
def abst(+fuel: Nat, +st: I.IS, +x: T.Ex, +e: U32, +nm: U32,
         +d: U32) -> I.IR:
  match fuel x:
    case 0n _:
      I.keep_ir(st, e)
    case 1n+p T.EConst{n, us}:
      I.pick_ir(U32.is_eq(n, nm), I.alloc_ex(st, T.EBVar{d}),
                I.keep_ir(st, e))
    case 1n+p T.EApp{f, a}:
      +pf = p
      +r1 = abst(pf, st, node(st, f), f, nm, d)
      +r2 = abst(pf, I.ir_st(r1), node(I.ir_st(r1), a), a, nm, d)
      I.pick_ir(U32.is_eq(I.ir_ty(r1), f) && U32.is_eq(I.ir_ty(r2), a),
                I.keep_ir(I.ir_st(r2), e),
                I.alloc_ex(I.ir_st(r2), T.EApp{I.ir_ty(r1), I.ir_ty(r2)}))
    case 1n+p T.ELam{n, ty, b, bi}:
      +pf = p
      +r1 = abst(pf, st, node(st, ty), ty, nm, d)
      +r2 = abst(pf, I.ir_st(r1), node(I.ir_st(r1), b), b, nm, (d + 1 : U32))
      I.pick_ir(U32.is_eq(I.ir_ty(r1), ty) && U32.is_eq(I.ir_ty(r2), b),
                I.keep_ir(I.ir_st(r2), e),
                I.alloc_ex(I.ir_st(r2), T.ELam{n, I.ir_ty(r1), I.ir_ty(r2), bi}))
    case 1n+p T.EAll{n, ty, b, bi}:
      +pf = p
      +r1 = abst(pf, st, node(st, ty), ty, nm, d)
      +r2 = abst(pf, I.ir_st(r1), node(I.ir_st(r1), b), b, nm, (d + 1 : U32))
      I.pick_ir(U32.is_eq(I.ir_ty(r1), ty) && U32.is_eq(I.ir_ty(r2), b),
                I.keep_ir(I.ir_st(r2), e),
                I.alloc_ex(I.ir_st(r2), T.EAll{n, I.ir_ty(r1), I.ir_ty(r2), bi}))
    case 1n+p T.ELet{n, ty, v, b}:
      +pf = p
      +r1 = abst(pf, st, node(st, ty), ty, nm, d)
      +r2 = abst(pf, I.ir_st(r1), node(I.ir_st(r1), v), v, nm, d)
      +r3 = abst(pf, I.ir_st(r2), node(I.ir_st(r2), b), b, nm, (d + 1 : U32))
      I.pick_ir(U32.is_eq(I.ir_ty(r1), ty) && U32.is_eq(I.ir_ty(r2), v)
                && U32.is_eq(I.ir_ty(r3), b),
                I.keep_ir(I.ir_st(r3), e),
                I.alloc_ex(I.ir_st(r3),
                           T.ELet{n, I.ir_ty(r1), I.ir_ty(r2), I.ir_ty(r3)}))
    case 1n+p T.EProj{tn, i, sx}:
      +pf = p
      +r1 = abst(pf, st, node(st, sx), sx, nm, d)
      I.pick_ir(U32.is_eq(I.ir_ty(r1), sx), I.keep_ir(I.ir_st(r1), e),
                I.alloc_ex(I.ir_st(r1), T.EProj{tn, i, I.ir_ty(r1)}))
    case 1n+p _:
      I.keep_ir(st, e)

def bind_node(+lam: Bool, +ty: U32, +b: U32) -> T.Ex:
  match lam:
    case True{}:
      T.ELam{0, ty, b, 0}
    case False{}:
      T.EAll{0, ty, b, 0}

# Bind the variables (flat triples, outermost first) around `body`:
# Pi (lam = False) or lambda (lam = True). Innermost first.
def bind_rev(rev: List<&2, U32>, +st: I.IS, +body: U32,
             +lam: Bool) -> I.IR:
  match rev:
    case Con{ty, Con{nd, Con{nm, t}}}:
      +b2 = abst(1024n, st, node(st, body), body, nm, 0)
      +r = I.alloc_ex(I.ir_st(b2),
                      bind_node(lam, ty, I.ir_ty(b2)))
      bind_rev(t, I.ir_st(r), I.ir_ty(r), lam)
    case _:
      I.keep_ir(st, body)

def mk_pi(+fvs: List<&2, U32>, +st: I.IS, +body: U32) -> I.IR:
  bind_rev(I.rev_u(fvs, Nil{}), st, body, False{})

def mk_lam(+fvs: List<&2, U32>, +st: I.IS, +body: U32) -> I.IR:
  bind_rev(I.rev_u(fvs, Nil{}), st, body, True{})

# --- structure ------------------------------------------------------------
def spine_hd(+st: I.IS, +x: U32) -> T.Ex:
  I.spine_hd(256n, I.is_ex(st), node(st, x))

def spine_go(fuel: Nat, +st: I.IS, +nd: T.Ex,
             +acc: List<&2, U32>) -> List<&2, U32>:
  match fuel nd:
    case 0n _:
      acc
    case 1n+p T.EApp{f, a}:
      spine_go(p, st, node(st, f), Con{a, acc})
    case 1n+p _:
      acc

def spine_args(+st: I.IS, +x: U32) -> List<&2, U32>:
  spine_go(256n, st, node(st, x), Nil{})

def const_us(+x: T.Ex) -> List<&2, U32>:
  match x:
    case T.EConst{n, us}:
      us
    case _:
      Nil{}

# levels equal by normal form
def lvls_eq(+lnt: R.Tr<L.LN>, xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{a, at} Con{b, bt}:
      L.tri_is_yes(L.ln_cmp(R.get(L.LN, 64n, lnt, a, L.LNun{}),
                            R.get(L.LN, 64n, lnt, b, L.LNun{})))
      && lvls_eq(lnt, at, bt)
    case _ _:
      False{}

# alpha-equivalence (binder names and info ignored), levels by normal form;
# x, y are the nodes of a, b
def ex_eq(+fuel: Nat, +st: I.IS, +a: U32, +b: U32, +x: T.Ex,
          +y: T.Ex) -> Bool:
  match fuel x y:
    case 0n _ _:
      U32.is_eq(a, b)
    case 1n+p T.EBVar{i} T.EBVar{j}:
      U32.is_eq(i, j)
    case 1n+p T.ESort{l} T.ESort{m}:
      L.tri_is_yes(L.ln_cmp(R.get(L.LN, 64n, I.is_lnt(st), l, L.LNun{}),
                            R.get(L.LN, 64n, I.is_lnt(st), m, L.LNun{})))
    case 1n+p T.EConst{n, us} T.EConst{m, vs}:
      U32.is_eq(n, m) && lvls_eq(I.is_lnt(st), us, vs)
    case 1n+p T.EApp{f, a1} T.EApp{g, b1}:
      U32.is_eq(a, b)
      || ex_eq(p, st, f, g, node(st, f), node(st, g))
         && ex_eq(p, st, a1, b1, node(st, a1), node(st, b1))
    case 1n+p T.ELam{n, t, b1, bi} T.ELam{m, u, c, b2}:
      U32.is_eq(a, b)
      || ex_eq(p, st, t, u, node(st, t), node(st, u))
         && ex_eq(p, st, b1, c, node(st, b1), node(st, c))
    case 1n+p T.EAll{n, t, b1, bi} T.EAll{m, u, c, b2}:
      U32.is_eq(a, b)
      || ex_eq(p, st, t, u, node(st, t), node(st, u))
         && ex_eq(p, st, b1, c, node(st, b1), node(st, c))
    case 1n+p T.ELet{n, t, v, b1} T.ELet{m, u, w, c}:
      U32.is_eq(a, b)
      || ex_eq(p, st, t, u, node(st, t), node(st, u))
         && ex_eq(p, st, v, w, node(st, v), node(st, w))
         && ex_eq(p, st, b1, c, node(st, b1), node(st, c))
    case 1n+p T.EProj{tn, i, s1} T.EProj{t2, j, s2}:
      U32.is_eq(tn, t2) && U32.is_eq(i, j)
      && ex_eq(p, st, s1, s2, node(st, s1), node(st, s2))
    case 1n+p T.ENat{d} T.ENat{e}:
      I.eq_u32s(d, e)
    case 1n+p T.EStr{d} T.EStr{e}:
      I.eq_u32s(d, e)
    case 1n+p _ _:
      False{}

def ex_eqi(+st: I.IS, +a: U32, +b: U32) -> Bool:
  ex_eq(4096n, st, a, b, node(st, a), node(st, b))

def exs_eq(+st: I.IS, xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{a, at} Con{b, bt}:
      ex_eqi(st, a, b) && exs_eq(st, at, bt)
    case _ _:
      False{}

# does any constant named in `ns` occur?
def occurs(+fuel: Nat, +st: I.IS, +nd: T.Ex, +ns: List<&2, U32>) -> Bool:
  match fuel nd:
    case 0n _:
      True{}
    case 1n+p T.EConst{n, us}:
      mem(n, ns)
    case 1n+p T.EApp{f, a}:
      occurs(p, st, node(st, f), ns) || occurs(p, st, node(st, a), ns)
    case 1n+p T.ELam{n, t, b, bi}:
      occurs(p, st, node(st, t), ns) || occurs(p, st, node(st, b), ns)
    case 1n+p T.EAll{n, t, b, bi}:
      occurs(p, st, node(st, t), ns) || occurs(p, st, node(st, b), ns)
    case 1n+p T.ELet{n, t, v, b}:
      occurs(p, st, node(st, t), ns) || occurs(p, st, node(st, v), ns)
      || occurs(p, st, node(st, b), ns)
    case 1n+p T.EProj{tn, i, s}:
      occurs(p, st, node(st, s), ns)
    case 1n+p _:
      False{}

def occursi(+st: I.IS, +x: U32, +ns: List<&2, U32>) -> Bool:
  occurs(4096n, st, node(st, x), ns)

# Lean's consume_type_annotations: optParam/autoParam (two arguments) and
# outParam/semiOutParam (one) wrappers dropped at the head. `ann` =
# [optParam, autoParam, outParam, semiOutParam] name indices.
def ann_one(+st: I.IS, +x: U32, +ann: List<&2, U32>) -> Bool:
  +h : U32 = I.const_nm2(spine_hd(st, x))
  +n2 : U32 = I.len_u(spine_args(st, x), 0)
  (U32.is_eq(h, I.nth_u(ann, 0, 4294967294))
   || U32.is_eq(h, I.nth_u(ann, 1, 4294967294))) && U32.is_eq(n2, 2)
  || (U32.is_eq(h, I.nth_u(ann, 2, 4294967294))
      || U32.is_eq(h, I.nth_u(ann, 3, 4294967294))) && U32.is_eq(n2, 1)

def strip_go(fuel: Nat, +z: Bool, +st: I.IS, +x: U32,
             +ann: List<&2, U32>) -> U32:
  match fuel z:
    case 0n _:
      x
    case 1n+p False{}:
      x
    case 1n+p True{}:
      +inner : U32 = I.nth_u(spine_args(st, x), 0, x)
      strip_go(p, ann_one(st, inner, ann), st, inner, ann)

def strip_ann(+st: I.IS, +x: U32, +ann: List<&2, U32>) -> U32:
  strip_go(16n, ann_one(st, x, ann), st, x, ann)


# =========================================================================
# The derivation
# =========================================================================
type SP is Data:
  SP{n: U32, us: List<&2, U32>, ps: List<&2, U32>}

def sp_n(+s: SP) -> U32:
  match s:
    case SP{n, us, ps}:
      n

def sp_us(+s: SP) -> List<&2, U32>:
  match s:
    case SP{n, us, ps}:
      us

def sp_ps(+s: SP) -> List<&2, U32>:
  match s:
    case SP{n, us, ps}:
      ps

def pick_sp(+z: Bool, +a: SP, +b: SP) -> SP:
  match z:
    case True{}:
      a
    case False{}:
      b

def nth_sp(xs: List<&2, SP>, +i: U32) -> SP:
  match xs:
    case Nil{}:
      SP{4294967295, Nil{}, Nil{}}
    case Con{h, t}:
      pick_sp(U32.is_eq(i, 0), h, nth_sp(t, (i - 1 : U32)))

def len_sp(xs: List<&2, SP>, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      len_sp(t, (acc + 1 : U32))

# --- inductive / constructor lookup ---------------------------------------
# this block's items first, then the tables of earlier blocks
def pick_item(+z: Bool, +a: K.IItem, +b: K.IItem) -> K.IItem:
  match z:
    case True{}:
      a
    case False{}:
      b

def find_ind(items: List<&2, K.IItem>, +n: U32) -> K.IItem:
  match items:
    case Nil{}:
      K.IOther{}
    case Con{K.IInd{nm, lps, ty, np, ni, nn, cs}, t}:
      +n2 : U32 = nm
      pick_item(U32.is_eq(n2, n), K.IInd{n2, lps, ty, np, ni, nn, cs},
                find_ind(t, n))
    case Con{h, t}:
      find_ind(t, n)

def is_iother(+x: K.IItem) -> Bool:
  match x:
    case K.IOther{}:
      True{}
    case _:
      False{}

def ind_of(+items: List<&2, K.IItem>, +itab: R.Tr<K.IItem>,
           +n: U32) -> K.IItem:
  +own = find_ind(items, n)
  pick_item(is_iother(own), R.get(K.IItem, 64n, itab, n, K.IOther{}), own)

def ii_lps(+x: K.IItem) -> List<&2, U32>:
  match x:
    case K.IInd{nm, lps, ty, np, ni, nn, cs}:
      lps
    case _:
      Nil{}

def ii_ty(+x: K.IItem) -> U32:
  match x:
    case K.IInd{nm, lps, ty, np, ni, nn, cs}:
      ty
    case _:
      4294967295

def ii_np(+x: K.IItem) -> U32:
  match x:
    case K.IInd{nm, lps, ty, np, ni, nn, cs}:
      np
    case _:
      0

def ii_cs(+x: K.IItem) -> List<&2, U32>:
  match x:
    case K.IInd{nm, lps, ty, np, ni, nn, cs}:
      cs
    case _:
      Nil{}

def ii_is(+x: K.IItem) -> Bool:
  match x:
    case K.IInd{nm, lps, ty, np, ni, nn, cs}:
      True{}
    case _:
      False{}

# a constructor's declared type: this block's, else the table's
def find_ctor_ty(items: List<&2, K.IItem>, +c: U32) -> U32:
  match items:
    case Nil{}:
      4294967295
    case Con{K.ICtor{nm, lps, ty, ind, np, nf, ci}, t}:
      S.pick(U32.is_eq(nm, c), ty, find_ctor_ty(t, c))
    case Con{h, t}:
      find_ctor_ty(t, c)

def ctor_ty(+items: List<&2, K.IItem>, +ctab: R.Tr<U32>, +c: U32) -> U32:
  +own : U32 = find_ctor_ty(items, c)
  S.pick(U32.is_eq(own, 4294967295), R.get(U32, 64n, ctab, c, 4294967295),
         own)

# --- instantiation --------------------------------------------------------
def lnfs(us: List<&2, U32>, +lnt: R.Tr<L.LN>) -> List<&2, L.LN>:
  match us:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{R.get(L.LN, 64n, lnt, h, L.LNun{}), lnfs(t, lnt)}

# the leading Pi binders of `ty` instantiated with `ps`, in order
def inst_ps(ps: List<&2, U32>, +st: I.IS, +ty: U32, +nd: T.Ex) -> I.IR:
  match ps nd:
    case Nil{} _:
      I.keep_ir(st, ty)
    case Con{p, t} T.EAll{nm, d, b, bi}:
      +r = inst0(st, b, p)
      inst_ps(t, I.ir_st(r), I.ir_ty(r), node(I.ir_st(r), I.ir_ty(r)))
    case _ _:
      I.IR{st, 4294967295, False{}}

# a declared type (with level params `lps`) at spec levels `us`, its first
# binders instantiated with `ps`
def at_spec(+st: I.IS, +ty: U32, +lps: List<&2, U32>, +us: List<&2, U32>,
            +ps: List<&2, U32>) -> I.IR:
  +r = I.lsubst(256n, st, node(st, ty), ty, lps, lnfs(us, I.is_lnt(st)))
  inst_ps(ps, I.ir_st(r), I.ir_ty(r), node(I.ir_st(r), I.ir_ty(r)))

# Pi telescope with whnf at every step (Lean's is_rec_argument)
# --- K-like reduction with the indices compared by defeq ---------------------
# The oracle's whnf (I.whd) reduces a K-like recursor only when the given
# indices are SYNTACTICALLY the constructor's. Lean's to_cnstr_when_K
# compares the major's type with the constructor's by is_def_eq, so a
# field type `Gate.rec .. h ..` whose indices only reduce to the
# constructor's (bugs/rec-missing-ih: `Owner.step`'s third field mentions
# `Owner` under such a recursor, and the indices agree only by proof
# irrelevance) stayed stuck here, read as an invalid occurrence, and the
# block's verification was abandoned -- the exported recursor's missing
# inductive hypothesis went unverified.
def kidx_ok(xs: List<&2, U32>, ys: List<&2, U32>, +st: I.IS,
            +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>,
            +vt: R.Tr<U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{a, at} Con{b, bt}:
      +a2 : U32 = a
      +b2 : U32 = b
      +s2 : I.IS = st
      L.tri_is_yes(I.dr_r(I.defeq(2048n, U32.is_eq(a2, b2), s2, mt, nt,
                                  lp, vt, Nil{}, node(s2, a2), node(s2, b2))))
      && kidx_ok(at, bt, s2, mt, nt, lp, vt)
    case _ _:
      False{}

# the reduct (the minor over the remaining arguments), or the sentinel
def k_reduct(+ok: Bool, +st: I.IS, +rest: List<&2, U32>, +minor: U32) -> I.IR:
  match ok:
    case False{}:
      I.IR{st, 4294967295, False{}}
    case True{}:
      I.app_args(rest, st, minor)

def pick_ir(+z: Bool, +a: I.IR, +b: I.IR) -> I.IR:
  match z:
    case True{}:
      a
    case False{}:
      b

def whd_k(fuel: Nat, +st: I.IS, +mt: R.Tr<I.Meta>,
          +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +x: U32) -> I.IR:
  match fuel:
    case 0n:
      I.whd(st, mt, lp, vt, x)
    case 1n+p:
      +w = I.whd(st, mt, lp, vt, x)
      +s1 : I.IS = I.ir_st(w)
      +y : U32 = I.ir_ty(w)
      +h : T.Ex = spine_hd(s1, y)
      +args : List<&2, U32> = spine_args(s1, y)
      +mi : I.Meta = R.get(I.Meta, 64n, mt, I.const_nm2(h), I.MNone{})
      +pp : U32 = I.meta_p(mi)
      +ni : U32 = I.meta_k(mi)
      +kneed : U32 = (pp + 1 + I.meta_n(mi) : U32)
      +iskr : Bool = I.meta_is_rec(mi) && U32.is_eq(I.meta_kf(mi), 1)
                     && U32.is_gt(I.len_u(args, 0), (kneed + ni : U32))
      +kexp = I.k_expected(s1, S.pick(iskr, I.meta_rcty(mi), 4294967295), pp,
                           args)
      +s2 : I.IS = I.ir_st(kexp)
      +kidx : List<&2, U32> = I.skip_u(spine_args(s2, I.ir_ty(kexp)), pp)
      +kgiven : List<&2, U32> = I.take_u(I.skip_u(args, kneed), ni, Nil{})
      +ok : Bool = iskr && I.ir_ok(kexp) && kidx_ok(kidx, kgiven, s2, mt, nt, lp, vt)
      +r = k_reduct(ok, s2, I.skip_u(args, (kneed + ni + 1 : U32)),
                    I.nth_u(args, (pp + 1 : U32), 4294967295))
      pick_ir(ok, whd_k(p, I.ir_st(r), mt, nt, lp, vt,
                        S.pick(ok, I.ir_ty(r), 0)), w)

def tw_go(fuel: Nat, +st: I.IS, +kc: U32, +mt: R.Tr<I.Meta>,
          +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +ty: U32,
          +acc: List<&2, U32>, +nd: T.Ex) -> TL:
  match fuel nd:
    case 0n _:
      TL{st, kc, I.rev_u(acc, Nil{}), ty}
    case 1n+p T.EAll{nm, d, b, bi}:
      +f = fv_new(st, kc)
      +bd = inst0(nr_st(f), b, nr_x(f))
      +w = whd_k(64n, I.ir_st(bd), mt, nt, lp, vt, I.ir_ty(bd))
      tw_go(p, I.ir_st(w), nr_kc(f), mt, nt, lp, vt, I.ir_ty(w),
            Con{d, Con{nr_x(f), Con{(fvb() + kc : U32), acc}}},
            node(I.ir_st(w), I.ir_ty(w)))
    case 1n+p _:
      TL{st, kc, I.rev_u(acc, Nil{}), ty}

def tele_whnf(+st: I.IS, +kc: U32, +mt: R.Tr<I.Meta>,
              +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +ty: U32) -> TL:
  +w = whd_k(64n, st, mt, nt, lp, vt, ty)
  tw_go(256n, I.ir_st(w), kc, mt, nt, lp, vt, I.ir_ty(w), Nil{},
        node(I.ir_st(w), I.ir_ty(w)))

# --- spec membership --------------------------------------------------------
# k = which spec `x` is an application of (sentinel if none), ix = its
# index arguments
type SO is Data:
  SO{k: U32, ix: List<&2, U32>}

def so_k(+r: SO) -> U32:
  match r:
    case SO{k, ix}:
      k

def so_ix(+r: SO) -> List<&2, U32>:
  match r:
    case SO{k, ix}:
      ix

def pick_so(+z: Bool, +a: SO, +b: SO) -> SO:
  match z:
    case True{}:
      a
    case False{}:
      b

def spec_go(specs: List<&2, SP>, +st: I.IS, +j: U32, +hn: U32,
            +hus: List<&2, U32>, +args: List<&2, U32>) -> SO:
  match specs:
    case Nil{}:
      SO{4294967295, Nil{}}
    case Con{h0, t}:
      +h : SP = h0
      +np : U32 = I.len_u(sp_ps(h), 0)
      +hit : Bool = U32.is_eq(sp_n(h), hn)
                    && lvls_eq(I.is_lnt(st), sp_us(h), hus)
                    && U32.is_ge(I.len_u(args, 0), np)
                    && exs_eq(st, I.take_u(args, np, Nil{}), sp_ps(h))
      pick_so(hit, SO{j, I.skip_u(args, np)},
              spec_go(t, st, (j + 1 : U32), hn, hus, args))

def spec_of(+specs: List<&2, SP>, +st: I.IS, +x: U32) -> SO:
  +h : T.Ex = spine_hd(st, x)
  spec_go(specs, st, 0, I.const_nm2(h), const_us(h), spine_args(st, x))

# --- small list helpers ------------------------------------------------------
def fv_types(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{a, Con{b, Con{c, t}}}:
      fv_types(t, Con{c, acc})
    case _:
      I.rev_u(acc, Nil{})

def occ_any(xs: List<&2, U32>, +st: I.IS, +ns: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      occursi(st, h, ns) || occ_any(t, st, ns)

def pick_lsp(+z: Bool, +a: List<&2, SP>, +b: List<&2, SP>) -> List<&2, SP>:
  match z:
    case True{}:
      a
    case False{}:
      b

def app_sp(xs: List<&2, SP>, +y: SP) -> List<&2, SP>:
  match xs:
    case Nil{}:
      Con{y, Nil{}}
    case Con{h, t}:
      Con{h, app_sp(t, y)}

# --- discovery of nested occurrences -------------------------------------
type DS is Data:
  DS{st: I.IS, kc: U32, specs: List<&2, SP>, bad: Bool}

def ds_st(+r: DS) -> I.IS:
  match r:
    case DS{st, kc, specs, bad}:
      st

def ds_kc(+r: DS) -> U32:
  match r:
    case DS{st, kc, specs, bad}:
      kc

def ds_specs(+r: DS) -> List<&2, SP>:
  match r:
    case DS{st, kc, specs, bad}:
      specs

def ds_bad(+r: DS) -> Bool:
  match r:
    case DS{st, kc, specs, bad}:
      bad

# Every field: in whnf at each Pi, the result's head. An external inductive
# applied to parameters that mention the block is a nested occurrence (a
# new spec, unless already one). Positivity is checked on the way: a field
# binder's domain may not mention the block at all, and a result that does
# must be a spec application.
def disc_fields(flds: List<&2, U32>, +st: I.IS, +kc: U32,
                +specs: List<&2, SP>, +bad: Bool, +tn: List<&2, U32>,
                +items: List<&2, K.IItem>, +itab: R.Tr<K.IItem>,
                +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>,
                +vt: R.Tr<U32>) -> DS:
  match flds:
    case Nil{}:
      DS{st, kc, specs, bad}
    case Con{fty, t}:
      +tw = tele_whnf(st, kc, mt, nt, lp, vt, fty)
      +s1 : I.IS = tl_st(tw)
      +fres : U32 = tl_ty(tw)
      +h : T.Ex = spine_hd(s1, fres)
      +hn : U32 = I.const_nm2(h)
      +ii = ind_of(items, itab, hn)
      +pa : List<&2, U32> = I.take_u(spine_args(s1, fres), ii_np(ii), Nil{})
      +known : Bool = U32.is_ne(so_k(spec_of(specs, s1, fres)), 4294967295)
      +isnew : Bool = ii_is(ii) && Bool.not(mem(hn, tn))
                      && occ_any(pa, s1, tn) && Bool.not(known)
      +ndom : Bool = occ_any(fv_types(tl_fvs(tw), Nil{}), s1, tn)
      +inval : Bool = occursi(s1, fres, tn) && Bool.not(known)
                      && Bool.not(isnew)
      disc_fields(t, s1, tl_kc(tw),
                  pick_lsp(isnew, app_sp(specs, SP{hn, const_us(h), pa}),
                           specs),
                  bad || ndom || inval, tn, items, itab, mt, nt, lp, vt)

def disc_ctors(cs: List<&2, U32>, +sp: SP, +lps: List<&2, U32>,
               +st: I.IS, +kc: U32, +specs: List<&2, SP>, +bad: Bool,
               +tn: List<&2, U32>, +items: List<&2, K.IItem>,
               +itab: R.Tr<K.IItem>, +ctab: R.Tr<U32>, +mt: R.Tr<I.Meta>,
               +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>) -> DS:
  match cs:
    case Nil{}:
      DS{st, kc, specs, bad}
    case Con{c, t}:
      +r = at_spec(st, ctor_ty(items, ctab, c), lps, sp_us(sp), sp_ps(sp))
      +tl = tele(I.ir_st(r), kc, I.ir_ty(r))
      +d = disc_fields(fv_types(tl_fvs(tl), Nil{}), tl_st(tl), tl_kc(tl),
                       specs, bad || Bool.not(I.ir_ok(r)), tn, items, itab,
                       mt, nt, lp, vt)
      disc_ctors(t, sp, lps, ds_st(d), ds_kc(d), ds_specs(d), ds_bad(d), tn,
                 items, itab, ctab, mt, nt, lp, vt)

def disc(fuel: Nat, +more: Bool, +j: U32, +st: I.IS, +kc: U32,
         +specs: List<&2, SP>, +bad: Bool, +tn: List<&2, U32>,
         +items: List<&2, K.IItem>, +itab: R.Tr<K.IItem>,
         +ctab: R.Tr<U32>, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>,
         +vt: R.Tr<U32>) -> DS:
  match fuel more:
    case 0n _:
      DS{st, kc, specs, True{}}
    case 1n+p False{}:
      DS{st, kc, specs, bad}
    case 1n+p True{}:
      +sp : SP = nth_sp(specs, j)
      +ii = ind_of(items, itab, sp_n(sp))
      +d = disc_ctors(ii_cs(ii), sp, ii_lps(ii), st, kc, specs, bad, tn,
                      items, itab, ctab, mt, nt, lp, vt)
      +sp2 : List<&2, SP> = ds_specs(d)
      disc(p, U32.is_lt((j + 1 : U32), len_sp(sp2, 0)), (j + 1 : U32),
           ds_st(d), ds_kc(d), sp2, ds_bad(d), tn, items, itab, ctab, mt,
           nt, lp, vt)

# --- motives -------------------------------------------------------------
# For each spec: its index telescope, the major `t`, and
#   motive_j : forall (indices) (t : spec_j indices), Sort v
# ML carries the motives (flat triples) and, for the recursor types later,
# nothing else: each recursor re-peels the telescope with fresh variables.
type ML is Data:
  ML{st: I.IS, kc: U32, fvs: List<&2, U32>}

def ml_st(+r: ML) -> I.IS:
  match r:
    case ML{st, kc, fvs}:
      st

def ml_kc(+r: ML) -> U32:
  match r:
    case ML{st, kc, fvs}:
      kc

def ml_fvs(+r: ML) -> List<&2, U32>:
  match r:
    case ML{st, kc, fvs}:
      fvs

# binders (fields, params, indices) with their types' annotations dropped
def strip_fvs(xs: List<&2, U32>, +st: I.IS, +ann: List<&2, U32>,
              acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{a, Con{b, Con{c, t}}}:
      strip_fvs(t, st, ann, Con{strip_ann(st, c, ann), Con{b, Con{a, acc}}})
    case _:
      I.rev_u(acc, Nil{})

# spec_j's type, instantiated; the index variables and the major premise
# with its type `spec_j params indices`; returns (st, kc, idx ++ [t] flat).
# The indices' types lose their annotations (Lean's mk_local_decl_for)
def spec_tele(+sp: SP, +st: I.IS, +kc: U32, +items: List<&2, K.IItem>,
              +itab: R.Tr<K.IItem>, +ann: List<&2, U32>) -> TL:
  +ii = ind_of(items, itab, sp_n(sp))
  +r = at_spec(st, ii_ty(ii), ii_lps(ii), sp_us(sp), sp_ps(sp))
  +tl = tele(I.ir_st(r), kc, I.ir_ty(r))
  +ifv : List<&2, U32> = strip_fvs(tl_fvs(tl), tl_st(tl), ann, Nil{})
  +hc = I.alloc_ex(tl_st(tl), T.EConst{sp_n(sp), sp_us(sp)})
  +ap = I.app_args(List.append(&2, U32, sp_ps(sp), fv_nodes(ifv, Nil{})),
                   I.ir_st(hc), I.ir_ty(hc))
  +t = fv_new(I.ir_st(ap), tl_kc(tl))
  TL{nr_st(t), nr_kc(t),
     List.append(&2, U32, ifv,
                 [(fvb() + tl_kc(tl) : U32), nr_x(t), I.ir_ty(ap)]),
     4294967295}

def mk_motives(specs: List<&2, SP>, +st: I.IS, +kc: U32, +sortv: U32,
               +items: List<&2, K.IItem>, +itab: R.Tr<K.IItem>,
               +ann: List<&2, U32>, +acc: List<&2, U32>) -> ML:
  match specs:
    case Nil{}:
      ML{st, kc, acc}
    case Con{sp, t}:
      +te = spec_tele(sp, st, kc, items, itab, ann)
      +ty = mk_pi(tl_fvs(te), tl_st(te), sortv)
      +m = fv_new(I.ir_st(ty), tl_kc(te))
      mk_motives(t, nr_st(m), nr_kc(m), sortv, items, itab, ann,
                 List.append(&2, U32, acc,
                             [(fvb() + tl_kc(te) : U32), nr_x(m), I.ir_ty(ty)]))

# --- minors ---------------------------------------------------------------
type IH is Data:
  IH{f: U32, k: U32, zs: List<&2, U32>, ix: List<&2, U32>}

type MI is Data:
  MI{j: U32, c: U32, mnode: U32, fields: List<&2, U32>, ihs: List<&2, IH>}

def mi_j(+m: MI) -> U32:
  match m:
    case MI{j, c, mnode, fields, ihs}:
      j

type MN is Data:
  MN{st: I.IS, kc: U32, fvs: List<&2, U32>, info: List<&2, MI>}

def mn_st(+r: MN) -> I.IS:
  match r:
    case MN{st, kc, fvs, info}:
      st

def mn_kc(+r: MN) -> U32:
  match r:
    case MN{st, kc, fvs, info}:
      kc

def mn_fvs(+r: MN) -> List<&2, U32>:
  match r:
    case MN{st, kc, fvs, info}:
      fvs

def mn_info(+r: MN) -> List<&2, MI>:
  match r:
    case MN{st, kc, fvs, info}:
      info


# one IH per field whose (whnf'd) type ends in a spec:
#   ih : forall zs, motive_k ix (f zs)
type IL is Data:
  IL{st: I.IS, kc: U32, fvs: List<&2, U32>, ihs: List<&2, IH>}

def il_st(+r: IL) -> I.IS:
  match r:
    case IL{st, kc, fvs, ihs}:
      st

def il_kc(+r: IL) -> U32:
  match r:
    case IL{st, kc, fvs, ihs}:
      kc

def il_fvs(+r: IL) -> List<&2, U32>:
  match r:
    case IL{st, kc, fvs, ihs}:
      fvs

def il_ihs(+r: IL) -> List<&2, IH>:
  match r:
    case IL{st, kc, fvs, ihs}:
      ihs

def ih_app(xs: List<&2, IH>, +y: IH) -> List<&2, IH>:
  match xs:
    case Nil{}:
      Con{y, Nil{}}
    case Con{h, t}:
      Con{h, ih_app(t, y)}

def pick_st(+z: Bool, +a: I.IS, +b: I.IS) -> I.IS:
  match z:
    case True{}:
      a
    case False{}:
      b

def pick_ihs(+z: Bool, +a: List<&2, IH>, +b: List<&2, IH>) -> List<&2, IH>:
  match z:
    case True{}:
      a
    case False{}:
      b

def mk_ihs(flds: List<&2, U32>, +st: I.IS, +kc: U32, +specs: List<&2, SP>,
           +mots: List<&2, U32>, +mt: R.Tr<I.Meta>,
           +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
           +fvs: List<&2, U32>, +ihs: List<&2, IH>) -> IL:
  match flds:
    case Con{fnm, Con{fnd0, Con{fty, t}}}:
      +fnd : U32 = fnd0
      +tw = tele_whnf(st, kc, mt, nt, lp, vt, fty)
      +s1 : I.IS = tl_st(tw)
      +so : SO = spec_of(specs, s1, tl_ty(tw))
      +k : U32 = so_k(so)
      +zn : List<&2, U32> = fv_nodes(tl_fvs(tw), Nil{})
      +fa = I.app_args(zn, s1, fnd)
      +mb = I.app_args(List.append(&2, U32, so_ix(so), [I.ir_ty(fa)]),
                       I.ir_st(fa), I.nth_u(fv_nodes(mots, Nil{}), k, 0))
      +ty = mk_pi(tl_fvs(tw), I.ir_st(mb), I.ir_ty(mb))
      +h = fv_new(I.ir_st(ty), tl_kc(tw))
      +rec : Bool = U32.is_ne(k, 4294967295)
      mk_ihs(t, pick_st(rec, nr_st(h), st), S.pick(rec, nr_kc(h), kc), specs,
             mots, mt, nt, lp, vt,
             S.pick_l(rec, List.append(&2, U32, fvs,
                                       [(fvb() + tl_kc(tw) : U32), nr_x(h),
                                        I.ir_ty(ty)]), fvs),
             pick_ihs(rec, ih_app(ihs, IH{fnd, k, tl_fvs(tw), so_ix(so)}),
                      ihs))
    case _:
      IL{st, kc, fvs, ihs}

def mi_app(xs: List<&2, MI>, +y: MI) -> List<&2, MI>:
  match xs:
    case Nil{}:
      Con{y, Nil{}}
    case Con{h, t}:
      Con{h, mi_app(t, y)}

# minor premise for constructor c of spec j:
#   forall fields ihs, motive_j idx (c params fields)
def mk_minors_c(cs: List<&2, U32>, +j: U32, +sp: SP, +lps: List<&2, U32>,
                +st: I.IS, +kc: U32, +specs: List<&2, SP>,
                +mots: List<&2, U32>, +ann: List<&2, U32>,
                +items: List<&2, K.IItem>, +ctab: R.Tr<U32>,
                +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
                +fvs: List<&2, U32>, +info: List<&2, MI>) -> MN:
  match cs:
    case Nil{}:
      MN{st, kc, fvs, info}
    case Con{c0, t}:
      +c : U32 = c0
      +r = at_spec(st, ctor_ty(items, ctab, c), lps, sp_us(sp), sp_ps(sp))
      +tl = tele(I.ir_st(r), kc, I.ir_ty(r))
      +s1 : I.IS = tl_st(tl)
      +flds : List<&2, U32> = strip_fvs(tl_fvs(tl), s1, ann, Nil{})
      +il = mk_ihs(flds, s1, tl_kc(tl), specs, mots, mt, nt, lp, vt, Nil{}, Nil{})
      +s2 : I.IS = il_st(il)
      +idx : List<&2, U32> = I.skip_u(spine_args(s2, tl_ty(tl)),
                                      I.len_u(sp_ps(sp), 0))
      +cc = I.alloc_ex(s2, T.EConst{c, sp_us(sp)})
      +ca = I.app_args(List.append(&2, U32, sp_ps(sp),
                                   fv_nodes(flds, Nil{})),
                       I.ir_st(cc), I.ir_ty(cc))
      +bd = I.app_args(List.append(&2, U32, idx, [I.ir_ty(ca)]),
                       I.ir_st(ca), I.nth_u(fv_nodes(mots, Nil{}), j, 0))
      +ty = mk_pi(List.append(&2, U32, flds, il_fvs(il)), I.ir_st(bd),
                  I.ir_ty(bd))
      +m = fv_new(I.ir_st(ty), il_kc(il))
      mk_minors_c(t, j, sp, lps, nr_st(m), nr_kc(m), specs, mots, ann,
                  items, ctab, mt, nt, lp, vt,
                  List.append(&2, U32, fvs,
                              [(fvb() + il_kc(il) : U32), nr_x(m),
                               I.ir_ty(ty)]),
                  mi_app(info, MI{j, c, nr_x(m), flds, il_ihs(il)}))

def mk_minors(sps: List<&2, SP>, +j: U32, +st: I.IS, +kc: U32,
              +specs: List<&2, SP>, +mots: List<&2, U32>,
              +ann: List<&2, U32>, +items: List<&2, K.IItem>,
              +itab: R.Tr<K.IItem>, +ctab: R.Tr<U32>, +mt: R.Tr<I.Meta>,
              +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
              +fvs: List<&2, U32>, +info: List<&2, MI>) -> MN:
  match sps:
    case Nil{}:
      MN{st, kc, fvs, info}
    case Con{sp0, t}:
      +sp : SP = sp0
      +ii = ind_of(items, itab, sp_n(sp))
      +r = mk_minors_c(ii_cs(ii), j, sp, ii_lps(ii), st, kc, specs, mots,
                       ann, items, ctab, mt, nt, lp, vt, fvs, info)
      mk_minors(t, (j + 1 : U32), mn_st(r), mn_kc(r), specs, mots, ann,
                items, itab, ctab, mt, nt, lp, vt, mn_fvs(r), mn_info(r))

# --- recursor types --------------------------------------------------------
#   rec_j : forall params motives minors (indices) (t : spec_j ..),
#           motive_j indices t
type RT is Data:
  RT{st: I.IS, kc: U32, tys: List<&2, U32>}

def rt_st(+r: RT) -> I.IS:
  match r:
    case RT{st, kc, tys}:
      st

def rt_tys(+r: RT) -> List<&2, U32>:
  match r:
    case RT{st, kc, tys}:
      tys

def rec_types(sps: List<&2, SP>, +j: U32, +st: I.IS, +kc: U32,
              +pre: List<&2, U32>, +mots: List<&2, U32>,
              +items: List<&2, K.IItem>, +itab: R.Tr<K.IItem>,
              +ann: List<&2, U32>, +acc: List<&2, U32>) -> RT:
  match sps:
    case Nil{}:
      RT{st, kc, acc}
    case Con{sp, t}:
      +te = spec_tele(sp, st, kc, items, itab, ann)
      +bd = I.app_args(fv_nodes(tl_fvs(te), Nil{}), tl_st(te),
                       I.nth_u(fv_nodes(mots, Nil{}), j, 0))
      +tail = mk_pi(tl_fvs(te), I.ir_st(bd), I.ir_ty(bd))
      +rty = mk_pi(pre, I.ir_st(tail), I.ir_ty(tail))
      rec_types(t, (j + 1 : U32), I.ir_st(rty), tl_kc(te), pre, mots, items,
                itab, ann, List.append(&2, U32, acc, [I.ir_ty(rty)]))

# --- association with the export's recursors --------------------------------
# for each derived type, the name of the exported recursor whose type is it
def rec_by_type(items: List<&2, K.IItem>, +st: I.IS, +ty: U32) -> U32:
  match items:
    case Nil{}:
      4294967295
    case Con{K.IRec{nm, lps, rty, np, ni, nmo, kf}, t}:
      S.pick(ex_eqi(st, rty, ty), nm, rec_by_type(t, st, ty))
    case Con{h, t}:
      rec_by_type(t, st, ty)

def assoc_recs(tys: List<&2, U32>, +items: List<&2, K.IItem>, +st: I.IS,
               +acc: List<&2, U32>) -> List<&2, U32>:
  match tys:
    case Nil{}:
      acc
    case Con{ty, t}:
      assoc_recs(t, items, st,
                 List.append(&2, U32, acc, [rec_by_type(items, st, ty)]))

def count_recs(items: List<&2, K.IItem>, +acc: U32) -> U32:
  match items:
    case Nil{}:
      acc
    case Con{K.IRec{nm, lps, ty, np, ni, nmo, kf}, t}:
      count_recs(t, (acc + 1 : U32))
    case Con{h, t}:
      count_recs(t, acc)

def count_rules(items: List<&2, K.IItem>, +acc: U32) -> U32:
  match items:
    case Nil{}:
      acc
    case Con{K.IRule{ct, nf, rhs}, t}:
      count_rules(t, (acc + 1 : U32))
    case Con{h, t}:
      count_rules(t, acc)

def rec_lps(items: List<&2, K.IItem>) -> List<&2, U32>:
  match items:
    case Nil{}:
      Nil{}
    case Con{K.IRec{nm, lps, ty, np, ni, nmo, kf}, t}:
      lps
    case Con{h, t}:
      rec_lps(t)

def all_found(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      U32.is_ne(h, 4294967295) && all_found(t)

def distinct(+xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      +t2 : List<&2, U32> = t
      Bool.not(mem(h, t2)) && distinct(t2)

# --- rules -----------------------------------------------------------------
# rule for minor m (spec j, constructor c):
#   fun params motives minors fields =>
#     minor_c fields (fun zs => rec_k params motives minors ix (f zs))..
type RL is Data:
  RL{st: I.IS, xs: List<&2, U32>}

def rl_st(+r: RL) -> I.IS:
  match r:
    case RL{st, xs}:
      st

def rl_xs(+r: RL) -> List<&2, U32>:
  match r:
    case RL{st, xs}:
      xs

def ih_vals(ihs: List<&2, IH>, +st: I.IS, +rnames: List<&2, U32>,
            +rus: List<&2, U32>, +pre: List<&2, U32>,
            +acc: List<&2, U32>) -> RL:
  match ihs:
    case Nil{}:
      RL{st, acc}
    case Con{IH{f, k, zs, ix}, t}:
      +zs2 : List<&2, U32> = zs
      +fa = I.app_args(fv_nodes(zs2, Nil{}), st, f)
      +rc = I.alloc_ex(I.ir_st(fa), T.EConst{I.nth_u(rnames, k, 4294967295),
                                             rus})
      +ap = I.app_args(List.append(&2, U32, pre,
                                   List.append(&2, U32, ix, [I.ir_ty(fa)])),
                       I.ir_st(rc), I.ir_ty(rc))
      +lm = mk_lam(zs2, I.ir_st(ap), I.ir_ty(ap))
      ih_vals(t, I.ir_st(lm), rnames, rus, pre,
              List.append(&2, U32, acc, [I.ir_ty(lm)]))

# the export's rule (ct, nf) whose rhs is this one (sentinel if none)
def rule_match(items: List<&2, K.IItem>, +st: I.IS, +c: U32, +nf: U32,
               +rhs: U32) -> U32:
  match items:
    case Nil{}:
      4294967295
    case Con{K.IRule{ct, nf2, rhs2}, t}:
      +r2 : U32 = rhs2
      S.pick(U32.is_eq(ct, c) && U32.is_eq(nf2, nf) && ex_eqi(st, r2, rhs),
             r2, rule_match(t, st, c, nf, rhs))
    case Con{h, t}:
      rule_match(t, st, c, nf, rhs)

# per recursor (by spec): the verified rules, flat [c, nf, rhs(export)]
type RW is Data:
  RW{st: I.IS, ok: Bool, per: List<&2, U32>}

def mk_rules(info: List<&2, MI>, +st: I.IS, +rnames: List<&2, U32>,
             +rus: List<&2, U32>, +pre: List<&2, U32>, +prefv: List<&2, U32>,
             +items: List<&2, K.IItem>, +ok: Bool,
             +per: List<&2, U32>) -> RW:
  match info:
    case Nil{}:
      RW{st, ok, per}
    case Con{MI{j, c, mnode, fields, ihs}, t}:
      +c2 : U32 = c
      +fl : List<&2, U32> = fields
      +iv = ih_vals(ihs, st, rnames, rus, pre, Nil{})
      +bd = I.app_args(List.append(&2, U32, fv_nodes(fl, Nil{}), rl_xs(iv)),
                       rl_st(iv), mnode)
      +rhs = mk_lam(List.append(&2, U32, prefv, fl), I.ir_st(bd),
                    I.ir_ty(bd))
      +nf : U32 = I.len_u(fv_nodes(fl, Nil{}), 0)
      +e : U32 = rule_match(items, I.ir_st(rhs), c2, nf, I.ir_ty(rhs))
      mk_rules(t, I.ir_st(rhs), rnames, rus, pre, prefv, items,
               ok && U32.is_ne(e, 4294967295),
               List.append(&2, U32, per, [j, c2, nf, e]))

# --- the block -------------------------------------------------------------
def ind_items(items: List<&2, K.IItem>) -> List<&2, K.IItem>:
  match items:
    case Nil{}:
      Nil{}
    case Con{K.IInd{nm, lps, ty, np, ni, nn, cs}, t}:
      Con{K.IInd{nm, lps, ty, np, ni, nn, cs}, ind_items(t)}
    case Con{h, t}:
      ind_items(t)

def ind_names(xs: List<&2, K.IItem>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{K.IInd{nm, lps, ty, np, ni, nn, cs}, t}:
      Con{nm, ind_names(t)}
    case Con{h, t}:
      ind_names(t)

def first_ind(xs: List<&2, K.IItem>) -> K.IItem:
  match xs:
    case Nil{}:
      K.IOther{}
    case Con{h, t}:
      h

def ii_nn(+x: K.IItem) -> U32:
  match x:
    case K.IInd{nm, lps, ty, np, ni, nn, cs}:
      nn
    case _:
      0

def ii_ni(+x: K.IItem) -> U32:
  match x:
    case K.IInd{nm, lps, ty, np, ni, nn, cs}:
      ni
    case _:
      0

def specs0(ns: List<&2, U32>, +us: List<&2, U32>,
           +ps: List<&2, U32>) -> List<&2, SP>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{n, t}:
      Con{SP{n, us, ps}, specs0(t, us, ps)}

# the rules of spec j, flat [c, nf, rhs]
def rules_of(per: List<&2, U32>, +j: U32) -> List<&2, U32>:
  match per:
    case Con{j2, Con{c, Con{nf, Con{rhs, t}}}}:
      +r : List<&2, U32> = rules_of(t, j)
      S.pick_l(U32.is_eq(j2, j), Con{c, Con{nf, Con{rhs, r}}}, r)
    case _:
      Nil{}

# per derived spec: the recursor's name and its metadata
def rr_metas(sps: List<&2, SP>, +j: U32, +rnames: List<&2, U32>,
             +per: List<&2, U32>, +np: U32, +nmot: U32, +nmin: U32,
             +items: List<&2, K.IItem>, +itab: R.Tr<K.IItem>,
             +acc: R.Tr<I.Meta>) -> R.Tr<I.Meta>:
  match sps:
    case Nil{}:
      acc
    case Con{sp, t}:
      +ii = ind_of(items, itab, sp_n(sp))
      rr_metas(t, (j + 1 : U32), rnames, per, np, nmot, nmin, items, itab,
               R.set(I.Meta, 64n, acc, I.nth_u(rnames, j, 4294967295),
                     I.MRecR{np, nmot, nmin, ii_ni(ii), rules_of(per, j)},
                     I.MNone{}))

# verdict: 0 the export's recursors are exactly the derived ones, 2 cannot
# say (a mismatch, an unsupported block, a positivity doubt) -- and the
# recursor metadata (rule-based iota) when 0
type VR is Data:
  VR{v: U32, mt: R.Tr<I.Meta>}

def vr_v(+r: VR) -> U32:
  match r:
    case VR{v, mt}:
      v

def vr_mt(+r: VR) -> R.Tr<I.Meta>:
  match r:
    case VR{v, mt}:
      mt

def len_mi(xs: List<&2, MI>, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      len_mi(t, (acc + 1 : U32))

def rw_ok(+r: RW) -> Bool:
  match r:
    case RW{st, ok, per}:
      ok

def rw_per(+r: RW) -> List<&2, U32>:
  match r:
    case RW{st, ok, per}:
      per

def verify_block(+items: List<&2, K.IItem>, +st0: I.IS,
                 +itab: R.Tr<K.IItem>, +ctab: R.Tr<U32>,
                 +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>,
                 +vt: R.Tr<U32>, +ann: List<&2, U32>) -> VR:
  +inds = ind_items(items)
  +tn : List<&2, U32> = ind_names(inds)
  +i0 = first_ind(inds)
  +np : U32 = ii_np(i0)
  +lps : List<&2, U32> = ii_lps(i0)
  # params and their levels
  +pl = W.param_lvls(lps, st0, Nil{})
  +us0 : List<&2, U32> = I.rev_u(I.ls_xs(pl), Nil{})
  +pt = tele_n(I.ls_st(pl), 0, ii_ty(i0), np)
  # binder types lose their annotations (Lean's mk_local_decl_for):
  # `class C (a : A) (b : outParam B)` has `b : B` in C.rec
  +params : List<&2, U32> = strip_fvs(tl_fvs(pt), tl_st(pt), ann, Nil{})
  +pv : List<&2, U32> = fv_nodes(params, Nil{})
  # the result sort: Prop-valued blocks (elimination into Prop only, or
  # subsingletons) are not handled here
  +rt = tele(tl_st(pt), tl_kc(pt), tl_ty(pt))
  +rs : T.Ex = node(tl_st(rt), tl_ty(rt))
  +isprop : Bool = Bool.not(I.is_sortx(rs))
                   || L.tri_is_yes(L.ln_is_zero(R.get(L.LN, 64n,
                        I.is_lnt(tl_st(rt)), I.sort_lvl_of(rs), L.LNun{})))
  # the recursors' level parameters: the motive's first, then the block's
  # -- unless the block eliminates only into Prop (Lean's
  # elim_only_at_universe_zero): the motive is `Sort 0`, no extra level.
  # A Prop block of several types after nested elimination (mutual, or
  # nested) always does. A single inductive follows its export's claim,
  # which check.bend's block_rec_v holds to Lean's rule (large_elim: the
  # subsingleton test, with the index exception) in the same block_v
  +rlps : List<&2, U32> = rec_lps(items)
  +single : Bool = U32.is_eq(I.len_u(tn, 0), 1) && U32.is_eq(ii_nn(i0), 0)
  +claim : Bool = U32.is_eq(I.len_u(rlps, 0), (I.len_u(lps, 0) + 1 : U32))
  +large : Bool = S.pick_b(single, claim, Bool.not(isprop))
  +lvok : Bool = S.pick_b(large,
                          I.eq_u32s(I.skip_u(rlps, 1), lps) && claim,
                          I.eq_u32s(rlps, lps))
  +rl = W.param_lvls(rlps, tl_st(rt), Nil{})
  +rus : List<&2, U32> = I.rev_u(I.ls_xs(rl), Nil{})
  +z = I.alloc_lvl(I.ls_st(rl), L.ln_zero())
  +sv = I.alloc_ex(I.ir_st(z), T.ESort{S.pick(large, I.nth_u(rus, 0, 0),
                                              I.ir_ty(z))})
  # specs
  +d = disc(64n, True{}, 0, I.ir_st(sv), tl_kc(rt),
            specs0(tn, us0, pv), False{}, tn, items, itab, ctab, mt, nt, lp, vt)
  +specs : List<&2, SP> = ds_specs(d)
  # motives, minors
  +ml = mk_motives(specs, ds_st(d), ds_kc(d), I.ir_ty(sv), items, itab, ann,
                   Nil{})
  +mots : List<&2, U32> = ml_fvs(ml)
  +mn = mk_minors(specs, 0, ml_st(ml), ml_kc(ml), specs, mots, ann, items,
                  itab, ctab, mt, nt, lp, vt, Nil{}, Nil{})
  +prefv : List<&2, U32> = List.append(&2, U32, params,
                             List.append(&2, U32, mots, mn_fvs(mn)))
  # recursor types and their exported namesakes
  +rty = rec_types(specs, 0, mn_st(mn), mn_kc(mn), prefv, mots, items,
                   itab, ann, Nil{})
  +rnames : List<&2, U32> = assoc_recs(rt_tys(rty), items, rt_st(rty), Nil{})
  +nmot : U32 = len_sp(specs, 0)
  +recok : Bool = all_found(rnames) && distinct(rnames)
                  && U32.is_eq(I.len_u(rnames, 0), count_recs(items, 0))
  # rules
  +info : List<&2, MI> = mn_info(mn)
  +nmin : U32 = len_mi(info, 0)
  +rw = mk_rules(info, rt_st(rty), rnames, rus,
                 fv_nodes(prefv, Nil{}), prefv, items, True{}, Nil{})
  +ruleok : Bool = rw_ok(rw) && U32.is_eq(count_rules(items, 0), nmin)
  +good : Bool = lvok && Bool.not(ds_bad(d)) && recok && ruleok
  # 0 verified, 2 undecided (the older derivation decides). A completed
  # derivation that does not match the export is NOT yet a reject: in
  # bugs/rec-missing-ih Lean rejects the inductive itself (a field's type is
  # a K-like recursor stuck because its indices `rcC x` and `rcA x` are not
  # defeq -- a non-transitive proof-irrelevance pair -- so `Owner` occurs
  # non-positively); deciding that NO needs the main machine's rigidity,
  # which this oracle lacks, and a derivation on an undecided field could
  # differ from Lean's for the wrong reason.
  VR{S.pick(good, 0, 2),
     rr_metas(specs, 0, rnames, rw_per(rw), np, nmot, nmin, items, itab, mt)}


# =========================================================================
# Simple blocks, compared on the export's DAG
# =========================================================================
# One inductive, no indices, not nested, no constructor field mentioning it.
# Lean's recursor (inductive.cpp mk_rec_infos / declare_recursors) is then
#   rec : Π params, Π (motive : T params -> Sort u),
#         Π (minor_k : Π fields_k, motive (c_k params fields_k)),
#         Π (t : T params), motive t
# with the rules  c_k := fun params motive minors fields_k => minor_k fields_k
# (params and fields with their head annotations dropped). Compared with the
# export's directly: a field's type inside minor_k is the constructor's with
# its parameter references shifted past the motive and the earlier minors.
# The comparison is memoised on (node, node, cutoff, shift), so a shared
# subterm is compared once: navier-stokes's structures are ~10^3 DAG nodes
# and ~10^6 tree nodes, and the derivation above rebuilds the trees.
# A mismatch is no verdict: the derivation above decides.
type MH is Data:
  MHnone{}
  MHyes{}
  MHno{}

type SM is Data:
  SM{ok: Bool, m: R.Tr<List<&2, U32>>}

def sm_ok(+r: SM) -> Bool:
  match r:
    case SM{ok, m}:
      ok

def sm_m(+r: SM) -> R.Tr<List<&2, U32>>:
  match r:
    case SM{ok, m}:
      m

# memo entries per left node: flat [b, c, s, ok]
def pick_mh(+z: Bool, +a: MH, +b: MH) -> MH:
  match z:
    case True{}:
      a
    case False{}:
      b

def memo_go(xs: List<&2, U32>, +b: U32, +c: U32, +s: U32, +acc: MH) -> MH:
  match xs:
    case Con{x, Con{y, Con{z, Con{v, t}}}}:
      memo_go(t, b, c, s,
              pick_mh(U32.is_eq(x, b) && U32.is_eq(y, c) && U32.is_eq(z, s),
                      pick_mh(U32.is_eq(v, 1), MHyes{}, MHno{}), acc))
    case _:
      acc

def memo_of(+m: R.Tr<List<&2, U32>>, +a: U32, +b: U32, +c: U32,
            +s: U32) -> MH:
  memo_go(R.get(List<&2, U32>, 64n, m, a, Nil{}), b, c, s, MHnone{})

def memo_put(+ok: Bool, +m: R.Tr<List<&2, U32>>, +a: U32, +b: U32,
             +c: U32, +s: U32) -> SM:
  +old : List<&2, U32> = R.get(List<&2, U32>, 64n, m, a, Nil{})
  SM{ok, R.set(List<&2, U32>, 64n, m, a,
               Con{b, Con{c, Con{s, Con{S.pick(ok, 1, 0), old}}}}, Nil{})}

def bv_eq(+lt: Bool, +i: U32, +j: U32, +s: U32) -> Bool:
  match lt:
    case True{}:
      U32.is_eq(i, j)
    case False{}:
      U32.is_eq(j, (i + s : U32))

# `a` (constructor side, nodes x) against `b` (export side, nodes y): a
# loose bvar i >= c of `a` is i + s in `b`; binder names and info ignored,
# levels by normal form
def sh_eq(+fuel: Nat, +st: I.IS, +a: U32, +b: U32, +c: U32, +s: U32,
          +h: MH, +x: T.Ex, +y: T.Ex, +m: R.Tr<List<&2, U32>>) -> SM:
  match fuel h x y:
    case 0n _ _ _:
      SM{False{}, m}
    case 1n+p MHyes{} _ _:
      SM{True{}, m}
    case 1n+p MHno{} _ _:
      SM{False{}, m}
    case 1n+p MHnone{} T.EBVar{i} T.EBVar{j}:
      SM{bv_eq(U32.is_lt(i, c), i, j, s), m}
    case 1n+p MHnone{} T.ESort{l} T.ESort{k}:
      SM{L.tri_is_yes(L.ln_cmp(R.get(L.LN, 64n, I.is_lnt(st), l, L.LNun{}),
                               R.get(L.LN, 64n, I.is_lnt(st), k, L.LNun{}))),
         m}
    case 1n+p MHnone{} T.EConst{n, us} T.EConst{n2, vs}:
      SM{U32.is_eq(n, n2) && lvls_eq(I.is_lnt(st), us, vs), m}
    case 1n+p MHnone{} T.ENat{d} T.ENat{e}:
      SM{I.eq_u32s(d, e), m}
    case 1n+p MHnone{} T.EStr{d} T.EStr{e}:
      SM{I.eq_u32s(d, e), m}
    case 1n+p MHnone{} T.EApp{f, a1} T.EApp{g, b1}:
      +r1 = sh_eq(p, st, f, g, c, s, memo_of(m, f, g, c, s), node(st, f),
                  node(st, g), m)
      +m1 = sm_m(r1)
      +r2 = sh_eq(p, st, a1, b1, c, s, memo_of(m1, a1, b1, c, s),
                  node(st, a1), node(st, b1), m1)
      memo_put(sm_ok(r1) && sm_ok(r2), sm_m(r2), a, b, c, s)
    case 1n+p MHnone{} T.ELam{n, t, b1, bi} T.ELam{n2, u, b2, bj}:
      +r1 = sh_eq(p, st, t, u, c, s, memo_of(m, t, u, c, s), node(st, t),
                  node(st, u), m)
      +m1 = sm_m(r1)
      +c1 : U32 = (c + 1 : U32)
      +r2 = sh_eq(p, st, b1, b2, c1, s, memo_of(m1, b1, b2, c1, s),
                  node(st, b1), node(st, b2), m1)
      memo_put(sm_ok(r1) && sm_ok(r2), sm_m(r2), a, b, c, s)
    case 1n+p MHnone{} T.EAll{n, t, b1, bi} T.EAll{n2, u, b2, bj}:
      +r1 = sh_eq(p, st, t, u, c, s, memo_of(m, t, u, c, s), node(st, t),
                  node(st, u), m)
      +m1 = sm_m(r1)
      +c1 : U32 = (c + 1 : U32)
      +r2 = sh_eq(p, st, b1, b2, c1, s, memo_of(m1, b1, b2, c1, s),
                  node(st, b1), node(st, b2), m1)
      memo_put(sm_ok(r1) && sm_ok(r2), sm_m(r2), a, b, c, s)
    case 1n+p MHnone{} T.ELet{n, t, v, b1} T.ELet{n2, u, w, b2}:
      +r1 = sh_eq(p, st, t, u, c, s, memo_of(m, t, u, c, s), node(st, t),
                  node(st, u), m)
      +m1 = sm_m(r1)
      +r2 = sh_eq(p, st, v, w, c, s, memo_of(m1, v, w, c, s), node(st, v),
                  node(st, w), m1)
      +m2 = sm_m(r2)
      +c1 : U32 = (c + 1 : U32)
      +r3 = sh_eq(p, st, b1, b2, c1, s, memo_of(m2, b1, b2, c1, s),
                  node(st, b1), node(st, b2), m2)
      memo_put(sm_ok(r1) && sm_ok(r2) && sm_ok(r3), sm_m(r3), a, b, c, s)
    case 1n+p MHnone{} T.EProj{tn, i, s1} T.EProj{tn2, j, s2}:
      +r1 = sh_eq(p, st, s1, s2, c, s, memo_of(m, s1, s2, c, s),
                  node(st, s1), node(st, s2), m)
      memo_put(U32.is_eq(tn, tn2) && U32.is_eq(i, j) && sm_ok(r1),
               sm_m(r1), a, b, c, s)
    case 1n+p MHnone{} _ _:
      SM{False{}, m}

def sq(+st: I.IS, +a: U32, +b: U32, +c: U32, +s: U32,
       +m: R.Tr<List<&2, U32>>) -> SM:
  sh_eq(4096n, st, a, b, c, s, memo_of(m, a, b, c, s), node(st, a),
        node(st, b), m)

# the walk's state: verdict so far, memo, two cursors
type WK is Data:
  WK{ok: Bool, m: R.Tr<List<&2, U32>>, x: U32, y: U32}

def wk_ok(+w: WK) -> Bool:
  match w:
    case WK{ok, m, x, y}:
      ok

def wk_m(+w: WK) -> R.Tr<List<&2, U32>>:
  match w:
    case WK{ok, m, x, y}:
      m

def wk_x(+w: WK) -> U32:
  match w:
    case WK{ok, m, x, y}:
      x

def wk_y(+w: WK) -> U32:
  match w:
    case WK{ok, m, x, y}:
      y

def is_pi(+x: T.Ex) -> Bool:
  match x:
    case T.EAll{n, t, b, bi}:
      True{}
    case _:
      False{}

def is_lam(+x: T.Ex) -> Bool:
  match x:
    case T.ELam{n, t, b, bi}:
      True{}
    case _:
      False{}

def bnd_dom(+x: T.Ex) -> U32:
  match x:
    case T.EAll{n, t, b, bi}:
      t
    case T.ELam{n, t, b, bi}:
      t
    case _:
      4294967295

def bnd_body(+x: T.Ex) -> U32:
  match x:
    case T.EAll{n, t, b, bi}:
      b
    case T.ELam{n, t, b, bi}:
      b
    case _:
      4294967295

# one binder of each side: x a Pi (its domain stripped, compared at cutoff c
# and shift s), y a Pi (ylam False) or a lambda (ylam True)
def wk_step(+st: I.IS, +ann: List<&2, U32>, +c: U32, +s: U32,
            +ylam: Bool, +w: WK) -> WK:
  +nx : T.Ex = node(st, wk_x(w))
  +ny : T.Ex = node(st, wk_y(w))
  +r = sq(st, strip_ann(st, bnd_dom(nx), ann), bnd_dom(ny), c, s, wk_m(w))
  WK{wk_ok(w) && is_pi(nx) && S.pick_b(ylam, is_lam(ny), is_pi(ny))
       && sm_ok(r),
     sm_m(r), bnd_body(nx), bnd_body(ny)}

# k binders; the cutoff counts the binders already passed (cb: the cutoff
# grows with them, for fields; params compare unshifted)
def wk_n(fuel: Nat, +go: Bool, +st: I.IS, +ann: List<&2, U32>, +k: U32,
         +c: U32, +cb: Bool, +s: U32, +ylam: Bool, +w: WK) -> WK:
  match fuel go:
    case 0n _:
      WK{False{}, wk_m(w), wk_x(w), wk_y(w)}
    case 1n+p False{}:
      w
    case 1n+p True{}:
      +k1 : U32 = (k - 1 : U32)
      wk_n(p, U32.is_ne(k1, 0), st, ann, k1, S.pick(cb, (c + 1 : U32), c),
           cb, s, ylam, wk_step(st, ann, c, s, ylam, w))

def wk_run(+st: I.IS, +ann: List<&2, U32>, +k: U32, +cb: Bool, +s: U32,
           +ylam: Bool, +w: WK) -> WK:
  wk_n(4096n, U32.is_ne(k, 0), st, ann, k, 0, cb, s, ylam, w)

# x's cursor past k Pi binders (no comparison)
def skip_pis(fuel: Nat, +go: Bool, +st: I.IS, +k: U32, +x: U32) -> U32:
  match fuel go:
    case 0n _:
      4294967295
    case 1n+p False{}:
      x
    case 1n+p True{}:
      +k1 : U32 = (k - 1 : U32)
      skip_pis(p, U32.is_ne(k1, 0), st, k1, bnd_body(node(st, x)))

def skip_n(+st: I.IS, +k: U32, +x: U32) -> U32:
  skip_pis(4096n, U32.is_ne(k, 0), st, k, x)

# [lo + cnt - 1, ..., lo] in front of acc
def desc_go(fuel: Nat, +go: Bool, +lo: U32, +cnt: U32,
            +acc: List<&2, U32>) -> List<&2, U32>:
  match fuel go:
    case 0n _:
      acc
    case 1n+p False{}:
      acc
    case 1n+p True{}:
      +c1 : U32 = (cnt - 1 : U32)
      desc_go(p, U32.is_ne(c1, 0), (lo + 1 : U32), c1, Con{lo, acc})

def desc(+lo: U32, +cnt: U32, +acc: List<&2, U32>) -> List<&2, U32>:
  desc_go(4096n, U32.is_ne(cnt, 0), lo, cnt, acc)

def is_bv(+x: T.Ex, +e: U32) -> Bool:
  match x:
    case T.EBVar{i}:
      U32.is_eq(i, e)
    case _:
      False{}

def bvs_eq(+st: I.IS, xs: List<&2, U32>, es: List<&2, U32>) -> Bool:
  match xs es:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{e, et}:
      is_bv(node(st, x), e) && bvs_eq(st, xt, et)
    case _ _:
      False{}

# level ids that are exactly the parameters `ns`
def lvl_params(+lnt: R.Tr<L.LN>, us: List<&2, U32>, ns: List<&2, U32>) -> Bool:
  match us ns:
    case Nil{} Nil{}:
      True{}
    case Con{u, ut} Con{n, nt}:
      L.tri_is_yes(L.ln_cmp(R.get(L.LN, 64n, lnt, u, L.LNun{}),
                            L.LNmax{[L.At{(n + 1 : U32), 0}]}))
      && lvl_params(lnt, ut, nt)
    case _ _:
      False{}

# `x` is `c.{lps} #e_1 .. #e_n` exactly
def capp(+st: I.IS, +x: U32, +c: U32, +lps: List<&2, U32>,
         +es: List<&2, U32>) -> Bool:
  +h : T.Ex = spine_hd(st, x)
  U32.is_eq(I.const_nm2(h), c) && lvl_params(I.is_lnt(st), const_us(h), lps)
  && bvs_eq(st, spine_args(st, x), es)

# `x` is `#f a_1 .. a_n` with the a's the bvars es
def bapp(+st: I.IS, +x: U32, +f: U32, +es: List<&2, U32>) -> Bool:
  is_bv(spine_hd(st, x), f) && bvs_eq(st, spine_args(st, x), es)

def ctor_nf(items: List<&2, K.IItem>, +c: U32) -> U32:
  match items:
    case Nil{}:
      4294967295
    case Con{K.ICtor{nm, lps, ty, ind, np, nf, ci}, t}:
      S.pick(U32.is_eq(nm, c), nf, ctor_nf(t, c))
    case Con{h, t}:
      ctor_nf(t, c)

def rule_rhs(items: List<&2, K.IItem>, +c: U32) -> U32:
  match items:
    case Nil{}:
      4294967295
    case Con{K.IRule{ct, nf, rhs}, t}:
      S.pick(U32.is_eq(ct, c), rhs, rule_rhs(t, c))
    case Con{h, t}:
      rule_rhs(t, c)

def rule_nf(items: List<&2, K.IItem>, +c: U32) -> U32:
  match items:
    case Nil{}:
      4294967295
    case Con{K.IRule{ct, nf, rhs}, t}:
      S.pick(U32.is_eq(ct, c), nf, rule_nf(t, c))
    case Con{h, t}:
      rule_nf(t, c)

# Does a constant of `tn` occur in x? Memoised on the DAG (vis: nodes known
# not to mention it); out of fuel counts as an occurrence.
type OV is Data:
  OV{f: Bool, vis: R.Tr<U32>}

def ov_f(+r: OV) -> Bool:
  match r:
    case OV{f, vis}:
      f

def ov_vis(+r: OV) -> R.Tr<U32>:
  match r:
    case OV{f, vis}:
      vis

def ov_mark(+f: Bool, +x: U32, +vis: R.Tr<U32>) -> OV:
  match f:
    case True{}:
      OV{True{}, vis}
    case False{}:
      OV{False{}, R.set(U32, 64n, vis, x, 1, 0)}

def occ_dag(+fuel: Nat, +st: I.IS, +x: U32, +tn: List<&2, U32>, +seen: Bool,
            +nd: T.Ex, +vis: R.Tr<U32>) -> OV:
  match fuel seen nd:
    case 0n _ _:
      OV{True{}, vis}
    case 1n+p True{} _:
      OV{False{}, vis}
    case 1n+p False{} T.EConst{n, us}:
      OV{mem(n, tn), vis}
    case 1n+p False{} T.EApp{f, a}:
      +r1 = occ_dag(p, st, f, tn, U32.is_eq(R.get(U32, 64n, vis, f, 0), 1),
                    node(st, f), vis)
      +v1 = ov_vis(r1)
      +r2 = occ_dag(p, st, a, tn, U32.is_eq(R.get(U32, 64n, v1, a, 0), 1),
                    node(st, a), v1)
      ov_mark(ov_f(r1) || ov_f(r2), x, ov_vis(r2))
    case 1n+p False{} T.ELam{n, t, b, bi}:
      +r1 = occ_dag(p, st, t, tn, U32.is_eq(R.get(U32, 64n, vis, t, 0), 1),
                    node(st, t), vis)
      +v1 = ov_vis(r1)
      +r2 = occ_dag(p, st, b, tn, U32.is_eq(R.get(U32, 64n, v1, b, 0), 1),
                    node(st, b), v1)
      ov_mark(ov_f(r1) || ov_f(r2), x, ov_vis(r2))
    case 1n+p False{} T.EAll{n, t, b, bi}:
      +r1 = occ_dag(p, st, t, tn, U32.is_eq(R.get(U32, 64n, vis, t, 0), 1),
                    node(st, t), vis)
      +v1 = ov_vis(r1)
      +r2 = occ_dag(p, st, b, tn, U32.is_eq(R.get(U32, 64n, v1, b, 0), 1),
                    node(st, b), v1)
      ov_mark(ov_f(r1) || ov_f(r2), x, ov_vis(r2))
    case 1n+p False{} T.ELet{n, t, v, b}:
      +r1 = occ_dag(p, st, t, tn, U32.is_eq(R.get(U32, 64n, vis, t, 0), 1),
                    node(st, t), vis)
      +v1 = ov_vis(r1)
      +r2 = occ_dag(p, st, v, tn, U32.is_eq(R.get(U32, 64n, v1, v, 0), 1),
                    node(st, v), v1)
      +v2 = ov_vis(r2)
      +r3 = occ_dag(p, st, b, tn, U32.is_eq(R.get(U32, 64n, v2, b, 0), 1),
                    node(st, b), v2)
      ov_mark(ov_f(r1) || ov_f(r2) || ov_f(r3), x, ov_vis(r3))
    case 1n+p False{} T.EProj{pn, i, s}:
      +r1 = occ_dag(p, st, s, tn, U32.is_eq(R.get(U32, 64n, vis, s, 0), 1),
                    node(st, s), vis)
      ov_mark(ov_f(r1), x, ov_vis(r1))
    case 1n+p False{} _:
      OV{False{}, vis}

def occ_x(+st: I.IS, +x: U32, +tn: List<&2, U32>, +vis: R.Tr<U32>) -> OV:
  occ_dag(65536n, st, x, tn, U32.is_eq(R.get(U32, 64n, vis, x, 0), 1),
          node(st, x), vis)

# the field domains of a constructor type (past np params, nf fields)
def occ_fields(fuel: Nat, +go: Bool, +st: I.IS, +x: U32, +k: U32,
               +tn: List<&2, U32>, +r: OV) -> OV:
  match fuel go:
    case 0n _:
      OV{True{}, ov_vis(r)}
    case 1n+p False{}:
      r
    case 1n+p True{}:
      +nd : T.Ex = node(st, x)
      +o = occ_x(st, bnd_dom(nd), tn, ov_vis(r))
      +k1 : U32 = (k - 1 : U32)
      occ_fields(p, U32.is_ne(k1, 0), st, bnd_body(nd), k1, tn,
                 OV{ov_f(r) || ov_f(o) || Bool.not(is_pi(nd)), ov_vis(o)})

def occ_ctors(cs: List<&2, U32>, +items: List<&2, K.IItem>, +st: I.IS,
              +np: U32, +tn: List<&2, U32>, +r: OV) -> OV:
  match cs:
    case Nil{}:
      r
    case Con{c0, t}:
      +c : U32 = c0
      +nf : U32 = ctor_nf(items, c)
      +x : U32 = skip_n(st, np, find_ctor_ty(items, c))
      occ_ctors(t, items, st, np, tn,
                occ_fields(4096n, U32.is_ne(nf, 0), st, x, nf, tn, r))

# the minors of the recursor type: k counts from 1; mins collects the
# minors' domains (for the rules)
type MW is Data:
  MW{w: WK, mins: List<&2, U32>}

def mw_w(+r: MW) -> WK:
  match r:
    case MW{w, mins}:
      w

def mw_mins(+r: MW) -> List<&2, U32>:
  match r:
    case MW{w, mins}:
      mins

# motive (c params fields): motive is #(nf + k - 1)
def minor_res(+st: I.IS, +nb: T.Ex, +nf: U32, +k: U32, +c: U32,
              +lps: List<&2, U32>, +np: U32) -> Bool:
  match nb:
    case T.EApp{f, a}:
      is_bv(node(st, f), (nf + k - 1 : U32))
      && capp(st, a, c, lps, desc((nf + k : U32), np, desc(0, nf, Nil{})))
    case _:
      False{}

def minors_v(cs: List<&2, U32>, +k: U32, +items: List<&2, K.IItem>,
             +st: I.IS, +ann: List<&2, U32>, +np: U32, +lps: List<&2, U32>,
             +r: MW) -> MW:
  match cs:
    case Nil{}:
      r
    case Con{c0, t}:
      +c : U32 = c0
      +w = mw_w(r)
      +nf : U32 = ctor_nf(items, c)
      +ny : T.Ex = node(st, wk_y(w))
      +md : U32 = bnd_dom(ny)
      # the minor's field binders against the constructor's
      +fw = wk_run(st, ann, nf, True{}, k, False{},
                   WK{wk_ok(w) && is_pi(ny), wk_m(w),
                      skip_n(st, np, find_ctor_ty(items, c)), md})
      # motive (c params fields): motive is #(nf + k - 1)
      +bd : U32 = wk_y(fw)
      +nb : T.Ex = node(st, bd)
      +ok2 : Bool = minor_res(st, nb, nf, k, c, lps, np)
      minors_v(t, (k + 1 : U32), items, st, ann, np, lps,
               MW{WK{wk_ok(fw) && ok2, wk_m(fw), wk_x(w), bnd_body(ny)},
                  List.append(&2, U32, mw_mins(r), [md])})

# the rule rhs's lambdas over the minors: each domain the recursor's
def rule_minors(ms: List<&2, U32>, +st: I.IS, +w: WK) -> WK:
  match ms:
    case Nil{}:
      w
    case Con{md0, t}:
      +md : U32 = md0
      +ny : T.Ex = node(st, wk_y(w))
      +r = sq(st, md, bnd_dom(ny), 0, 0, wk_m(w))
      rule_minors(t, st, WK{wk_ok(w) && is_lam(ny) && sm_ok(r), sm_m(r),
                            wk_x(w), bnd_body(ny)})

def rules_v(cs: List<&2, U32>, +k: U32, +nc: U32,
            +items: List<&2, K.IItem>, +st: I.IS, +ann: List<&2, U32>,
            +np: U32, +ity: U32, +mdom: U32, +mins: List<&2, U32>,
            +w: WK) -> WK:
  match cs:
    case Nil{}:
      w
    case Con{c0, t}:
      +c : U32 = c0
      +nf : U32 = ctor_nf(items, c)
      +rhs : U32 = rule_rhs(items, c)
      # params: the inductive's, unshifted
      +pw = wk_run(st, ann, np, False{}, 0, True{},
                   WK{wk_ok(w) && U32.is_eq(rule_nf(items, c), nf), wk_m(w),
                      ity, rhs})
      # motive
      +nm : T.Ex = node(st, wk_y(pw))
      +rm = sq(st, mdom, bnd_dom(nm), 0, 0, wk_m(pw))
      +mw = rule_minors(mins, st,
                        WK{wk_ok(pw) && is_lam(nm) && sm_ok(rm), sm_m(rm), 0,
                           bnd_body(nm)})
      # fields, shifted past the motive and the minors
      +fw = wk_run(st, ann, nf, True{}, (nc + 1 : U32), True{},
                   WK{wk_ok(mw), wk_m(mw),
                      skip_n(st, np, find_ctor_ty(items, c)), wk_y(mw)})
      # minor_k fields: minor_k is #(nf + nc - k)
      +ok2 : Bool = bapp(st, wk_y(fw), (nf + nc - k : U32), desc(0, nf, Nil{}))
      rules_v(t, (k + 1 : U32), nc, items, st, ann, np, ity, mdom, mins,
              WK{wk_ok(fw) && ok2, wk_m(fw), 0, 0})

def rec_item(items: List<&2, K.IItem>) -> K.IItem:
  match items:
    case Nil{}:
      K.IOther{}
    case Con{K.IRec{nm, lps, ty, np, ni, nmo, kf}, t}:
      K.IRec{nm, lps, ty, np, ni, nmo, kf}
    case Con{h, t}:
      rec_item(t)

def ir_ty(+x: K.IItem) -> U32:
  match x:
    case K.IRec{nm, lps, ty, np, ni, nmo, kf}:
      ty
    case _:
      4294967295

def ir_lps(+x: K.IItem) -> List<&2, U32>:
  match x:
    case K.IRec{nm, lps, ty, np, ni, nmo, kf}:
      lps
    case _:
      Nil{}

def ir_shape(+x: K.IItem, +np: U32) -> Bool:
  match x:
    case K.IRec{nm, lps, ty, np2, ni, nmo, kf}:
      U32.is_eq(np2, np) && U32.is_eq(ni, 0) && U32.is_eq(nmo, 1)
    case _:
      False{}

def elim_ln(+large: Bool, +rlps: List<&2, U32>) -> L.LN:
  match large:
    case True{}:
      L.LNmax{[L.At{(I.nth_u(rlps, 0, 0) + 1 : U32), 0}]}
    case False{}:
      L.ln_zero()

def sort_is(+st: I.IS, +x: T.Ex, +u: L.LN) -> Bool:
  match x:
    case T.ESort{l}:
      L.tri_is_yes(L.ln_cmp(R.get(L.LN, 64n, I.is_lnt(st), l, L.LNun{}), u))
    case _:
      False{}

# One inductive, no indices, not nested? (the caller's nb = False says the
# last two; the occurrence test is done here)
def simple_ok(+items: List<&2, K.IItem>, +st: I.IS,
              +ann: List<&2, U32>) -> Bool:
  +inds = ind_items(items)
  +i0 = first_ind(inds)
  +tn : List<&2, U32> = ind_names(inds)
  +np : U32 = ii_np(i0)
  +lps : List<&2, U32> = ii_lps(i0)
  +ity : U32 = ii_ty(i0)
  +cs : List<&2, U32> = ii_cs(i0)
  +nc : U32 = I.len_u(cs, 0)
  +elig : Bool = U32.is_eq(I.len_u(tn, 0), 1) && U32.is_eq(ii_ni(i0), 0)
                 && U32.is_eq(ii_nn(i0), 0)
                 && U32.is_eq(count_recs(items, 0), 1)
                 && U32.is_eq(count_rules(items, 0), nc)
  +o = occ_ctors(cs, items, st, np, tn, OV{False{}, R.TNil{}})
  +ri = rec_item(items)
  +rlps : List<&2, U32> = ir_lps(ri)
  +large : Bool = U32.is_eq(I.len_u(rlps, 0), (I.len_u(lps, 0) + 1 : U32))
  +lvok : Bool = S.pick_b(large, I.eq_u32s(I.skip_u(rlps, 1), lps),
                          I.eq_u32s(rlps, lps))
  +elim : L.LN = elim_ln(large, rlps)
  # params
  +pw = wk_run(st, ann, np, False{}, 0, False{},
               WK{elig && Bool.not(ov_f(o)) && lvok && ir_shape(ri, np),
                  R.TNil{}, ity, ir_ty(ri)})
  # motive : T params -> Sort elim
  +nm : T.Ex = node(st, wk_y(pw))
  +mdom : U32 = bnd_dom(nm)
  +nmd : T.Ex = node(st, mdom)
  +mok : Bool = is_pi(nm) && is_pi(nmd)
                && capp(st, bnd_dom(nmd), I.nth_u(tn, 0, 0), lps,
                        desc(0, np, Nil{}))
                && sort_is(st, node(st, bnd_body(nmd)), elim)
  +mw = minors_v(cs, 1, items, st, ann, np, lps,
                 MW{WK{wk_ok(pw) && mok, wk_m(pw), 0, bnd_body(nm)}, Nil{}})
  +w2 = mw_w(mw)
  # major : T params, result motive major
  +nj : T.Ex = node(st, wk_y(w2))
  +jok : Bool = is_pi(nj)
                && capp(st, bnd_dom(nj), I.nth_u(tn, 0, 0), lps,
                        desc((nc + 1 : U32), np, Nil{}))
                && bapp(st, bnd_body(nj), (nc + 1 : U32), [0])
  +rw = rules_v(cs, 1, nc, items, st, ann, np, ity, mdom, mw_mins(mw),
                WK{wk_ok(w2) && jok, wk_m(w2), 0, 0})
  wk_ok(rw)
