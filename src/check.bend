# The checker, over reusable tries.
#
# Every answer is three-valued: accept, reject, or decline. Decline is the
# honest answer when a check cannot be decided, and keeping it apart from
# reject is load-bearing in both directions -- folding "cannot decide" into
# "not equal" once rejected nine valid proofs, and returning accept after one
# partial check once accepted nine invalid ones.
#
# `sl x ctx` is the level l with `infer x = Sort l`, i.e. the universe of a
# type. It is the one piece of real inference that needs no substitution, no
# beta and no definitional equality, because **a level is invariant under
# substitution**: the universe of `ctx[i]` can be read in the truncated
# context without lifting any de Bruijn index. That is what makes the Pi
# fragment -- arrow types, dependent types, imax -- decidable here.

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
import ./nested.bend as N

type V is Data:
  VAccept{}
  VReject{}
  VDecline{}

def comb(+a: V, +b: V) -> V:
  match a b:
    case VReject{} _:
      VReject{}
    case _ VReject{}:
      VReject{}
    case VDecline{} _:
      VDecline{}
    case _ VDecline{}:
      VDecline{}
    case _ _:
      VAccept{}

def tri_v(+t: L.Tri) -> V:
  match t:
    case L.TYes{}:
      VAccept{}
    case L.TNo{}:
      VReject{}
    case L.TUnk{}:
      VDecline{}

def bad_v(+bad: Bool) -> V:
  match bad:
    case True{}:
      VReject{}
    case False{}:
      VAccept{}

def pick_v(+z: Bool, +x: V, +y: V) -> V:
  match z:
    case True{}:
      x
    case False{}:
      y

# --- uniqueness ----------------------------------------------------------
def mem(+v: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{head, tail}:
      U32.is_eq(head, v) || mem(v, tail)

# one pass with a trie of the names seen so far (a pairwise `mem` scan was
# quadratic: 44 s of init's 58k declarations)
def has_dup_go(xs: List<&2, U32>, +hit: Bool, +seen: R.Tr<Bool>) -> Bool:
  match xs:
    case Nil{}:
      hit
    case Con{head, tail}:
      match hit:
        case True{}:
          True{}
        case False{}:
          +h = head
          has_dup_go(tail, R.get(Bool, 64n, seen, h, False{}),
                     R.set(Bool, 64n, seen, h, True{}, False{}))

def has_dup(xs: List<&2, U32>) -> Bool:
  has_dup_go(xs, False{}, R.TNil{})

def dcl_all_nms(+d: K.Dcl) -> List<&2, U32>:
  match d:
    case K.DInd{nms, items}:
      nms
    case _:
      T.cons_if(U32.is_gt(K.dcl_name(d), 0), K.dcl_name(d), Nil{})

def names_of(ds: List<&2, K.Dcl>, acc: List<&2, U32>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      acc
    case Con{head, tail}:
      names_of(tail, List.append(&2, U32, dcl_all_nms(head), acc))

def item_lps(+it: K.IItem) -> List<&2, U32>:
  match it:
    case K.IInd{nm, lps, ty, np, ni, nn, cs}:
      lps
    case K.ICtor{nm, lps, ty, ind, np, nf, ci}:
      lps
    case K.IRec{nm, lps, ty, np, ni, nmo, kf}:
      lps
    case _:
      Nil{}

def items_dup_lps(items: List<&2, K.IItem>) -> Bool:
  match items:
    case Nil{}:
      False{}
    case Con{head, tail}:
      has_dup(item_lps(head)) || items_dup_lps(tail)

def dcl_items_of(+d: K.Dcl) -> List<&2, K.IItem>:
  match d:
    case K.DInd{nms, items}:
      items
    case _:
      Nil{}

def any_dup_lps(ds: List<&2, K.Dcl>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{head, tail}:
      +h = head
      has_dup(K.dcl_lparams(h)) || items_dup_lps(dcl_items_of(h))
      || any_dup_lps(tail)

def pre_check(+ds: List<&2, K.Dcl>) -> V:
  bad_v(has_dup(names_of(ds, Nil{})) || any_dup_lps(ds))

# --- unknown constants ---------------------------------------------------
def mark_names(ns: List<&2, U32>, +t: R.Tr<Bool>) -> R.Tr<Bool>:
  match ns:
    case Nil{}:
      t
    case Con{head, tail}:
      mark_names(tail, R.set(Bool, 64n, t, head, True{}, False{}))

def declared(ds: List<&2, K.Dcl>, acc: List<&2, U32>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      acc
    case Con{head, tail}:
      declared(tail, List.append(&2, U32, dcl_all_nms(head), acc))

def const_nm_of(+x: T.Ex) -> U32:
  match x:
    case T.EConst{n, us}:
      n
    case _:
      0

def bad_const_at(+i: U32, +ex: R.Tr<T.Ex>, +dn: R.Tr<Bool>) -> Bool:
  +x = R.get(T.Ex, 64n, ex, i, T.EBad{})
  U32.is_gt(const_nm_of(x), 0)
  && Bool.not(R.get(Bool, 64n, dn, const_nm_of(x), False{}))

def scan_consts(n: Nat, +i: U32, +ex: R.Tr<T.Ex>, +dn: R.Tr<Bool>,
                +bad: Bool) -> Bool:
  match n:
    case 0n:
      bad
    case 1n+p:
      scan_consts(p, (i + 1 : U32), ex, dn,
                  bad || bad_const_at(i, ex, dn))

# --- inductive declarations ---------------------------------------------
def tele_n(fuel: Nat, +ex: R.Tr<T.Ex>, +x: T.Ex, +cnt: U32) -> U32:
  match fuel x:
    case 0n _:
      cnt
    case 1n+p T.EAll{n, t, b, bi}:
      tele_n(p, ex, R.get(T.Ex, 64n, ex, b, T.EBad{}), (cnt + 1 : U32))
    case 1n+p _:
      cnt

def tele_res(fuel: Nat, +ex: R.Tr<T.Ex>, +x: T.Ex) -> T.Ex:
  match fuel x:
    case 0n _:
      T.EBad{}
    case 1n+p T.EAll{n, t, b, bi}:
      tele_res(p, ex, R.get(T.Ex, 64n, ex, b, T.EBad{}))
    case 1n+p y:
      y

def sort_res_tri(+x: T.Ex) -> L.Tri:
  match x:
    case T.ESort{l}:
      L.TYes{}
    case T.ELam{n, t, b, bi}:
      L.TNo{}
    case T.ENat{d}:
      L.TNo{}
    case T.EStr{d}:
      L.TNo{}
    case _:
      L.TUnk{}

# Never accepts: a well-formed telescope is one property out of many, with
# constructor result types, positivity and the recursors all still unchecked.
# This may accept now: a block's overall verdict is the combination of every
# check, and the recursor is derived rather than trusted, so "all checks
# passed" is real evidence.
def ind_item_v(+t: L.Tri, +enough: Bool) -> V:
  match t:
    case L.TNo{}:
      VReject{}
    case L.TUnk{}:
      VDecline{}
    case L.TYes{}:
      pick_v(enough, VAccept{}, VReject{})

# An inductive's telescope must end in a Sort. `sort_res_tri` decides the
# syntactic cases; `not_a_type` additionally looks through a constant to its
# declared type, which is what `tutorial/046_inductBadNonSort` and `047` need
# -- their inductive's type is `constType`, whose own type is
# `Type -> Type -> Type`, so it is not a type at all, let alone a Sort.
# A constant with no value cannot unfold, so if the telescope ends in one it
# is stuck and is not a Sort. `tutorial/047_inductBadNonSort2` declares
# `inductive X : aType` where `aType` is an axiom: a perfectly good type, but
# not a Sort and unable to become one.
def stuck_const(+vt: R.Tr<U32>, +x: T.Ex) -> Bool:
  match x:
    case T.EConst{n, us}:
      U32.is_eq(R.get(U32, 64n, vt, n, 4294967295), 4294967295)
    case _:
      False{}

def ind_res_tri(+ex: R.Tr<T.Ex>, +nt: R.Tr<U32>, +vt: R.Tr<U32>,
                +res: T.Ex) -> L.Tri:
  L.pick_tri(I.not_a_type(ex, nt, res) || stuck_const(vt, res), L.TNo{},
             sort_res_tri(res))

def ind_one(+ex: R.Tr<T.Ex>, +nt: R.Tr<U32>, +vt: R.Tr<U32>,
            +it: K.IItem) -> V:
  match it:
    case K.IInd{nm, lps, ty, np, ni, nn, cs}:
      +x = R.get(T.Ex, 64n, ex, ty, T.EBad{})
      ind_item_v(ind_res_tri(ex, nt, vt, tele_res(256n, ex, x)),
                 U32.is_ge(tele_n(256n, ex, x, 0), (np + ni : U32)))
    # Not an inductive type: not this check's business. Declining here made
    # every block decline, because a block always also contains its
    # constructors and its recursors.
    case _:
      VAccept{}

def ind_items(items: List<&2, K.IItem>, +ex: R.Tr<T.Ex>, +nt: R.Tr<U32>,
              +vt: R.Tr<U32>, +acc: V) -> V:
  match items:
    case Nil{}:
      acc
    case Con{head, tail}:
      ind_items(tail, ex, nt, vt, comb(acc, ind_one(ex, nt, vt, head)))


# --- constructor shape --------------------------------------------------
# A constructor's type is a telescope whose result is the inductive type
# being declared, applied to its parameters and indices. When the result is
# headed by some OTHER constant, the declaration is invalid -- that is
# `tutorial/050_inductWrongCtorParams`, `051`, `052` ("invalid occurrence of
# datatype being declared") and `053_inductInIndex` ("invalid return type").
#
# A result not headed by a constant at all declines: it might reduce, and
# this does not reduce it.
def spine_head(+fuel: Nat, +ex: R.Tr<T.Ex>, +x: T.Ex) -> T.Ex:
  match fuel x:
    case 0n _:
      T.EBad{}
    case 1n+p T.EApp{f, a}:
      spine_head(p, ex, U.ex_at(ex, f))
    case 1n+p y:
      y

def ind_names_of(items: List<&2, K.IItem>, acc: List<&2, U32>) -> List<&2, U32>:
  match items:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case K.IInd{nm, lps, ty, np, ni, nn, cs}:
          ind_names_of(tail, Con{nm, acc})
        case _:
          ind_names_of(tail, acc)

def is_constx(+x: T.Ex) -> Bool:
  match x:
    case T.EConst{n, us}:
      True{}
    case _:
      False{}

def const_name_of(+x: T.Ex) -> U32:
  match x:
    case T.EConst{n, us}:
      n
    case _:
      0

# The head being the datatype being declared is now an accept, not a
# decline: the parameter positions, the indices and strict positivity are
# separate checks combined alongside this one, so this one no longer has to
# hedge on their behalf.
def ctor_shape_v(+isc: Bool, +ok: Bool, +names: List<&2, U32>,
                 +hd: T.Ex) -> V:
  match isc:
    case False{}:
      VDecline{}
    case True{}:
      pick_v(is_constx(hd),
             pick_v(mem(const_name_of(hd), names), VAccept{}, VReject{}),
             VDecline{})


# --- parameter positions and positivity ---------------------------------
# A constructor `c : (p1 .. pn) -> (fields) -> I p1 .. pn indices` must apply
# the inductive to its OWN bound parameters, in order. Under k traversed
# binders the i-th parameter is `bvar (k-1-i)`.
#   tutorial/050_inductWrongCtorParams applies it to a constant instead.
#   tutorial/051_inductWrongCtorResParams swaps two of them.
# And the inductive may not occur in a field's domain -- that is strict
# positivity, and `tutorial/054_indNeg` declares `C1` with a field of type
# `C1 -> C1`.
#
# Both reject only on a rigid mismatch. An argument that is an application
# might reduce, and nothing here reduces it, so that declines.
def spine_args(+fuel: Nat, +ex: R.Tr<T.Ex>, +x: T.Ex,
               acc: List<&2, U32>) -> List<&2, U32>:
  match fuel x:
    case 0n _:
      acc
    case 1n+p T.EApp{f, a}:
      spine_args(p, ex, U.ex_at(ex, f), Con{a, acc})
    case 1n+p _:
      acc

def tele_doms(+fuel: Nat, +ex: R.Tr<T.Ex>, +x: T.Ex,
              acc: List<&2, U32>) -> List<&2, U32>:
  match fuel x:
    case 0n _:
      acc
    case 1n+p T.EAll{n, t, b, bi}:
      tele_doms(p, ex, U.ex_at(ex, b), Con{t, acc})
    case 1n+p _:
      acc

# Occurrence, memoised and three-valued.
#
# Two defects in the naive version. It recursed structurally over a DAG with
# heavy sharing and no memo, so `perf/app-lam` went from 0.13 s to a 100 s
# timeout. And on fuel exhaustion it answered "does not occur", which for a
# positivity check means "positive" -- a latent unsoundness that could accept
# a non-positive inductive. Running out of budget now answers "cannot
# decide".
#
# The memo codes are 0 unknown, 1 no, 2 yes, 3 cannot decide. A hit is
# consumed by passing fuel 0 with the answer as the accumulator, because
# returning early would need a helper that calls back.
type OM is Data:
  OM{m: R.Tr<U32>, r: L.Tri}

def om_m(+o: OM) -> R.Tr<U32>:
  match o:
    case OM{m, r}:
      m

def om_r(+o: OM) -> L.Tri:
  match o:
    case OM{m, r}:
      r

def occ_code(+t: L.Tri) -> U32:
  match t:
    case L.TNo{}:
      1
    case L.TYes{}:
      2
    case L.TUnk{}:
      3

def occ_tri(+c: U32) -> L.Tri:
  L.pick_tri(U32.is_eq(c, 1), L.TNo{},
             L.pick_tri(U32.is_eq(c, 2), L.TYes{}, L.TUnk{}))

def tri_or(+a: L.Tri, +b: L.Tri) -> L.Tri:
  match a b:
    case L.TYes{} _:
      L.TYes{}
    case _ L.TYes{}:
      L.TYes{}
    case L.TUnk{} _:
      L.TUnk{}
    case _ L.TUnk{}:
      L.TUnk{}
    case _ _:
      L.TNo{}

# The memo bookkeeping is inlined per case rather than factored out: a
# shared helper would call `occ_go` back, and Bend forbids mutual recursion.
# A memo hit is signalled by `skip` rather than by shortening the fuel,
# because the termination checker requires the fuel to shrink structurally
# and will not accept a computed one.
def occ_go(+fuel: Nat, +skip: Bool, +ex: R.Tr<T.Ex>,
           +names: List<&2, U32>, +m: R.Tr<U32>, +acc: L.Tri,
           +x: T.Ex) -> OM:
  match fuel skip x:
    case 0n _ _:
      OM{m, acc}
    case 1n+p True{} _:
      OM{m, acc}
    case 1n+p False{} T.EConst{n, us}:
      OM{m, L.pick_tri(mem(n, names), L.TYes{}, L.TNo{})}
    case 1n+p False{} T.EApp{f, a}:
      +pf = p
      +h1 = R.get(U32, 64n, m, f, 0)
      +r1 = occ_go(pf, U32.is_ne(h1, 0), ex, names, m, occ_tri(h1),
                   U.ex_at(ex, f))
      +m1 = R.set(U32, 64n, om_m(r1), f, occ_code(om_r(r1)), 0)
      +h2 = R.get(U32, 64n, m1, a, 0)
      +r2 = occ_go(pf, U32.is_ne(h2, 0), ex, names, m1, occ_tri(h2),
                   U.ex_at(ex, a))
      OM{R.set(U32, 64n, om_m(r2), a, occ_code(om_r(r2)), 0),
         tri_or(om_r(r1), om_r(r2))}
    case 1n+p False{} T.EAll{n, t, b, bi}:
      +pf = p
      +h1 = R.get(U32, 64n, m, t, 0)
      +r1 = occ_go(pf, U32.is_ne(h1, 0), ex, names, m, occ_tri(h1),
                   U.ex_at(ex, t))
      +m1 = R.set(U32, 64n, om_m(r1), t, occ_code(om_r(r1)), 0)
      +h2 = R.get(U32, 64n, m1, b, 0)
      +r2 = occ_go(pf, U32.is_ne(h2, 0), ex, names, m1, occ_tri(h2),
                   U.ex_at(ex, b))
      OM{R.set(U32, 64n, om_m(r2), b, occ_code(om_r(r2)), 0),
         tri_or(om_r(r1), om_r(r2))}
    case 1n+p False{} T.ELam{n, t, b, bi}:
      +pf = p
      +h1 = R.get(U32, 64n, m, t, 0)
      +r1 = occ_go(pf, U32.is_ne(h1, 0), ex, names, m, occ_tri(h1),
                   U.ex_at(ex, t))
      +m1 = R.set(U32, 64n, om_m(r1), t, occ_code(om_r(r1)), 0)
      +h2 = R.get(U32, 64n, m1, b, 0)
      +r2 = occ_go(pf, U32.is_ne(h2, 0), ex, names, m1, occ_tri(h2),
                   U.ex_at(ex, b))
      OM{R.set(U32, 64n, om_m(r2), b, occ_code(om_r(r2)), 0),
         tri_or(om_r(r1), om_r(r2))}
    case 1n+p False{} T.ELet{n, t, v, b}:
      +pf = p
      +h1 = R.get(U32, 64n, m, v, 0)
      +r1 = occ_go(pf, U32.is_ne(h1, 0), ex, names, m, occ_tri(h1),
                   U.ex_at(ex, v))
      +m1 = R.set(U32, 64n, om_m(r1), v, occ_code(om_r(r1)), 0)
      +h2 = R.get(U32, 64n, m1, b, 0)
      +r2 = occ_go(pf, U32.is_ne(h2, 0), ex, names, m1, occ_tri(h2),
                   U.ex_at(ex, b))
      OM{R.set(U32, 64n, om_m(r2), b, occ_code(om_r(r2)), 0),
         tri_or(om_r(r1), om_r(r2))}
    case 1n+p False{} T.EProj{tn, i, sx}:
      +pf = p
      +h1 = R.get(U32, 64n, m, sx, 0)
      +r1 = occ_go(pf, U32.is_ne(h1, 0), ex, names, m, occ_tri(h1),
                   U.ex_at(ex, sx))
      OM{R.set(U32, 64n, om_m(r1), sx, occ_code(om_r(r1)), 0), om_r(r1)}
    case 1n+p False{} _:
      OM{m, L.TNo{}}

def occurs_tri(+ex: R.Tr<T.Ex>, +names: List<&2, U32>, +x: T.Ex) -> L.Tri:
  # The walk is memoised, so the fuel bounds DEPTH, not cost -- and the
  # `perf` files are deep: `folded-constant-last` carries 1000-deep
  # numerals, `app-lam` 4000 nested binders over a 4000-deep sum. 8192 was
  # not enough for the latter; the bound only guards the C stack.
  om_r(occ_go(262144n, False{}, ex, names, R.TNil{}, L.TUnk{}, x))

# A bound variable with the wrong index, or anything else rigid, is a real
# mismatch; an application or a let might reduce and so declines.
def arg_v(+x: T.Ex, +want: U32) -> V:
  match x:
    case T.EBVar{i}:
      pick_v(U32.is_eq(i, want), VAccept{}, VReject{})
    case T.EConst{n, us}:
      VReject{}
    case T.ESort{l}:
      VReject{}
    case _:
      VDecline{}

# The first `np` arguments must be the constructor's own bound parameters, in
# order. The arguments after them are the indices, and the inductive being
# declared may not occur in those at all -- that is
# `tutorial/053_inductInIndex`, whose constructor returns
# `inductInIndex (inductInIndex aProp)`, and `118_reflOccInIndex`.
# An occurrence is a reject, its absence an accept, and "cannot decide" a
# decline -- the same discipline as everywhere else.
def neg_v(+t: L.Tri) -> V:
  match t:
    case L.TYes{}:
      VReject{}
    case L.TNo{}:
      VAccept{}
    case L.TUnk{}:
      VDecline{}

def index_v(+ex: R.Tr<T.Ex>, +names: List<&2, U32>, +ai: U32) -> V:
  neg_v(occurs_tri(ex, names, U.ex_at(ex, ai)))

def params_v(args: List<&2, U32>, +ex: R.Tr<T.Ex>, +k: U32, +i: U32,
             +np: U32, +names: List<&2, U32>, +acc: V) -> V:
  match args:
    case Nil{}:
      acc
    case Con{head, tail}:
      +pi = i
      +ph = head
      params_v(tail, ex, k, (pi + 1 : U32), np, names,
               comb(acc,
                    pick_v(U32.is_ge(pi, np),
                           index_v(ex, names, ph),
                           arg_v(U.ex_at(ex, ph), (k - 1 - pi : U32)))))

# Strict positivity constrains where the inductive may appear INSIDE a
# field's type, not whether a field may mention it at all. A recursive field
# like `Nat.succ : Nat -> Nat` has the inductive as its whole field type and
# is perfectly legal; what is forbidden is the inductive occurring in a
# domain of the field's own telescope, as in `tutorial/054_indNeg`, whose
# field has type `C1 -> C1`.
#
# Conflating the two rejected 46 valid files -- every inductive with a
# recursive constructor, which is nearly all of them.
def any_dom_occurs(doms: List<&2, U32>, +ex: R.Tr<T.Ex>,
                   +names: List<&2, U32>, +acc: L.Tri) -> L.Tri:
  match doms:
    case Nil{}:
      acc
    case Con{head, tail}:
      any_dom_occurs(tail, ex, names,
                     tri_or(acc, occurs_tri(ex, names,
                                            U.ex_at(ex, head))))

def field_pos_v(+ex: R.Tr<T.Ex>, +names: List<&2, U32>, +fi: U32) -> V:
  neg_v(any_dom_occurs(tele_doms(256n, ex, U.ex_at(ex, fi), Nil{}), ex,
                       names, L.TNo{}))

def positivity_v(doms: List<&2, U32>, +ex: R.Tr<T.Ex>,
                 +names: List<&2, U32>, +nskip: U32, +i: U32,
                 +acc: V) -> V:
  match doms:
    case Nil{}:
      acc
    case Con{head, tail}:
      +pi = i
      positivity_v(tail, ex, names, nskip, (pi + 1 : U32),
                   pick_v(U32.is_lt(pi, nskip), acc,
                          comb(acc, field_pos_v(ex, names, head))))

def ctor_one(+ex: R.Tr<T.Ex>, +names: List<&2, U32>, +it: K.IItem) -> V:
  match it:
    case K.ICtor{nm, lps, ty, ind, np, nf, ci}:
      +tx = U.ex_at(ex, ty)
      +res = tele_res(256n, ex, tx)
      +k = tele_n(256n, ex, tx, 0)
      # `other/orphan-ctor` declares `rogue` with `induct` naming `Orphan`,
      # an inductive the block never declares. The kernel adds no such
      # constructor, so the later reference to it is an unknown constant.
      comb(comb(comb(pick_v(mem(ind, names), VAccept{}, VReject{}),
                     ctor_shape_v(True{}, True{}, names,
                                  spine_head(256n, ex, res))),
                params_v(spine_args(256n, ex, res, Nil{}), ex, k, 0, np,
                         names, VAccept{})),
           positivity_v(D.rev_u32(tele_doms(256n, ex, tx, Nil{}), Nil{}),
                        ex, names, np, 0, VAccept{}))
    case _:
      VAccept{}

def ctor_all(items: List<&2, K.IItem>, +ex: R.Tr<T.Ex>,
             +names: List<&2, U32>, +acc: V) -> V:
  match items:
    case Nil{}:
      acc
    case Con{head, tail}:
      ctor_all(tail, ex, names, comb(acc, ctor_one(ex, names, head)))

# A declaration may not name itself. Lean compiles recursion through
# `WellFounded.fix` or a structural recursor, so the kernel never sees a
# self-reference; `tutorial/014_selfProof` is a theorem whose proof is
# itself, and the official kernel answers "unknown constant" because the name
# is not in the environment while its own declaration is being checked.
def self_ref_v(+ex: R.Tr<T.Ex>, +d: K.Dcl) -> V:
  +nm = K.dcl_name(d)
  +ti = K.dcl_type(d)
  +vi = K.dcl_value(d)
  pick_v(U32.is_eq(nm, 0), VAccept{},
         neg_v(tri_or(occurs_tri(ex, [nm], U.ex_at(ex, ti)),
                      occurs_tri(ex, [nm], U.ex_at(ex, vi)))))


# --- recursor universe parameters ---------------------------------------
# A recursor gains one fresh universe parameter for its motive, but only when
# the inductive permits large elimination. A Prop-valued inductive does not,
# unless it is a subsingleton -- no constructors at all, or exactly one whose
# every field is itself a proposition.
#
#   bugs/large-elim-prop-bool: `NewBool` is a Prop with two constructors, and
#     its recursor claims one level parameter. "#0 expected, #1 provided".
#   bugs/large-elim-param: `MyBool` likewise, with `#1 expected, #2 provided`.
#   tutorial/073_BogusRecursor: a recursor with no level parameter and no
#     motive at all.
#
# `False.rec` is the interesting legitimate case: an empty Prop IS a
# subsingleton, so it does eliminate into any universe.
def count_ctors(items: List<&2, K.IItem>, +ind: U32, +acc: U32) -> U32:
  match items:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case K.ICtor{nm, lps, ty, ind2, np, nf, ci}:
          count_ctors(tail, ind,
                      S.pick(U32.is_eq(ind2, ind), (acc + 1 : U32), acc))
        case _:
          count_ctors(tail, ind, acc)

def list_len(xs: List<&2, U32>, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      list_len(tail, (acc + 1 : U32))

# Lean permits large elimination from a Prop with one constructor when every
# field is a proposition OR appears in the constructor's result -- which is
# how `Eq`, whose `refl : forall a, Eq a a` has the non-propositional field
# `a`, eliminates into any universe. That second clause needs an occurrence
# check over the result's arguments that tracks binder depth, and is not
# implemented, so a non-propositional field answers "cannot decide" rather
# than "no".
#
# Answering "no" instead rejected init-prelude, grind-ring-5 and both
# magma-string tests: every real prelude has an `Eq`.
# No longer softens, and that is the point. It used to turn "this field is
# definitely not a proposition" into "cannot decide", because answering
# honestly rejected `init-prelude`, `grind-ring-5` and both `magma-string`
# tests.
#
# That was a workaround for a gap in `sl`, not a fact about Lean. `sl` had no
# rule for applications, none for applications headed by a bound variable,
# and the inductive block's own names were not in scope while its
# constructors were checked -- so a constructor field whose type ended in
# `Eq ..` or in the inductive itself came back with an unknown universe, and
# a hard "no" built on an unknown is a wrong reject. With those three fixed,
# the honest answer is correct: the full suite reports WRONG: 0, and
# `init-prelude` -- the test this softening was introduced for -- now
# *accepts* rather than declining.
def prop_or_unknown(+t: L.Tri) -> L.Tri:
  t

# Is this constructor field a PROOF? Three-valued, and the middle case has to
# fall the right way.
#
# A field whose universe is a bare parameter `u` is a proof exactly when
# `u = 0`, which is not known when the recursor is derived. Lean resolves
# that conservatively -- it denies large elimination -- so "might not be a
# proof" must read as "not a proof" HERE, which is the opposite of what
# `ln_is_zero`'s "cannot decide" means on its own. `Exists {a : Sort u}` is
# the case: its field `w : a` has universe `u`, and `Exists.rec` is declared
# with no extra universe, so Lean denied it.
#
# A genuinely unknown universe -- `sl` answering `LNun`, meaning the type
# could not be read at all -- still declines. That distinction is the whole
# content of this function: "a parameter, so possibly not a proof" is a
# decision, "unreadable" is not.
def field_is_proof(+u: L.LN) -> L.Tri:
  L.pick_tri(L.is_un(u), L.TUnk{},
             L.pick_tri(L.tri_is_yes(L.ln_is_zero(u)), L.TYes{}, L.TNo{}))

# --- the subsingleton rule's index exception -----------------------------
# A Prop inductive with one constructor supports large elimination when every
# field of that constructor is EITHER a proof OR one of the index arguments
# of the constructor's result type. The second clause was missing, and it is
# the whole reason `Acc` works in Lean:
#
#   Acc.intro : forall {a} {r} (x : a), (forall y, r y x -> Acc r y)
#                 -> Acc r x
#
# The field `x : a` is not a proof -- `a` is a `Sort u` -- so by the first
# clause alone `Acc` would be barred from eliminating into `Sort u`. But `x`
# is exactly the index of the result `Acc r x`, so it is allowed. Without
# this, `Acc`, `PredWithTypeField` and `SortElimProp` came back "cannot
# decide" and declined.
#
# The binder depth is carried, so a reference to the target from under n
# further binders is n higher. Running out of fuel answers "it occurs",
# which is the conservative direction: it grants the exception rather than
# denying large elimination on a term too deep to read.
def bvar_occurs(fuel: Nat, +ex: R.Tr<T.Ex>, +x: T.Ex, +k: U32) -> Bool:
  match fuel x:
    case 0n _:
      True{}
    case 1n+p T.EBVar{i}:
      U32.is_eq(i, k)
    case 1n+p T.EApp{f, a}:
      +pf = p
      bvar_occurs(pf, ex, R.get(T.Ex, 64n, ex, f, T.EBad{}), k)
      || bvar_occurs(pf, ex, R.get(T.Ex, 64n, ex, a, T.EBad{}), k)
    case 1n+p T.ELam{n, t, b, bi}:
      +pf = p
      bvar_occurs(pf, ex, R.get(T.Ex, 64n, ex, t, T.EBad{}), k)
      || bvar_occurs(pf, ex, R.get(T.Ex, 64n, ex, b, T.EBad{}),
                     (k + 1 : U32))
    case 1n+p T.EAll{n, t, b, bi}:
      +pf = p
      bvar_occurs(pf, ex, R.get(T.Ex, 64n, ex, t, T.EBad{}), k)
      || bvar_occurs(pf, ex, R.get(T.Ex, 64n, ex, b, T.EBad{}),
                     (k + 1 : U32))
    case 1n+p T.ELet{n, t, v, b}:
      +pf = p
      bvar_occurs(pf, ex, R.get(T.Ex, 64n, ex, t, T.EBad{}), k)
      || bvar_occurs(pf, ex, R.get(T.Ex, 64n, ex, v, T.EBad{}), k)
      || bvar_occurs(pf, ex, R.get(T.Ex, 64n, ex, b, T.EBad{}),
                     (k + 1 : U32))
    case 1n+p T.EProj{tn, i, sx}:
      +pf = p
      bvar_occurs(pf, ex, R.get(T.Ex, 64n, ex, sx, T.EBad{}), k)
    case 1n+p _:
      False{}

# The index must be EXACTLY the field variable, not merely contain it.
#
# `Eq.refl : forall {a} (x : a), Eq x x` has the field `x` as the index
# itself, and `Eq.rec` does eliminate into `Sort u`. The arena also carries
# the counterexample that forces this distinction: `SortElimProp2` has two
# indices and two fields, and its recursor is declared with NO extra
# universe parameter -- so Lean denies it large elimination. Accepting
# "occurs anywhere in an index" granted it, and `rec_count_v` then rejected
# an accept test. "Is the index" is the narrower reading and the one the
# export agrees with.
def is_bvar_k(+x: T.Ex, +k: U32) -> Bool:
  match x:
    case T.EBVar{i}:
      U32.is_eq(i, k)
    case _:
      False{}

def occurs_in_any(idxs: List<&2, U32>, +ex: R.Tr<T.Ex>, +k: U32) -> Bool:
  match idxs:
    case Nil{}:
      False{}
    case Con{head, tail}:
      is_bvar_k(R.get(T.Ex, 64n, ex, head, T.EBad{}), k)
      || occurs_in_any(tail, ex, k)

# Every field of the constructor must be a proposition.
#
# The local context is threaded, and must be: a field's type is written under
# the constructor's own telescope, so it is routinely a *bound variable*.
# `And.intro : forall {a b : Prop}, a -> b -> And a b` has fields of type `a`
# and `b`, which are binders. Asking for their universe with an empty context
# answers "unknown", which made `large_elim` undecided and declined the whole
# inductive block -- `And` and every Prop-valued structure like it, 21
# declining declarations across 7 files.
#
# `ctx` is innermost-first, the same convention `infer` and `ck_expr` use
# when they descend into a binder (`Con{dom, ctx}`), so each domain is consed
# on as the walk passes it.
def fields_prop(doms: List<&2, U32>, +ex: R.Tr<T.Ex>, +ln: R.Tr<L.LN>,
                +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +nskip: U32,
                +i: U32, +ctx: List<&2, U32>, +idxs: List<&2, U32>,
                +nf: U32, +acc: L.Tri) -> L.Tri:
  match doms:
    case Nil{}:
      acc
    case Con{head, tail}:
      +pi = i
      +ph = head
      # The field's own de Bruijn index as seen from the result type, which
      # sits under all `nf` fields: field 0 is `nf - 1`, the last is 0.
      +isidx = U32.is_ge(pi, nskip) && U32.is_gt(nf, 0)
               && occurs_in_any(idxs, ex,
                                (nf - 1 - (pi - nskip : U32) : U32))
      fields_prop(tail, ex, ln, nt, lp, nskip, (pi + 1 : U32),
                  Con{ph, ctx}, idxs, nf,
                  L.pick_tri(U32.is_lt(pi, nskip), acc,
                             L.pick_tri(isidx, acc,
                               I.tri_and(acc,
                                 field_is_proof(I.sl(64n, ex, ln, nt, lp,
                                   U.ex_at(ex, ph), ctx))))))

def subsingleton(+nc: U32, +fp: L.Tri) -> L.Tri:
  L.pick_tri(U32.is_eq(nc, 0), L.TYes{},
             L.pick_tri(U32.is_eq(nc, 1), fp, L.TNo{}))

# A universe that MIGHT be Prop gets the Prop restriction. `MyBool : Sort u`
# in bugs/large-elim-param has two constructors and a parameter universe; if
# u were 0 it would be a two-constructor Prop, so Lean expects no extra motive
# universe -- "#1 expected, #2 provided". Treating "might be Prop" as "is not
# a Prop" is how that export gets accepted.
def large_elim(+isprop: L.Tri, +nc: U32, +fp: L.Tri) -> L.Tri:
  match isprop:
    case L.TNo{}:
      L.TYes{}
    case L.TYes{}:
      subsingleton(nc, fp)
    case L.TUnk{}:
      subsingleton(nc, fp)

def rec_count_v(+le: L.Tri, +nind: U32, +nrec: U32, +nmot: U32) -> V:
  match le:
    case L.TUnk{}:
      VDecline{}
    case L.TYes{}:
      pick_v(U32.is_eq(nrec, (nind + 1 : U32)) && U32.is_eq(nmot, 1),
             VAccept{}, VReject{})
    case L.TNo{}:
      pick_v(U32.is_eq(nrec, nind) && U32.is_eq(nmot, 1),
             VAccept{}, VReject{})

def ind_only(items: List<&2, K.IItem>,
             acc: List<&2, K.IItem>) -> List<&2, K.IItem>:
  match items:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case K.IInd{nm, lps, ty, np, ni, nn, cs}:
          ind_only(tail, Con{K.IInd{nm, lps, ty, np, ni, nn, cs}, acc})
        case _:
          ind_only(tail, acc)

def len_items(xs: List<&2, K.IItem>, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      len_items(tail, (acc + 1 : U32))

def head_item(xs: List<&2, K.IItem>) -> K.IItem:
  match xs:
    case Nil{}:
      K.IOther{}
    case Con{head, tail}:
      head

def ctor_fields_prop(items: List<&2, K.IItem>, +ind: U32,
                     +ex: R.Tr<T.Ex>, +ln: R.Tr<L.LN>, +nt: R.Tr<U32>,
                     +lp: R.Tr<List<&2, U32>>, +acc: L.Tri) -> L.Tri:
  match items:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case K.ICtor{nm, lps, ty, ind2, np, nf, ci}:
          # `np`, `ty` and `nf` are each used more than once below, so they
          # are rebound as reusable first: pattern binders are affine.
          +pnp = np
          +pty = ty
          +pnf = nf
          ctor_fields_prop(tail, ind, ex, ln, nt, lp,
            L.pick_tri(U32.is_eq(ind2, ind),
              I.tri_and(acc,
                fields_prop(D.rev_u32(tele_doms(256n, ex,
                                                U.ex_at(ex, pty), Nil{}),
                                      Nil{}),
                            ex, ln, nt, lp, pnp, 0, Nil{},
                            # the index arguments of the constructor's
                            # result type: its spine, past the parameters
                            I.skip_u(I.spine_ar(256n, ex,
                                                tele_res(256n, ex,
                                                  U.ex_at(ex, pty)),
                                                Nil{}),
                                     pnp),
                            pnf, L.TYes{})),
              acc))
        case _:
          ctor_fields_prop(tail, ind, ex, ln, nt, lp, acc)

# A nested inductive's recursor has one motive per nested occurrence, not
# one. `Lean.Syntax` in init-prelude is nested and its recursor has three,
# and requiring exactly one rejected the whole prelude. Nested blocks decline.
def recs_all(items: List<&2, K.IItem>, +le: L.Tri, +nind: U32,
             +nested: U32, +acc: V) -> V:
  match items:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case K.IRec{nm, lps, ty, np, ni, nmo, kf}:
          recs_all(tail, le, nind, nested,
                   comb(acc,
                        pick_v(U32.is_gt(nested, 0), VDecline{},
                               rec_count_v(le, nind, list_len(lps, 0),
                                           nmo))))
        case _:
          recs_all(tail, le, nind, nested, acc)

# --- the K-like claim ----------------------------------------------------
# A recursor's `k` flag asserts that it reduces K-LIKE: applied to a major
# premise whose type's indices match the constructor's, it reduces to the
# single minor premise WITHOUT the major premise being a constructor
# application. `Eq.rec` is the real case.
#
# That is only sound when the inductive has exactly one constructor and that
# constructor has no fields -- then every element of the type is that
# constructor, so matching on it is no assumption. `Eq.refl` qualifies;
# `Nat.succ` does not, because a `Nat` can be something other than `zero`.
#
# The arena has two exports that lie about it, and they are exactly the
# dangerous shape: `bugs/rec-k-lie` claims `k` for a two-constructor
# `MyBool`, and `bugs/nat-rec-k-lie` claims it for `Nat`. A checker that
# honours such a claim can reduce a stuck recursor to the wrong branch and
# prove anything. Since the claim is checkable from the block itself, a false
# one is a REJECT rather than a decline.
def k_claim_v(items: List<&2, K.IItem>, +nc: U32, +nf0: U32,
              +acc: V) -> V:
  match items:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case K.IRec{nm, lps, ty, np, ni, nmo, kf}:
          k_claim_v(tail, nc, nf0,
                    comb(acc,
                         pick_v(U32.is_eq(kf, 0)
                                || (U32.is_eq(nc, 1) && U32.is_eq(nf0, 0)),
                                VAccept{}, VReject{})))
        case _:
          k_claim_v(tail, nc, nf0, acc)

# The single constructor's field count, or a sentinel when there is not
# exactly one.
def sole_ctor_nf(items: List<&2, K.IItem>, +ind: U32, +acc: U32) -> U32:
  match items:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case K.ICtor{nm, lps, ty, ind2, np, nf, ci}:
          sole_ctor_nf(tail, ind, S.pick(U32.is_eq(ind2, ind), nf, acc))
        case _:
          sole_ctor_nf(tail, ind, acc)

def block_rec_one(+items: List<&2, K.IItem>, +ex: R.Tr<T.Ex>,
                  +ln: R.Tr<L.LN>, +nt: R.Tr<U32>,
                  +lp: R.Tr<List<&2, U32>>, +ind: K.IItem) -> V:
  match ind:
    case K.IInd{nm, lps, ty, np, ni, nn, cs}:
      +res = tele_res(256n, ex, U.ex_at(ex, ty))
      +isprop = L.pick_tri(I.is_sortx(res),
                           L.ln_is_zero(R.get(L.LN, 64n, ln,
                                              I.sort_lvl_of(res), L.LNun{})),
                           L.TUnk{})
      +its = items
      +nested = nn
      +kv = k_claim_v(its, count_ctors(its, nm, 0),
                      sole_ctor_nf(its, nm, 4294967295), VAccept{})
      comb(kv,
           recs_all(its, large_elim(isprop, count_ctors(its, nm, 0),
                               ctor_fields_prop(its, nm, ex, ln, nt, lp,
                                                L.TYes{})),
               list_len(lps, 0), nested, VAccept{}))
    case _:
      VDecline{}

# Mutual blocks need each recursor matched to its own inductive, which needs
# the `all` field decoded; they decline for now.
def block_rec_v(+items: List<&2, K.IItem>, +ex: R.Tr<T.Ex>,
                +ln: R.Tr<L.LN>, +nt: R.Tr<U32>,
                +lp: R.Tr<List<&2, U32>>) -> V:
  +inds = ind_only(items, Nil{})
  pick_v(U32.is_eq(len_items(inds, 0), 1),
         block_rec_one(items, ex, ln, nt, lp, head_item(inds)),
         VDecline{})


# --- projections --------------------------------------------------------
# `e.i` with type name `T` is valid only when `T` is a structure -- one
# constructor and no indices -- and `i` is within that constructor's fields.
#   bugs/proj-non-structure projects from `Bad`, which has two constructors.
#   tutorial/088_projNotStruct projects from something that is not one.
#
# Encoded in one table: 0 means the name is not a known inductive, 1 means it
# is but is not a structure, and n+2 means a structure with n fields. An
# unknown name declines -- it might be an inductive this version does not
# decode, such as a nested or mutual one.
def ctor_nf_for(items: List<&2, K.IItem>, +ind: U32, +acc: U32) -> U32:
  match items:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case K.ICtor{nm, lps, ty, ind2, np, nf, ci}:
          ctor_nf_for(tail, ind, S.pick(U32.is_eq(ind2, ind), nf, acc))
        case _:
          ctor_nf_for(tail, ind, acc)

# Lean's infer_proj asks for one constructor and no indices only; a NESTED
# structure (Lean.Doc.Part, Lean.Language.SnapshotTree) is projected like
# any other. Requiring `nn == 0` here rejected every projection out of one
# (cedar: 19 wrong rejects, all `abbrev` projection functions)
def str_code(+nc: U32, +ni: U32, +nn: U32, +nf: U32) -> U32:
  S.pick(U32.is_eq(nc, 1) && U32.is_eq(ni, 0), (nf + 2 : U32), 1)

def str_of_items(items: List<&2, K.IItem>, +all: List<&2, K.IItem>,
                 +t: R.Tr<U32>) -> R.Tr<U32>:
  match items:
    case Nil{}:
      t
    case Con{head, tail}:
      match head:
        case K.IInd{nm, lps, ty, np, ni, nn, cs}:
          +pn = nm
          str_of_items(tail, all,
            R.set(U32, 64n, t, pn,
                  str_code(count_ctors(all, pn, 0), ni, nn,
                           ctor_nf_for(all, pn, 0)), 0))
        case _:
          str_of_items(tail, all, t)

def build_str(ds: List<&2, K.Dcl>, +t: R.Tr<U32>) -> R.Tr<U32>:
  match ds:
    case Nil{}:
      t
    case Con{head, tail}:
      match head:
        case K.DInd{nms, items}:
          +its = items
          build_str(tail, str_of_items(its, its, t))
        case _:
          build_str(tail, t)

def proj_code_v(+code: U32, +i: U32) -> V:
  pick_v(U32.is_eq(code, 0), VDecline{},
         pick_v(U32.is_eq(code, 1), VReject{},
                pick_v(U32.is_lt(i, (code - 2 : U32)), VAccept{},
                       VReject{})))

def not_projx(+x: T.Ex) -> Bool:
  match x:
    case T.EProj{tn, i, sx}:
      False{}
    case _:
      True{}

def proj_tn(+x: T.Ex) -> U32:
  match x:
    case T.EProj{tn, i, sx}:
      tn
    case _:
      0

def proj_idx(+x: T.Ex) -> U32:
  match x:
    case T.EProj{tn, i, sx}:
      i
    case _:
      0

def proj_at(+i: U32, +ex: R.Tr<T.Ex>, +strt: R.Tr<U32>) -> V:
  +x = U.ex_at(ex, i)
  pick_v(not_projx(x), VAccept{},
         proj_code_v(R.get(U32, 64n, strt, proj_tn(x), 0), proj_idx(x)))

def scan_projs(n: Nat, +i: U32, +ex: R.Tr<T.Ex>, +strt: R.Tr<U32>,
               +acc: V) -> V:
  match n:
    case 0n:
      acc
    case 1n+p:
      scan_projs(p, (i + 1 : U32), ex, strt,
                 comb(acc, proj_at(i, ex, strt)))


# --- deriving and checking the recursor ---------------------------------
# An inductive block is accepted only when every check passes INCLUDING the
# recursor's type being derived and matching the export's claim. That is what
# makes accepting safe: nothing about the recursor is taken on trust, which is
# the point, because `bugs/rec-k-lie` and friends are exports that lie about
# one and then prove `False`.
#
# Only the base case is derived -- no parameters, no indices, field-less
# constructors. Anything else declines.
def ctor_by_cidx(items: List<&2, K.IItem>, +ind: U32, +j: U32,
                 +acc: U32) -> U32:
  match items:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case K.ICtor{nm, lps, ty, ind2, np, nf, ci}:
          ctor_by_cidx(tail, ind, j,
                       S.pick(U32.is_eq(ind2, ind) && U32.is_eq(ci, j),
                              nm, acc))
        case _:
          ctor_by_cidx(tail, ind, j, acc)

def all_fieldless(items: List<&2, K.IItem>, +ind: U32) -> Bool:
  match items:
    case Nil{}:
      True{}
    case Con{head, tail}:
      match head:
        case K.ICtor{nm, lps, ty, ind2, np, nf, ci}:
          S.pick_b(U32.is_eq(ind2, ind), U32.is_eq(nf, 0), True{})
          && all_fieldless(tail, ind)
        case _:
          all_fieldless(tail, ind)

def rec_of(items: List<&2, K.IItem>, +acc: K.IItem) -> K.IItem:
  match items:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case K.IRec{nm, lps, ty, np, ni, nmo, kf}:
          rec_of(tail, K.IRec{nm, lps, ty, np, ni, nmo, kf})
        case _:
          rec_of(tail, acc)

def rec_ty_of(+it: K.IItem) -> U32:
  match it:
    case K.IRec{nm, lps, ty, np, ni, nmo, kf}:
      ty
    case _:
      4294967295

def rec_lps_of(+it: K.IItem) -> List<&2, U32>:
  match it:
    case K.IRec{nm, lps, ty, np, ni, nmo, kf}:
      lps
    case _:
      Nil{}

def head_u(xs: List<&2, U32>, +dflt: U32) -> U32:
  match xs:
    case Nil{}:
      dflt
    case Con{head, tail}:
      head

def build_cs(k: Nat, +j: U32, +items: List<&2, K.IItem>, +ind: U32,
             +us: List<&2, U32>, +st: I.IS,
             acc: List<&2, U32>) -> I.LS:
  match k:
    case 0n:
      I.LS{st, acc}
    case 1n+p:
      +ce = I.alloc_ex(st, T.EConst{ctor_by_cidx(items, ind, j, 0), us})
      build_cs(p, (j + 1 : U32), items, ind, us, I.ir_st(ce),
               Con{I.ir_ty(ce), acc})

def ctor_ty_by_cidx(items: List<&2, K.IItem>, +ind: U32, +j: U32,
                    +acc: U32) -> U32:
  match items:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case K.ICtor{nm, lps, ty, ind2, np, nf, ci}:
          ctor_ty_by_cidx(tail, ind, j,
                          S.pick(U32.is_eq(ind2, ind) && U32.is_eq(ci, j),
                                 ty, acc))
        case _:
          ctor_ty_by_cidx(tail, ind, j, acc)

def ctor_nf_by_cidx(items: List<&2, K.IItem>, +ind: U32, +j: U32,
                    +acc: U32) -> U32:
  match items:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case K.ICtor{nm, lps, ty, ind2, np, nf, ci}:
          ctor_nf_by_cidx(tail, ind, j,
                          S.pick(U32.is_eq(ind2, ind) && U32.is_eq(ci, j),
                                 nf, acc))
        case _:
          ctor_nf_by_cidx(tail, ind, j, acc)

# A recursive field needs an inductive hypothesis in its minor premise, whose
# own telescope shifts two ranges of de Bruijn indices by different amounts.
# Not implemented; such a block declines.
def skip_n(xs: List<&2, U32>, +n: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{head, tail}:
      +pt = tail
      S.pick_l(U32.is_eq(n, 0), Con{head, pt}, skip_n(pt, (n - 1 : U32)))

def ctor_has_rec(+ex: R.Tr<T.Ex>, +names: List<&2, U32>, +ty: U32,
                 +np: U32) -> Bool:
  Bool.not(L.tri_is_no(
    any_dom_occurs(skip_n(D.rev_u32(tele_doms(256n, ex,
                                              U.ex_at(ex, ty), Nil{}),
                                    Nil{}), np),
                   ex, names, L.TNo{})))

# A field is recursive when its type is exactly the inductive applied to
# arguments -- `Nat.succ : Nat -> Nat`, `List.cons : a -> List a -> List a`.
# A recursive field with its own telescope (a `W`-type, `Acc`) would need its
# inductive hypothesis to shift two ranges of indices by different amounts
# under its own binders, and declines.
# A recursive field is one whose telescope ENDS in the inductive. The
# telescope no longer has to be empty -- `ih_one` builds the hypothesis for
# it. What is still excluded is the inductive appearing in some other shape,
# nested inside another type: `field_is_deep` catches that and declines.
# The syntactic version, for the `Meta` table. That table is built before any
# checking state exists, so there is nothing to reduce with -- and it is only
# consulted by iota, where a missed field costs a decline rather than a wrong
# answer. The derivation uses the reducing version above.
def field_is_rec_syn(+ex: R.Tr<T.Ex>, +names: List<&2, U32>,
                     +fty: U32) -> Bool:
  +fr = tele_res(256n, ex, U.ex_at(ex, fty))
  is_constx(spine_head(256n, ex, fr))
  && mem(const_name_of(spine_head(256n, ex, fr)), names)

def any_field_rec(fs: List<&2, U32>, +ex: R.Tr<T.Ex>, +nm: U32) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{head, tail}:
      field_is_rec_syn(ex, [nm], head) || any_field_rec(tail, ex, nm)

def rec_positions_syn(fs: List<&2, U32>, +ex: R.Tr<T.Ex>,
                      +names: List<&2, U32>, +i: U32,
                      acc: List<&2, U32>) -> List<&2, U32>:
  match fs:
    case Nil{}:
      D.rev_u32(acc, Nil{})
    case Con{head, tail}:
      +pi = i
      rec_positions_syn(tail, ex, names, (pi + 1 : U32),
                        T.cons_if(field_is_rec_syn(ex, names, head), pi,
                                  acc))

# The index, not the node, of a telescope's result -- so it can be reduced.
def tele_res_ix(fuel: Nat, +ex: R.Tr<T.Ex>, +x: T.Ex, +i: U32) -> U32:
  match fuel x:
    case 0n _:
      i
    case 1n+p T.EAll{n, t, b, bi}:
      tele_res_ix(p, ex, U.ex_at(ex, b), b)
    case 1n+p _:
      i

# A recursive field is one whose telescope result REDUCES to the inductive.
# Reduction is the point: `055_reduceCtorParam` declares
#
#     reduceCtorParam.mk : constType (reduceCtorParam a) (reduceCtorParam a)
#                            -> reduceCtorParam a
#
# where `constType` is an ordinary definition that unfolds to its first
# argument. Syntactically the field's head is `constType`; only after delta
# is it the inductive. The export agrees -- it marks the type `isRec: true` --
# and without reducing, the derivation produced a minor premise with no
# inductive hypothesis and the block declined.
#
# The reduction's state is discarded: only the shape of the answer is wanted,
# and the nodes it allocated go with it.
def field_is_rec(+st: I.IS, +mt: R.Tr<I.Meta>, +lp: R.Tr<List<&2, U32>>,
                 +vt: R.Tr<U32>, +names: List<&2, U32>,
                 +fty: U32) -> Bool:
  +ex = I.is_ex(st)
  +w = I.whd(st, mt, lp, vt,
             tele_res_ix(256n, ex, U.ex_at(ex, fty), fty))
  +ex2 = I.is_ex(I.ir_st(w))
  +hd = spine_head(256n, ex2, U.ex_at(ex2, I.ir_ty(w)))
  is_constx(hd) && mem(const_name_of(hd), names)

def field_is_deep(+st: I.IS, +mt: R.Tr<I.Meta>,
                  +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
                  +names: List<&2, U32>, +fty: U32) -> Bool:
  Bool.not(L.tri_is_no(occurs_tri(I.is_ex(st), names,
                                  U.ex_at(I.is_ex(st), fty))))
  && Bool.not(field_is_rec(st, mt, lp, vt, names, fty))

def rec_positions(fs: List<&2, U32>, +st: I.IS, +mt: R.Tr<I.Meta>,
                  +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
                  +names: List<&2, U32>, +i: U32,
                  acc: List<&2, U32>) -> List<&2, U32>:
  match fs:
    case Nil{}:
      D.rev_u32(acc, Nil{})
    case Con{head, tail}:
      +pi = i
      rec_positions(tail, st, mt, lp, vt, names, (pi + 1 : U32),
                    T.cons_if(field_is_rec(st, mt, lp, vt, names, head),
                              pi, acc))

def any_deep(fs: List<&2, U32>, +st: I.IS, +mt: R.Tr<I.Meta>,
             +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
             +names: List<&2, U32>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{head, tail}:
      field_is_deep(st, mt, lp, vt, names, head)
      || any_deep(tail, st, mt, lp, vt, names)

# Recursive fields are fine now; what still declines is a field that
# mentions the inductive in some other shape -- nested inside another type,
# or behind its own telescope.
def no_deep_fields(items: List<&2, K.IItem>, +st: I.IS,
                   +mt: R.Tr<I.Meta>, +lp: R.Tr<List<&2, U32>>,
                   +vt: R.Tr<U32>, +names: List<&2, U32>,
                   +ind: U32) -> Bool:
  match items:
    case Nil{}:
      True{}
    case Con{head, tail}:
      match head:
        case K.ICtor{nm, lps, ty, ind2, np, nf, ci}:
          S.pick_b(U32.is_eq(ind2, ind),
                   Bool.not(any_deep(
                     skip_n(D.rev_u32(tele_doms(256n, I.is_ex(st),
                                                U.ex_at(I.is_ex(st), ty),
                                                Nil{}),
                                      Nil{}), np),
                     st, mt, lp, vt, names)),
                   True{})
          && no_deep_fields(tail, st, mt, lp, vt, names, ind)
        case _:
          no_deep_fields(tail, st, mt, lp, vt, names, ind)

# `ih_s : motive i-bar'' f_h`, at context
# [a.., motive, minors.., f_1..f_m, ih_1..ih_{s-1}].
# The inductive hypothesis for the h-th field, where that field may have a
# telescope of its own:
#
#     f_h : forall z_1 .. z_q, I a-bar e-bar
#     ih  : forall z_1'.. z_q', motive e-bar'' (f_h z_1 .. z_q)
#
# `q = 0` is the ordinary case (`Nat.succ`, `List.cons`) and falls out of the
# same formulas. `q > 0` is the one the earlier note called impossible here --
# "would need its inductive hypothesis to shift two ranges of indices by
# different amounts under its own binders" -- and that is exactly what the
# two cut positions below do: the field's own binders are RE-BOUND by the
# hypothesis, so every cut is offset by `q` to step over them, while the
# binders outside are shifted. `Acc.intro`'s recursive field
# `forall y, r y x -> Acc r y` is the case.
#
# Context at the point the hypothesis is built: `m` lifted fields and `s-1`
# earlier hypotheses are in scope, so the motive is at `s-1+m+j-1` and the
# field itself at `s-1+m-h`; under the `q` new binders both move up by `q`.
def ih_one(+st0: I.IS, +mt: R.Tr<I.Meta>, +lp2: R.Tr<List<&2, U32>>,
           +vt: R.Tr<U32>, +ex: R.Tr<T.Ex>, +fty: U32, +p: U32, +m: U32,
           +j: U32, +s: U32, +h: U32) -> I.IR:
  +fx = U.ex_at(ex, fty)
  +q = tele_n(256n, ex, fx, 0)
  +amt2 = (s - 1 + m - h + 1 : U32)
  # The field's result is REDUCED before its index arguments are read. For
  # `055_reduceCtorParam` the raw result is
  # `constType (reduceCtorParam a) (reduceCtorParam a)`, whose spine has two
  # arguments; reduced it is `reduceCtorParam a`, with one. Taking them
  # unreduced applied the motive to an argument that does not exist -- the
  # inductive has no indices at all -- and the derived recursor disagreed
  # with the declared one by exactly that argument.
  +wr = I.whd(st0, mt, lp2, vt, tele_res_ix(256n, ex, fx, fty))
  +st : I.IS = I.ir_st(wr)
  +rsp = spine_args(256n, I.is_ex(st),
                    U.ex_at(I.is_ex(st), I.ir_ty(wr)), Nil{})
  # the field's own binder types, each with its own cutoff
  +z1 = W.lift_each(D.rev_u32(tele_doms(256n, ex, fx, Nil{}), Nil{}), st,
                    (h - 1 : U32), j, 0, Nil{})
  +z2 = W.lift_each(D.rev_u32(I.ls_xs(z1), Nil{}), I.ls_st(z1), 0, amt2, 0,
                    Nil{})
  # the index arguments of the field's result, past the parameters
  +l1 = W.lift_all(skip_n(rsp, p),
                   I.ls_st(z2), (h - 1 + q : U32), j, Nil{})
  +l2 = W.lift_all(D.rev_u32(I.ls_xs(l1), Nil{}), I.ls_st(l1), q, amt2,
                   Nil{})
  +mv = I.alloc_ex(I.ls_st(l2), T.EBVar{(s - 1 + m + j - 1 + q : U32)})
  +fv = I.alloc_ex(I.ir_st(mv), T.EBVar{(s - 1 + m - h + q : U32)})
  +zv = W.bvar_nodes(W.desc(q, (q - 1 : U32)), I.ir_st(fv), Nil{})
  +fa = W.apply_spine(D.rev_u32(I.ls_xs(zv), Nil{}), I.ls_st(zv),
                      I.ir_ty(fv))
  +bd = W.apply_spine(List.append(&2, U32, D.rev_u32(I.ls_xs(l2), Nil{}),
                                  [I.ir_ty(fa)]),
                      I.ir_st(fa), I.ir_ty(mv))
  W.wrap_alls(D.rev_u32(I.ls_xs(z2), Nil{}), I.ir_st(bd), I.ir_ty(bd))

def ih_all(poss: List<&2, U32>, +st: I.IS, +mt: R.Tr<I.Meta>,
           +lp2: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +ex: R.Tr<T.Ex>,
           +fs: List<&2, U32>, +p: U32, +m: U32, +j: U32, +s: U32,
           acc: List<&2, U32>) -> I.LS:
  match poss:
    case Nil{}:
      I.LS{st, D.rev_u32(acc, Nil{})}
    case Con{head, tail}:
      +h = head
      +r = ih_one(st, mt, lp2, vt, ex,
                  I.nth_u(fs, (h - 1 : U32), 4294967295), p, m, j, s, h)
      ih_all(tail, I.ir_st(r), mt, lp2, vt, ex, fs, p, m, j,
             (s + 1 : U32), Con{I.ir_ty(r), acc})

# forall (f_1'..f_m') (ih_1..ih_r), motive e-bar'' (c_j a-bar f-bar)
def minor_full(+st: I.IS, +mt: R.Tr<I.Meta>,
               +lp2: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
               +ex: R.Tr<T.Ex>, +names: List<&2, U32>,
               +cnm: U32, +us: List<&2, U32>, +p: U32, +k: U32, +m: U32,
               +j: U32, +cdoms: List<&2, U32>,
               +cargs: List<&2, U32>) -> I.IR:
  +fs = W.take_last(cdoms, m, W.list_len_u(cdoms, 0))
  +poss = rec_positions(fs, st, mt, lp2, vt, names, 1, Nil{})
  +r = W.list_len_u(poss, 0)
  +fl = W.lift_each(fs, st, 0, j, 0, Nil{})
  +ihs = ih_all(poss, I.ls_st(fl), mt, lp2, vt, ex, fs, p, m, j, 1,
                Nil{})
  +e1 = W.lift_all(W.take_last(cargs, k, W.list_len_u(cargs, 0)),
                   I.ls_st(ihs), m, j, Nil{})
  +e2 = W.lift_all(D.rev_u32(I.ls_xs(e1), Nil{}), I.ls_st(e1), 0, r,
                   Nil{})
  +bn = W.bvar_nodes(List.append(&2, U32,
                                 W.desc(p, (r + m + j + p - 1 : U32)),
                                 W.desc(m, (r + m - 1 : U32))),
                     I.ls_st(e2), Nil{})
  +cc = I.alloc_ex(I.ls_st(bn), T.EConst{cnm, us})
  +capp = W.apply_spine(D.rev_u32(I.ls_xs(bn), Nil{}), I.ir_st(cc),
                        I.ir_ty(cc))
  +mv = I.alloc_ex(I.ir_st(capp), T.EBVar{(r + m + j - 1 : U32)})
  +body = W.apply_spine(List.append(&2, U32,
                                    D.rev_u32(I.ls_xs(e2), Nil{}),
                                    [I.ir_ty(capp)]),
                        I.ir_st(mv), I.ir_ty(mv))
  W.wrap_alls(List.append(&2, U32, D.rev_u32(I.ls_xs(fl), Nil{}),
                          I.ls_xs(ihs)),
              I.ir_st(body), I.ir_ty(body))

def build_minors(cnt: Nat, +j: U32, +items: List<&2, K.IItem>,
                 +ind: U32, +us: List<&2, U32>, +p: U32, +k: U32,
                 +ex: R.Tr<T.Ex>, +st: I.IS, +mtt: R.Tr<I.Meta>,
                 +lp2: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
                 acc: List<&2, U32>) -> I.LS:
  match cnt:
    case 0n:
      I.LS{st, D.rev_u32(acc, Nil{})}
    case 1n+q:
      +ci = (j - 1 : U32)
      +cty = ctor_ty_by_cidx(items, ind, ci, 4294967295)
      +ctx = U.ex_at(ex, cty)
      +mtv = minor_full(st, mtt, lp2, vt, ex, [ind],
                       ctor_by_cidx(items, ind, ci, 0), us,
                       p, k, ctor_nf_by_cidx(items, ind, ci, 0), j,
                       D.rev_u32(tele_doms(256n, ex, ctx, Nil{}), Nil{}),
                       spine_args(256n, ex, tele_res(256n, ex, ctx),
                                  Nil{}))
      build_minors(q, (j + 1 : U32), items, ind, us, p, k, ex,
                   I.ir_st(mtv), mtt, lp2, vt,
                   Con{I.ir_ty(mtv), acc})

def cmp_derived(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
                +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
                +mine: U32, +theirs: U32) -> V:
  +w1 = I.whd(st, mt, lp, vt, mine)
  +w2 = I.whd(I.ir_st(w1), mt, lp, vt, theirs)
  +s2 = I.ir_st(w2)
  # Fuel 512, not 64. These are whole recursor types and the `bugs/rec-*`
  # exports carry very large ones: `bugs/rec-missing-ih` is 296 KB, and the
  # difference that matters -- a missing inductive hypothesis, so a `forall`
  # on one side against an application on the other -- sits deep inside the
  # minor premise. Running out of fuel there turns a definite mismatch into
  # "cannot decide" and the lie goes uncaught.
  tri_v(I.dr_r(I.defeq(8192n, U32.is_eq(mine, theirs), s2, mt, nt, lp, vt,
                       Nil{},
                       U.ex_at(I.is_ex(s2), I.ir_ty(w1)),
                       U.ex_at(I.is_ex(s2), I.ir_ty(w2)))))

# The universe arguments must be in the inductive's own levelParams order;
# `param_lvls` conses, so its result is reversed.
def derive_go(+ok: Bool, +items: List<&2, K.IItem>, +st: I.IS,
              +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
              +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +ex: R.Tr<T.Ex>,
              +nm: U32, +lps: List<&2, U32>, +ity: U32, +np: U32,
              +ni: U32, +nc: U32, +vnm: U32, +theirs: U32) -> V:
  match ok:
    case False{}:
      VDecline{}
    case True{}:
      +ul = W.param_lvls(lps, st, Nil{})
      +us = D.rev_u32(I.ls_xs(ul), Nil{})
      +mn = build_minors(U32.to_nat(nc), 1, items, nm, us, np, ni, ex,
                         I.ls_st(ul), mt, lp, vt, Nil{})
      +d = W.derive_gen(I.ls_st(mn), nm, us, np, ni, nc,
                        D.rev_u32(tele_doms(256n, ex, U.ex_at(ex, ity),
                                            Nil{}), Nil{}),
                        I.ls_xs(mn), vnm)
      cmp_derived(I.ir_st(d), mt, nt, lp, vt, I.ir_ty(d), theirs)

# Parameters, indices and non-recursive constructor fields are all handled.
# A recursive field, a nested block, or an inductive whose large-elimination
# status cannot be settled declines.
def derive_block_v(+items: List<&2, K.IItem>, +st: I.IS,
                   +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
                   +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
                   +ind: K.IItem, +nc: U32, +le: L.Tri) -> V:
  match ind:
    case K.IInd{nm, lps, ty, np, ni, nn, cs}:
      +its = items
      +pnm = nm
      +ex = I.is_ex(st)
      +rc = rec_of(its, K.IOther{})
      # The derivation now runs for BOTH elimination strengths. Only an
      # undecided one declines: with large elimination the motive's universe
      # is the recursor's extra level parameter, without it the motive goes
      # to `Prop`, and the sentinel name picks between them.
      derive_go(U32.is_eq(nn, 0) && Bool.not(L.tri_is_unk(le))
                && no_deep_fields(its, st, mt, lp, vt, [pnm], pnm)
                && U32.is_ne(rec_ty_of(rc), 4294967295),
                its, st, mt, nt, lp, vt, ex, pnm, lps, ty, np, ni, nc,
                S.pick(L.tri_is_yes(le), head_u(rec_lps_of(rc), 0),
                       4294967295),
                rec_ty_of(rc))
    case _:
      VDecline{}

# Mirrors block_rec_v: one inductive per block, otherwise decline.
def block_derive_one(+items: List<&2, K.IItem>, +st: I.IS,
                     +mt: R.Tr<I.Meta>, +vt: R.Tr<U32>, +ln: R.Tr<L.LN>, +nt: R.Tr<U32>,
                     +lp: R.Tr<List<&2, U32>>, +ind: K.IItem) -> V:
  match ind:
    case K.IInd{nm, lps, ty, np, ni, nn, cs}:
      +its = items
      +pnm = nm
      +res = tele_res(256n, I.is_ex(st), U.ex_at(I.is_ex(st), ty))
      +isprop = L.pick_tri(I.is_sortx(res),
                           L.ln_is_zero(R.get(L.LN, 64n, ln,
                                              I.sort_lvl_of(res),
                                              L.LNun{})),
                           L.TUnk{})
      +nc = count_ctors(its, pnm, 0)
      derive_block_v(its, st, mt, nt, lp, vt,
                     K.IInd{pnm, lps, ty, np, ni, nn, cs}, nc,
                     large_elim(isprop, nc,
                                ctor_fields_prop(its, pnm, I.is_ex(st),
                                                 ln, nt, lp, L.TYes{})))
    case _:
      VDecline{}

def block_derive_v(+items: List<&2, K.IItem>, +st: I.IS,
                   +mt: R.Tr<I.Meta>, +vt: R.Tr<U32>,
                   +ln: R.Tr<L.LN>, +nt: R.Tr<U32>,
                   +lp: R.Tr<List<&2, U32>>) -> V:
  +inds = ind_only(items, Nil{})
  pick_v(U32.is_eq(len_items(inds, 0), 1),
         block_derive_one(items, st, mt, vt, ln, nt, lp, head_item(inds)),
         VDecline{})

# --- the block must declare what the kernel would derive ----------------
# `other/orphan-ctor` declares a constructor the inductive's own `ctors` list
# does not mention; the kernel never adds it, so the later reference is an
# unknown constant. And `tutorial/137_dup_rec_def2` names its recursor
# `X.not_rec` to dodge a collision with an earlier `def X.rec` -- but the
# kernel derives the name `X.rec` and the collision is real.
#
# Both are cases of the export describing an environment the kernel would not
# build, which is exactly the class of lie the recursor derivation exists to
# catch.
def ctor_names_for(items: List<&2, K.IItem>, +ind: U32,
                   acc: List<&2, U32>) -> List<&2, U32>:
  match items:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case K.ICtor{nm, lps, ty, ind2, np, nf, ci}:
          ctor_names_for(tail, ind,
                         T.cons_if(U32.is_eq(ind2, ind), nm, acc))
        case _:
          ctor_names_for(tail, ind, acc)

def subset_u(xs: List<&2, U32>, +ys: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{head, tail}:
      mem(head, ys) && subset_u(tail, ys)

def ctors_match_v(+declared: List<&2, U32>, +listed: List<&2, U32>) -> V:
  pick_v(subset_u(declared, listed) && subset_u(listed, declared),
         VAccept{}, VReject{})

def nm_is_str(+n: T.Nm) -> Bool:
  match n:
    case T.NStr{pre, s}:
      True{}
    case _:
      False{}

def nm_pre(+n: T.Nm) -> U32:
  match n:
    case T.NStr{pre, s}:
      pre
    case T.NNum{pre, i}:
      pre
    case _:
      0

def nm_bytes(+n: T.Nm) -> List<&2, U32>:
  match n:
    case T.NStr{pre, s}:
      s
    case _:
      Nil{}

def bytes_eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{a, as} Con{b, bs}:
      U32.is_eq(a, b) && bytes_eq(as, bs)
    case _ _:
      False{}

# "rec" is 114 101 99.
def is_rec_name(+nmt: R.Tr<T.Nm>, +recnm: U32, +indnm: U32) -> Bool:
  +n = R.get(T.Nm, 64n, nmt, recnm, T.NAnon{})
  nm_is_str(n) && U32.is_eq(nm_pre(n), indnm)
  && bytes_eq(nm_bytes(n), [114, 101, 99])

def recs_name_v(items: List<&2, K.IItem>, +nmt: R.Tr<T.Nm>, +indnm: U32,
                +acc: V) -> V:
  match items:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case K.IRec{nm, lps, ty, np, ni, nmo, kf}:
          recs_name_v(tail, nmt, indnm,
                      comb(acc, pick_v(is_rec_name(nmt, nm, indnm),
                                       VAccept{}, VReject{})))
        case _:
          recs_name_v(tail, nmt, indnm, acc)

def block_names_one(+items: List<&2, K.IItem>, +nmt: R.Tr<T.Nm>,
                    +ind: K.IItem) -> V:
  match ind:
    case K.IInd{nm, lps, ty, np, ni, nn, cs}:
      +its = items
      +pnm = nm
      # A nested block legitimately has `rec_1`, `rec_2`, ... alongside
      # `rec` -- one per nested occurrence -- so the derived-name check does
      # not apply to it. Applying it anyway rejected every real prelude,
      # because `Lean.Syntax` is nested.
      comb(ctors_match_v(ctor_names_for(its, pnm, Nil{}), cs),
           pick_v(U32.is_gt(nn, 0), VDecline{},
                  recs_name_v(its, nmt, pnm, VAccept{})))
    case _:
      VDecline{}

def block_names_v(+items: List<&2, K.IItem>, +nmt: R.Tr<T.Nm>) -> V:
  +inds = ind_only(items, Nil{})
  pick_v(U32.is_eq(len_items(inds, 0), 1),
         block_names_one(items, nmt, head_item(inds)),
         VDecline{})

# --- rule-reduced recursors (nested blocks) ------------------------------
# The inductive a constructor belongs to: this block's own, or (an external
# inductive's constructor, for a nested auxiliary) from the metadata so far.
def ctor_ind_items(items: List<&2, K.IItem>, +ct: U32) -> U32:
  match items:
    case Nil{}:
      4294967295
    case Con{head, tail}:
      match head:
        case K.ICtor{nm, lps, ty, ind2, np, nf, ci}:
          S.pick(U32.is_eq(nm, ct), ind2, ctor_ind_items(tail, ct))
        case _:
          ctor_ind_items(tail, ct)

# --- a trusted nested block: each exported rule bound to its own recursor ---
# Picking a recursor's rules by the constructor's inductive alone is wrong
# when the block nests one external type twice (Cedar.Spec.Value nests List
# for List Value and for List (String x Value)): both auxiliary recursors
# have List.nil/List.cons rules, and the first match won -- a wrong reduct
# and WRONG REJECTS of Value.brecOn.go and 33 more cedar declarations in a
# worker that trusts the block. Lean keeps each recursor's own rules. Here:
# the rule's rhs applies minor k (its body's head variable); minor k's
# conclusion is `motive_s ..`; the recursor's own conclusion is
# `motive_j ..`; the rule is the recursor's iff s = j.
def pi_count(+fuel: Nat, +ex: R.Tr<T.Ex>, +x: T.Ex, +acc: U32) -> U32:
  match fuel x:
    case 0n _:
      acc
    case 1n+p T.EAll{n, t, b, bi}:
      pi_count(p, ex, U.ex_at(ex, b), (acc + 1 : U32))
    case 1n+p _:
      acc

def pi_concl(+fuel: Nat, +ex: R.Tr<T.Ex>, +x: T.Ex) -> T.Ex:
  match fuel x:
    case 0n _:
      T.EBad{}
    case 1n+p T.EAll{n, t, b, bi}:
      pi_concl(p, ex, U.ex_at(ex, b))
    case 1n+p y:
      y

def lam_concl(+fuel: Nat, +ex: R.Tr<T.Ex>, +x: T.Ex) -> T.Ex:
  match fuel x:
    case 0n _:
      T.EBad{}
    case 1n+p T.ELam{n, t, b, bi}:
      lam_concl(p, ex, U.ex_at(ex, b))
    case 1n+p y:
      y

def bv_ix(+x: T.Ex) -> U32:
  match x:
    case T.EBVar{i}:
      i
    case _:
      4294967295

def hd_bvar(+ex: R.Tr<T.Ex>, +x: T.Ex) -> U32:
  bv_ix(I.spine_hd(4096n, ex, x))

# the motive index minor k targets (doms: the recursor's binder domains,
# outermost first; the minor's own telescope has f binders)
def minor_spec(+ex: R.Tr<T.Ex>, +doms: List<&2, U32>, +rp: U32, +nmo: U32,
               +k: U32) -> U32:
  +d : U32 = I.nth_u(doms, (rp + nmo + k : U32), 4294967295)
  +e2 = ex
  +dx : T.Ex = U.ex_at(e2, d)
  +f : U32 = pi_count(4096n, e2, dx, 0)
  +b : U32 = hd_bvar(e2, pi_concl(4096n, e2, dx))
  S.pick(U32.is_eq(b, 4294967295) || U32.is_eq(d, 4294967295), 4294967295,
         ((nmo + k : U32) + f - 1 - b : U32))

def rules_own(items: List<&2, K.IItem>, +ex: R.Tr<T.Ex>,
              +doms: List<&2, U32>, +rp: U32, +nmo: U32, +nmin: U32,
              +j: U32, +acc: List<&2, U32>) -> List<&2, U32>:
  match items:
    case Nil{}:
      acc
    case Con{h, tail}:
      match h:
        case K.IRule{ct, nf, rhs}:
          +e2 = ex
          +nf2 : U32 = nf
          +rh : U32 = rhs
          +ct2 : U32 = ct
          +i : U32 = hd_bvar(e2, lam_concl(4096n, e2, U.ex_at(e2, rh)))
          +k : U32 = ((nf2 + nmin : U32) - 1 - i : U32)
          +mine : Bool = U32.is_ne(i, 4294967295)
                         && U32.is_eq(minor_spec(e2, doms, rp, nmo, k), j)
          rules_own(tail, e2, doms, rp, nmo, nmin, j,
                    S.pick_l(mine, Con{ct2, Con{nf2, Con{rh, acc}}}, acc))
        case _:
          rules_own(tail, ex, doms, rp, nmo, nmin, j, acc)

# a recursor's own rules: j from its conclusion `motive_j ..`
def rules_of_rec(items: List<&2, K.IItem>, +ex: R.Tr<T.Ex>, +ty: U32,
                 +rp: U32, +nmo: U32, +nmin: U32) -> List<&2, U32>:
  +e2 = ex
  +tx : T.Ex = U.ex_at(e2, ty)
  +tot : U32 = pi_count(4096n, e2, tx, 0)
  +b : U32 = hd_bvar(e2, pi_concl(4096n, e2, tx))
  +j : U32 = ((tot - 1 : U32) - rp - b : U32)
  rules_own(items, e2, I.rev_u(tele_doms(4096n, e2, tx, Nil{}), Nil{}), rp, nmo,
            nmin, j, Nil{})

def rule_ind(+ct: U32, +items: List<&2, K.IItem>, +t: R.Tr<I.Meta>) -> U32:
  +c2 : U32 = ct
  +own : U32 = ctor_ind_items(items, c2)
  S.pick(U32.is_eq(own, 4294967295),
         I.meta_ind(R.get(I.Meta, 64n, t, c2, I.MNone{})), own)

# the recursor's rules: those whose constructor builds the major premise's
# inductive (the head of its last binder's type), flat [ctor, nf, rhs, ...]
def rules_for(items: List<&2, K.IItem>, +all: List<&2, K.IItem>,
              +head: U32, +t: R.Tr<I.Meta>,
              +acc: List<&2, U32>) -> List<&2, U32>:
  match items:
    case Nil{}:
      acc
    case Con{h, tail}:
      match h:
        case K.IRule{ct, nf, rhs}:
          +c2 : U32 = ct
          rules_for(tail, all, head, t,
                    S.pick_l(U32.is_eq(rule_ind(c2, all, t), head),
                             Con{c2, Con{nf, Con{rhs, acc}}}, acc))
        case _:
          rules_for(tail, all, head, t, acc)

def rr_major_head(+ex: R.Tr<T.Ex>, +ty: U32) -> U32:
  +e2 = ex
  I.const_nm2(I.spine_hd(256n, e2,
    U.ex_at(e2, head_u(tele_doms(256n, e2, U.ex_at(e2, ty), Nil{}),
                       4294967295))))

# --- metadata for iota --------------------------------------------------
# What `whnf` needs to recognise a recursor application and its major
# premise. The arities come from the inductive itself and the minor count
# from its actual constructors, not from the export's `numMinors`.
def meta_items(items: List<&2, K.IItem>, +allit: List<&2, K.IItem>,
               +ex: R.Tr<T.Ex>, +ind: U32,
               +np: U32, +ni: U32, +nc: U32,
               +t: R.Tr<I.Meta>) -> R.Tr<I.Meta>:
  match items:
    case Nil{}:
      t
    case Con{head, tail}:
      match head:
        # A NESTED block's recursors (numMotives > 1: Lean.Syntax.rec and
        # its auxiliaries rec_1/rec_2 over Array/List) take several motives
        # and more minors, so "params + 1 + #ctors + indices" points at a
        # minor, not the major premise; and the built-in iota below assumes
        # a non-nested block (minor at params+1+cidx, IHs from this block
        # only). For those the major position is read off the recursor's own
        # type (binders - 1, encoded so params+1+n+indices lands on it) and
        # the inductive is a SENTINEL, so that iota never fires: a
        # constructor major then flags the declaration INCOMPLETE (km WI3)
        # instead of producing a wrong reduct or a "stuck" term to deny.
        case K.IRec{nm, lps, ty, rp, rni, nmo, kf}:
          +pty = ty
          +prp = rp
          +prni = rni
          +pkf = kf
          +nmo2 : U32 = nmo
          +nested : Bool = Bool.not(U32.is_eq(nmo2, 1))
          +tot : U32 = I.len_u(tele_doms(256n, ex, U.ex_at(ex, pty), Nil{}),
                               0)
          +t2 : R.Tr<I.Meta> = t
          +al2 : List<&2, K.IItem> = allit
          # a nested recursor of an OWNED block reduces by the exported
          # rules too (rules_for, as a trusted block's does): with an empty
          # rule list it never fired, every structural recursion over the
          # nested occurrence (Cedar's TermType.rec_1 on List.cons) stayed
          # stuck, and the projections in its unfolded body (`f.1.0` for
          # `f : below (a :: l)`) had no type -- an argument-type check met
          # the sentinel and the declaration declined (TermType.lt_trans._f)
          meta_items(tail, al2, ex, ind, np, ni, nc,
                     R.set(I.Meta, 64n, t2, nm,
                           I.pick_meta(nested,
                             I.MRecR{prp, nmo2,
                                     (tot - 1 - prp - nmo2 - prni : U32),
                                     prni,
                                     rules_of_rec(al2, ex, pty, prp, nmo2,
                                                  (tot - 1 - prp - nmo2 - prni : U32))},
                             I.MRec{np, ni, nc, ind, pkf,
                                    ctor_ty_by_cidx(al2, ind, 0,
                                                    4294967295)}),
                           I.MNone{}))
        case K.ICtor{nm, lps, ty, ind2, cnp, nf, ci}:
          +pcnp = cnp
          +pty2 = ty
          meta_items(tail, allit, ex, ind, np, ni, nc,
                     R.set(I.Meta, 64n, t, nm,
                           I.MCtor{ci, pcnp, nf, ind2,
                                   rec_positions_syn(
                                     skip_n(D.rev_u32(
                                       tele_doms(256n, ex,
                                                 U.ex_at(ex, pty2),
                                                 Nil{}),
                                       Nil{}), pcnp),
                                     ex, [ind], 1, Nil{}), pty2},
                           I.MNone{}))
        case _:
          meta_items(tail, allit, ex, ind, np, ni, nc, t)

def ctx_upto(doms: List<&2, U32>, +i: U32,
             acc: List<&2, U32>) -> List<&2, U32>:
  match doms:
    case Nil{}:
      acc
    case Con{head, tail}:
      +ph = head
      +pa = acc
      S.pick_l(U32.is_eq(i, 0), pa,
               ctx_upto(tail, (i - 1 : U32), Con{ph, pa}))

# --- the bound on projections out of a proposition -----------------------
# The first DEPENDENT data field: the lowest index `j` whose field is data
# (its type is not a proposition) and which some later field's type mentions.
# A projection out of a Prop structure is allowed only strictly below this.
#
# A data field nothing depends on does not count -- the arena says so
# directly: "Non-dependent data fields are not relevant."
#
# `nf` when there is no such field, which permits every proof field.
# a field counts as data: not definitely a proof, or (strict) definitely not
def kdata(+strict: Bool, +z: L.Tri) -> Bool:
  match strict:
    case True{}:
      L.tri_is_no(z)
    case False{}:
      Bool.not(L.tri_is_yes(z))

def dep_data_inner(n: Nat, +doms: List<&2, U32>, +ex: R.Tr<T.Ex>,
                   +ln: R.Tr<L.LN>, +nt: R.Tr<U32>,
                   +lp: R.Tr<List<&2, U32>>, +nskip: U32, +k: U32,
                   +j: U32, +acc: U32, +strict: Bool) -> U32:
  match n:
    case 0n:
      acc
    case 1n+q:
      # does field k's type mention field j? seen from field k, field j is
      # at de Bruijn index k-1-j
      +hit = U32.is_lt(j, k)
             && bvar_occurs(256n, ex,
                            U.ex_at(ex, I.nth_u(doms, (nskip + k : U32),
                                              4294967295)),
                            (k - 1 - j : U32))
             && kdata(strict,
                  L.ln_is_zero(I.sl(256n, ex, ln, nt, lp,
                    U.ex_at(ex, I.nth_u(doms, (nskip + j : U32),
                                      4294967295)),
                    ctx_upto(doms, (nskip + j : U32), Nil{}))))
      dep_data_inner(q, doms, ex, ln, nt, lp, nskip, k, (j + 1 : U32),
                     S.pick(hit && U32.is_lt(j, acc), j, acc), strict)

def dep_data_outer(n: Nat, +doms: List<&2, U32>, +ex: R.Tr<T.Ex>,
                   +ln: R.Tr<L.LN>, +nt: R.Tr<U32>,
                   +lp: R.Tr<List<&2, U32>>, +nskip: U32, +nf: U32,
                   +k: U32, +acc: U32, +strict: Bool) -> U32:
  match n:
    case 0n:
      acc
    case 1n+q:
      dep_data_outer(q, doms, ex, ln, nt, lp, nskip, nf, (k + 1 : U32),
                     dep_data_inner(U32.to_nat(nf), doms, ex, ln, nt, lp,
                                    nskip, k, 0, acc, strict), strict)

# The context for the field at position `i`: the domains before it,
# innermost first.
# 4294967295 when the structure is not DEFINITELY a proposition. The bound is
# only meaningful for one that is, and the distinction matters: a definite
# violation of the rule is a REJECT, while "this might be a Prop and I cannot
# tell" must only decline.
def prop_proj_bound(+isprop: L.Tri, +ex: R.Tr<T.Ex>, +ln: R.Tr<L.LN>,
                    +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +cty: U32,
                    +np: U32, +nf: U32, +strict: Bool) -> U32:
  match isprop:
    case L.TYes{}:
      dep_data_outer(U32.to_nat(nf),
                     D.rev_u32(tele_doms(256n, ex, U.ex_at(ex, cty),
                                         Nil{}), Nil{}),
                     ex, ln, nt, lp, np, nf, 0, nf, strict)
    case _:
      4294967295

def meta_block_one(+items: List<&2, K.IItem>, +ex: R.Tr<T.Ex>,
                   +ln: R.Tr<L.LN>, +t: R.Tr<I.Meta>,
                   +ind: K.IItem, +nt: R.Tr<U32>,
                   +lp: R.Tr<List<&2, U32>>) -> R.Tr<I.Meta>:
  match ind:
    case K.IInd{nm, lps, ty, np, ni, nn, cs}:
      +its = items
      +pnm = nm
      # A structure -- one constructor, no indices, not nested -- also gets
      # an entry under its own name, so projection typing can find the
      # constructor's field types.
      +nc = count_ctors(its, pnm, 0)
      # structure eta for iota (km's WI3c): structure-like, not recursive,
      # definitely not a Prop -- recorded under the name + 2^30
      +cty0 : U32 = ctor_ty_by_cidx(its, pnm, 0, 4294967295)
      +se : Bool = U32.is_eq(nc, 1) && U32.is_eq(ni, 0) && U32.is_eq(nn, 0)
                   && L.tri_is_no(L.ln_is_zero(R.get(L.LN, 64n, ln,
                        I.sort_lvl_of(tele_res(256n, ex, U.ex_at(ex, ty))),
                        L.LNun{})))
                   && Bool.not(any_field_rec(
                        skip_n(D.rev_u32(tele_doms(256n, ex,
                                                   U.ex_at(ex, cty0), Nil{}),
                                         Nil{}), np), ex, pnm))
      meta_items(its, its, ex, pnm, np, ni, nc,
                 R.set_if(I.Meta, se,
                 # Lean's infer_proj asks only for one constructor and no
                 # indices: a NESTED structure (Lean.Doc.Part, SnapshotTree)
                 # projects like any other, from its exported constructor
                 # type; without this entry its projections were REJECTED
                 # (cedar: 19 wrong rejects, the unknown-structure bounds
                 # read as a definite Prop violation)
                 R.sub(I.Meta,
                       U32.is_eq(nc, 1) && U32.is_eq(ni, 0),
                       R.set(I.Meta, 64n, t, pnm,
                             I.MInd{np, ctor_nf_by_cidx(its, pnm, 0, 0),
                                    ctor_ty_by_cidx(its, pnm, 0,
                                                    4294967295),
                                    S.pick(L.tri_is_yes(
                                      large_elim(
                                        L.ln_is_zero(R.get(L.LN, 64n, ln,
                                          I.sort_lvl_of(tele_res(256n, ex,
                                            U.ex_at(ex, ty))),
                                          L.LNun{})),
                                        nc,
                                        ctor_fields_prop(its, pnm, ex, ln,
                                          R.TNil{}, R.TNil{}, L.TYes{}))),
                                      0, 1),
                                    prop_proj_bound(
                                      L.ln_is_zero(R.get(L.LN, 64n, ln,
                                        I.sort_lvl_of(tele_res(256n, ex,
                                          U.ex_at(ex, ty))), L.LNun{})),
                                      ex, ln, nt, lp,
                                      ctor_ty_by_cidx(its, pnm, 0,
                                                      4294967295),
                                      np,
                                      ctor_nf_by_cidx(its, pnm, 0, 0), False{}),
                                    prop_proj_bound(
                                      L.ln_is_zero(R.get(L.LN, 64n, ln,
                                        I.sort_lvl_of(tele_res(256n, ex,
                                          U.ex_at(ex, ty))), L.LNun{})),
                                      ex, ln, nt, lp,
                                      ctor_ty_by_cidx(its, pnm, 0,
                                                      4294967295),
                                      np,
                                      ctor_nf_by_cidx(its, pnm, 0, 0), True{})},
                             I.MNone{}),
                       t),
                 (pnm + 1073741824 : U32), I.MVer{1}, I.MNone{}))
    case _:
      t

# nt / lp: the constants' types and level params so far, so the bound on
# projections out of a Prop structure can size field types that mention
# constants (an empty table counted `a = b` as data)
# A structure-like inductive of a MUTUAL block (one constructor, no
# indices) gets the same projection-typing entry as a lone one, computed
# from its own sort and constructor type; Lean's infer_proj does not care
# which block the inductive came from. bugs/proj-of-imax-prop puts a Prop
# structure `ImaxProp : Sort (imax 1 0)` in a mutual block and projects
# `Bool` out of a proof: the entry's bounds (ppx = ppd = 0) are what make
# that a definite ill-typing. No structure-eta marker here (eta needs the
# block non-recursive, which the single path checks against one name).
def meta_struct_one(+items: List<&2, K.IItem>, +ex: R.Tr<T.Ex>,
                    +ln: R.Tr<L.LN>, +t: R.Tr<I.Meta>, +ind: K.IItem,
                    +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>) -> R.Tr<I.Meta>:
  match ind:
    case K.IInd{nm, lps, ty, np, ni, nn, cs}:
      +its = items
      +pnm = nm
      +nc = count_ctors(its, pnm, 0)
      +isp : L.Tri = L.ln_is_zero(R.get(L.LN, 64n, ln,
                       I.sort_lvl_of(tele_res(256n, ex, U.ex_at(ex, ty))),
                       L.LNun{}))
      R.sub(I.Meta, U32.is_eq(nc, 1) && U32.is_eq(ni, 0),
            R.set(I.Meta, 64n, t, pnm,
                  I.MInd{np, ctor_nf_by_cidx(its, pnm, 0, 0),
                         ctor_ty_by_cidx(its, pnm, 0, 4294967295),
                         S.pick(L.tri_is_yes(
                           large_elim(isp, nc,
                             ctor_fields_prop(its, pnm, ex, ln,
                                              R.TNil{}, R.TNil{}, L.TYes{}))),
                           0, 1),
                         prop_proj_bound(isp, ex, ln, nt, lp,
                                         ctor_ty_by_cidx(its, pnm, 0, 4294967295),
                                         np, ctor_nf_by_cidx(its, pnm, 0, 0),
                                         False{}),
                         prop_proj_bound(isp, ex, ln, nt, lp,
                                         ctor_ty_by_cidx(its, pnm, 0, 4294967295),
                                         np, ctor_nf_by_cidx(its, pnm, 0, 0),
                                         True{})},
                  I.MNone{}),
            t)
    case _:
      t

def meta_structs(inds: List<&2, K.IItem>, +items: List<&2, K.IItem>,
                 +ex: R.Tr<T.Ex>, +ln: R.Tr<L.LN>, +t: R.Tr<I.Meta>,
                 +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>) -> R.Tr<I.Meta>:
  match inds:
    case Nil{}:
      t
    case Con{h, tl}:
      meta_structs(tl, items, ex, ln,
                   meta_struct_one(items, ex, ln, t, h, nt, lp), nt, lp)

def meta_block(+items: List<&2, K.IItem>, +ex: R.Tr<T.Ex>,
               +ln: R.Tr<L.LN>, +t: R.Tr<I.Meta>, +nt: R.Tr<U32>,
               +lp: R.Tr<List<&2, U32>>) -> R.Tr<I.Meta>:
  +inds = ind_only(items, Nil{})
  +its = items
  R.sub(I.Meta, U32.is_eq(len_items(inds, 0), 1),
        meta_block_one(its, ex, ln, t, head_item(inds), nt, lp),
        meta_structs(inds, its, ex, ln, t, nt, lp))

# --- mutual and nested blocks -------------------------------------------
def add_itab(items: List<&2, K.IItem>, +t: R.Tr<K.IItem>) -> R.Tr<K.IItem>:
  match items:
    case Nil{}:
      t
    case Con{K.IInd{nm, lps, ty, np, ni, nn, cs}, tl}:
      +n2 : U32 = nm
      add_itab(tl, R.set(K.IItem, 64n, t, n2,
                         K.IInd{n2, lps, ty, np, ni, nn, cs}, K.IOther{}))
    case Con{h, tl}:
      add_itab(tl, t)

def add_ctab(items: List<&2, K.IItem>, +t: R.Tr<U32>) -> R.Tr<U32>:
  match items:
    case Nil{}:
      t
    case Con{K.ICtor{nm, lps, ty, ind, np, nf, ci}, tl}:
      add_ctab(tl, R.set(U32, 64n, t, nm, ty, 4294967295))
    case Con{h, tl}:
      add_ctab(tl, t)

def nn_any(items: List<&2, K.IItem>) -> Bool:
  match items:
    case Nil{}:
      False{}
    case Con{K.IInd{nm, lps, ty, np, ni, nn, cs}, tl}:
      U32.is_ne(nn, 0) || nn_any(tl)
    case Con{h, tl}:
      nn_any(tl)

# mutual (several types) or nested: recursors derived by nested.bend
def is_nm_block(+items: List<&2, K.IItem>) -> Bool:
  +its = items
  U32.is_gt(len_items(ind_only(its, Nil{}), 0), 1) || nn_any(its)

def first_ind_nm(items: List<&2, K.IItem>) -> U32:
  match items:
    case Nil{}:
      4294967295
    case Con{K.IInd{nm, lps, ty, np, ni, nn, cs}, tl}:
      nm
    case Con{h, tl}:
      first_ind_nm(tl)

# where a block's verdict is kept in the metadata
def ver_key(+items: List<&2, K.IItem>) -> U32:
  (first_ind_nm(items) + 2147483648 : U32)

def block_ver_v(+items: List<&2, K.IItem>, +mt: R.Tr<I.Meta>) -> V:
  +v : U32 = I.meta_ver(R.get(I.Meta, 64n, mt, ver_key(items), I.MNone{}))
  pick_v(U32.is_eq(v, 0), VAccept{}, VDecline{})

def pick_mt(+z: Bool, +a: R.Tr<I.Meta>, +b: R.Tr<I.Meta>) -> R.Tr<I.Meta>:
  match z:
    case True{}:
      a
    case False{}:
      b

# Every block's recursors go through nested.bend's derivation (it is the
# cheaper one: structural comparison, no defeq). A mutual/nested block also
# takes its rule-based iota metadata from it; a single inductive keeps the
# built-in iota metadata and uses only the verdict (with the older
# derivation as the fallback when this one cannot say, e.g. Prop).
def meta_nm(+nb: Bool, +items: List<&2, K.IItem>, +st: I.IS,
            +itab: R.Tr<K.IItem>, +ctab: R.Tr<U32>, +t: R.Tr<I.Meta>,
            +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
            +ann: List<&2, U32>) -> R.Tr<I.Meta>:
  +vr = N.verify_block(items, st, itab, ctab, t, nt, lp, vt, ann)
  R.set(I.Meta, 64n, pick_mt(nb, N.vr_mt(vr), t), ver_key(items),
        I.MVer{N.vr_v(vr)}, I.MNone{})

# A block another worker checks (fmain's worker K of N): no derivation.
# A mutual/nested block's recursors reduce by the export's own rules --
# exactly what the owning worker verifies the derived ones against
# (nested.bend's verdict 0: "the export's recursors are exactly the derived
# ones"); a single inductive keeps the built-in iota metadata; the block
# reads as verified. The derivation of every block was most of the eight
# minutes every worker spent before its first declaration on con-leche
# (the 25k declarations' trusting pass itself takes 0.2 s).
def meta_tr_items(items: List<&2, K.IItem>, +allit: List<&2, K.IItem>,
                  +ex: R.Tr<T.Ex>, +nmin: U32,
                  +t: R.Tr<I.Meta>) -> R.Tr<I.Meta>:
  match items:
    case Nil{}:
      t
    case Con{head, tail}:
      match head:
        case K.IRec{nm, lps, ty, rp, rni, nmo, kf}:
          +pty = ty
          +t2 = t
          +al2 = allit
          +rp2 : U32 = rp
          +nmo2 : U32 = nmo
          +rs : List<&2, U32> = rules_of_rec(al2, ex, pty, rp2, nmo2, nmin)
          meta_tr_items(tail, al2, ex, nmin,
                        R.set(I.Meta, 64n, t2, nm, I.MRecR{rp2, nmo2, nmin, rni, rs},
                              I.MNone{}))
        case _:
          meta_tr_items(tail, allit, ex, nmin, t)

def meta_tr2(+nb: Bool, +items: List<&2, K.IItem>, +ex: R.Tr<T.Ex>,
             +t: R.Tr<I.Meta>) -> R.Tr<I.Meta>:
  match nb:
    case True{}:
      +its = items
      meta_tr_items(its, its, ex, N.count_rules(its, 0), t)
    case False{}:
      t

def meta_tr(+nb: Bool, +items: List<&2, K.IItem>, +ex: R.Tr<T.Ex>,
            +t: R.Tr<I.Meta>) -> R.Tr<I.Meta>:
  +its = items
  meta_tr2(nb, its, ex,
           R.set(I.Meta, 64n, t, ver_key(its), I.MVer{0}, I.MNone{}))

def meta_owned(+own: Bool, +nb: Bool, +items: List<&2, K.IItem>, +st: I.IS,
               +itab: R.Tr<K.IItem>, +ctab: R.Tr<U32>, +t: R.Tr<I.Meta>,
               +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
               +ann: List<&2, U32>) -> R.Tr<I.Meta>:
  match own:
    case True{}:
      meta_nm(nb, items, st, itab, ctab, t, nt, lp, vt, ann)
    case False{}:
      meta_tr(nb, items, I.is_ex(st), t)

def meta_any(+blk: Bool, +nb: Bool, +own: Bool, +items: List<&2, K.IItem>,
             +st: I.IS, +itab: R.Tr<K.IItem>, +ctab: R.Tr<U32>,
             +t: R.Tr<I.Meta>, +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>,
             +vt: R.Tr<U32>, +ann: List<&2, U32>) -> R.Tr<I.Meta>:
  match blk:
    case True{}:
      meta_owned(own, nb, items, st, itab, ctab, t, nt, lp, vt, ann)
    case False{}:
      t

def dov2(+ok: Bool, +items: List<&2, K.IItem>, +st: I.IS, +mt: R.Tr<I.Meta>,
         +vt: R.Tr<U32>, +ln: R.Tr<L.LN>, +nt: R.Tr<U32>,
         +lp: R.Tr<List<&2, U32>>) -> V:
  match ok:
    case True{}:
      VAccept{}
    case False{}:
      block_derive_v(items, st, mt, vt, ln, nt, lp)

# build_meta, plus: the tables of earlier inductives and constructors, and
# for every mutual/nested block the derivation of its recursors (verdict and
# rule-based iota metadata)
# a single inductive: nested.bend's verdict, or the older derivation
def derive_or_ver(+items: List<&2, K.IItem>, +st: I.IS, +mt: R.Tr<I.Meta>,
                  +vt: R.Tr<U32>, +ln: R.Tr<L.LN>, +nt: R.Tr<U32>,
                  +lp: R.Tr<List<&2, U32>>) -> V:
  +its = items
  +m2 = mt
  dov2(U32.is_eq(I.meta_ver(R.get(I.Meta, 64n, m2, ver_key(its),
                                  I.MNone{})), 0),
       its, st, m2, vt, ln, nt, lp)

# ix counts declarations as fcheck's fck_all does; worker wk of wn owns
# the ones with ix mod wn = wk (the others' inductive blocks are trusted)
def build_meta2(ds: List<&2, K.Dcl>, +st: I.IS, +itab: R.Tr<K.IItem>,
                +ctab: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>,
                +vt: R.Tr<U32>, +ann: List<&2, U32>,
                +t: R.Tr<I.Meta>, +nt: R.Tr<U32>, +ix: U32, +wk: U32,
                +wn: U32) -> R.Tr<I.Meta>:
  match ds:
    case Nil{}:
      t
    case Con{head, tail}:
      +h = head
      +nt2 = B.add_nt(h, nt)
      +lp2 = B.add_lp(h, lp)
      +vt2 = B.add_vt(h, vt)
      +its : List<&2, K.IItem> = K.dcl_items(h)
      +it2 = add_itab(its, itab)
      +ct2 = add_ctab(its, ctab)
      +t1 = meta_block(its, I.is_ex(st), I.is_lnt(st), t, nt2, lp2)
      build_meta2(tail, st, it2, ct2, lp2, vt2, ann,
                  meta_any(U32.is_gt(len_items(ind_only(its, Nil{}), 0), 0),
                           is_nm_block(its), U32.is_eq(U32.mod(ix, wn), wk),
                           its, st, it2, ct2, t1, nt2, lp2, vt2,
                           ann), nt2, (ix + 1 : U32), wk, wn)

def build_meta(ds: List<&2, K.Dcl>, +ex: R.Tr<T.Ex>, +ln: R.Tr<L.LN>,
               +t: R.Tr<I.Meta>) -> R.Tr<I.Meta>:
  match ds:
    case Nil{}:
      t
    case Con{head, tail}:
      match head:
        case K.DInd{nms, items}:
          build_meta(tail, ex, ln, meta_block(items, ex, ln, t, R.TNil{},
                                              R.TNil{}))
        case _:
          build_meta(tail, ex, ln, t)

# --- per declaration ----------------------------------------------------
# A declaration with no value -- an axiom or a quotient constant -- is
# accepted once its type is a type, which is what the official kernel does.
#
# When the declared type is a Sort, the value has to be a type whose universe
# matches, and `sl` decides that outright: this is where arrow types,
# dependent types and `imax` are checked.

# Check a value against a declared type.
#
# Three rules, in order of how much they decide:
#   lambda against Pi  -- descend both binders together. No substitution is
#                         needed: the de Bruijn indices stay aligned.
#   anything against Sort -- the value must be a type of that universe, which
#                         `sl` decides outright.
#   otherwise          -- infer the value's type and compare. The comparison
#                         is structural, so it answers yes or "cannot
#                         decide", never no: two different-looking terms may
#                         still be definitionally equal.
#
# The declared type is weak-head normalised once on the way in, and each
# codomain on the way down, so a type that is a constant unfolding to a Pi
# still matches the first rule.
type CR is Data:
  CR{st: I.IS, r: L.Tri}

def cr_of(+st: I.IS, +r: L.Tri) -> CR:
  CR{st, r}

def cr_st(+c: CR) -> I.IS:
  match c:
    case CR{st, r}:
      st

def cr_r(+c: CR) -> L.Tri:
  match c:
    case CR{st, r}:
      r

# Reduce an index to weak head normal form, carrying the state.
def wh(+st: I.IS, +mt: R.Tr<I.Meta>, +lp: R.Tr<List<&2, U32>>,
       +vt: R.Tr<U32>, +i: U32) -> I.IR:
  I.whd(st, mt, lp, vt, i)

# A failed inference answers "cannot decide", never no: the checker must not
# reject a declaration it was unable to analyse.
def ck_infer(+fuel: Nat, +st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
             +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +x: T.Ex, +e: U32,
             +tye: U32, +ctx: List<&2, U32>) -> CR:
  +ri = I.infer(fuel, st, mt, nt, lp, vt, x, e, ctx)
  +st2 = I.ir_st(ri)
  +w1 = I.whd(st2, mt, lp, vt, I.ir_ty(ri))
  +w2 = I.whd(I.ir_st(w1), mt, lp, vt, tye)
  +st3 = I.ir_st(w2)
  +d = I.defeq(64n, U32.is_eq(I.ir_ty(ri), tye), st3, mt, nt, lp, vt, ctx,
               U.ex_at(I.is_ex(st3), I.ir_ty(w1)),
               U.ex_at(I.is_ex(st3), I.ir_ty(w2)))
  # A definite type error -- `infer` reporting the ill-typed sentinel -- is a
  # REJECTION, not a failure to decide. Everything else keeps the
  # conservative reading: a failed inference answers "cannot decide", never
  # "no", because the checker must not reject a declaration it was unable to
  # analyse.
  cr_of(I.dr_st(d),
        L.pick_tri(U32.is_eq(I.ir_ty(ri), 4294967294), L.TNo{},
                   L.pick_tri(I.ir_ok(ri), I.dr_r(d), L.TUnk{})))

# As `cr_fallback`, but a definite "not a type" is preserved: only an
# undecided universe comparison is retried.
def cr_sort_fallback(+t: L.Tri, +nat: Bool, +fuel: Nat, +st: I.IS,
                     +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
                     +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
                     +x: T.Ex, +e: U32, +tye: U32,
                     +ctx: List<&2, U32>) -> CR:
  match t:
    case L.TYes{}:
      cr_of(st, L.TYes{})
    case L.TNo{}:
      cr_of(st, L.TNo{})
    case L.TUnk{}:
      ck_infer(fuel, st, mt, nt, lp, vt, x, e, tye, ctx)

def cr_fallback(+t: L.Tri, +fuel: Nat, +st: I.IS, +mt: R.Tr<I.Meta>,
                +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
                +x: T.Ex, +e: U32, +tye: U32,
                +ctx: List<&2, U32>) -> CR:
  match t:
    case L.TYes{}:
      cr_of(st, L.TYes{})
    case _:
      ck_infer(fuel, st, mt, nt, lp, vt, x, e, tye, ctx)

def ck_expr(+fuel: Nat, +st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
            +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +x: T.Ex, +e: U32,
            +ty: T.Ex, +tye: U32, +ctx: List<&2, U32>) -> CR:
  match fuel x ty:
    case 0n _ _:
      cr_of(st, L.TUnk{})
    case 1n+p T.ELam{n1, a1, b1, i1} T.EAll{n2, a2, b2, i2}:
      +pf = p
      +pa = a1
      +wc = wh(st, mt, lp, vt, b2)
      +st1 = I.ir_st(wc)
      +ex1 = I.is_ex(st1)
      +sub = ck_expr(pf, st1, mt, nt, lp, vt, U.ex_at(ex1, b1), b1,
                     U.ex_at(ex1, I.ir_ty(wc)), I.ir_ty(wc), Con{pa, ctx})
      +wd1 = I.whd(cr_st(sub), mt, lp, vt, pa)
      +wd2 = I.whd(I.ir_st(wd1), mt, lp, vt, a2)
      +stw = I.ir_st(wd2)
      +dd = I.defeq(64n, U32.is_eq(pa, a2), stw, mt, nt, lp, vt, Con{pa, ctx},
                    U.ex_at(I.is_ex(stw), I.ir_ty(wd1)),
                    U.ex_at(I.is_ex(stw), I.ir_ty(wd2)))
      # If the structural route cannot conclude, fall back to the general
      # rule: infer the whole lambda's type and compare it with the declared
      # one. `Nat.below` is why. Checking it structurally descends into the
      # body and compares a recursor application against the Pi's codomain,
      # which does not conclude; inferring the lambda outright gives
      # `forall motive n, (fun _ => Sort v) n`, and that IS definitionally
      # the declared `forall motive n, Sort v`.
      #
      # A `match`, so the fallback costs nothing when the structural route
      # already succeeded.
      cr_fallback(I.tri_and(I.dr_r(dd), cr_r(sub)), pf, I.dr_st(dd), mt, nt,
                  lp, vt, x, e, tye, ctx)
    # A `let` on the value side is zeta-reduced and re-checked. Without
    # this, `tutorial/033_letType` -- `def letType : Type := let x := Prop; x`
    # -- reaches the Sort rule, which has no rule for `let` and declines.
    case 1n+p T.ELet{ln1, lt1, lv1, lb1} _:
      +pf = p
      +rz = U.inst(256n, I.is_ex(st), I.is_nx(st),
                   U.ex_at(I.is_ex(st), lb1), lb1, 0, lv1)
      +st2 : I.IS = I.IS{U.sr_t(rz), U.sr_nx(rz), I.is_lnt(st),
                         I.is_nlx(st), I.is_wm(st), I.is_ht(st),
                        I.is_natn(st), I.is_strn(st), I.is_qt_t(st)}
      ck_expr(pf, st2, mt, nt, lp, vt,
              U.ex_at(I.is_ex(st2), U.sr_i(rz)), U.sr_i(rz), ty, tye, ctx)
    # The value is checked against a Sort by comparing its universe. `sl`
    # does not reduce, so when the universe cannot be read this falls back to
    # the general rule rather than declining: `008_forallSortWhnf` declares
    # `Sort 0` for a Pi whose domain is an application that has to be
    # unfolded before its universe is visible -- `sl` answers unknown, while
    # inferring the Pi outright gets it right.
    #
    # A definite NO is kept: `not_a_type` is a structural fact, not a
    # failure to compute, so it still rejects.
    case 1n+p _ T.ESort{lt}:
      +pf = p
      +pnat = I.not_a_type(I.is_ex(st), nt, x)
      +scmp = L.pick_tri(pnat, L.TNo{},
                         L.ln_cmp(R.get(L.LN, 64n, I.is_lnt(st), lt,
                                        L.LNun{}),
                                  I.sl(fuel, I.is_ex(st), I.is_lnt(st), nt,
                                       lp, x, ctx)))
      cr_sort_fallback(scmp, pnat, pf, st, mt, nt, lp, vt, x, e, tye, ctx)
    case 1n+p _ _:
      ck_infer(fuel, st, mt, nt, lp, vt, x, e, tye, ctx)

def ck_value(+fuel: Nat, +st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
             +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +ti: U32,
             +vi: U32) -> V:
  +wt = wh(st, mt, lp, vt, ti)
  +st1 = I.ir_st(wt)
  +ex1 = I.is_ex(st1)
  tri_v(cr_r(ck_expr(fuel, st1, mt, nt, lp, vt, U.ex_at(ex1, vi), vi,
                     U.ex_at(ex1, I.ir_ty(wt)), I.ir_ty(wt), Nil{})))

# A theorem's type must be a proposition, and then its value must prove it.
# "Cannot tell whether it is a proposition" declines rather than rejects.
def ck_thm(+t: L.Tri, +fuel: Nat, +st: I.IS, +mt: R.Tr<I.Meta>,
           +nt: R.Tr<U32>,
           +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +ti: U32,
           +vi: U32) -> V:
  match t:
    case L.TNo{}:
      VReject{}
    case L.TUnk{}:
      VDecline{}
    case L.TYes{}:
      ck_value(fuel, st, mt, nt, lp, vt, ti, vi)

def ck_body(+fuel: Nat, +st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
            +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +isthm: Bool,
            +u: L.LN, +ti: U32, +vi: U32) -> V:
  match isthm:
    case True{}:
      ck_thm(L.ln_is_zero(u), fuel, st, mt, nt, lp, vt, ti, vi)
    case False{}:
      pick_v(U32.is_eq(vi, 4294967295), VAccept{},
             ck_value(fuel, st, mt, nt, lp, vt, ti, vi))

# A match cannot scrutinise a local binder either, only a parameter or a
# pattern field, so the decided tri-state is handed to its own def.
def ck_typed2(+t: L.Tri, +fuel: Nat, +st: I.IS, +mt: R.Tr<I.Meta>,
              +nt: R.Tr<U32>,
              +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +isthm: Bool,
              +u: L.LN, +ti: U32, +vi: U32) -> V:
  match t:
    case L.TNo{}:
      VReject{}
    case L.TUnk{}:
      VDecline{}
    case L.TYes{}:
      ck_body(fuel, st, mt, nt, lp, vt, isthm, u, ti, vi)

# The declared type is reduced before its universe is asked for.
# `tutorial/006_betaReduction` declares `betaReduction : constType Prop
# (Prop -> Prop)`, an application that delta- and beta-reduces to `Prop`;
# asking for the universe of the unreduced application answers "unknown" and
# the whole file declines.
# "The declared type is a type" is decided by inferring its type and
# reducing: it is a type exactly when that reduces to a Sort, and the Sort's
# level is the universe the theorem Prop rule needs.
#
# This replaces a `sl`-based test, which had no rule for applications and so
# declined on any declared type with one in it -- which is most real code.
# `tutorial/007_betaReduction2` declares
# `betaReduction2 : forall (_ : Prop), constType Prop (Prop -> Prop)`.
def ck_typed(+fuel: Nat, +st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
             +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +isthm: Bool,
             +ti: U32, +vi: U32) -> V:
  +wt = I.whd(st, mt, lp, vt, ti)
  +st1 = I.ir_st(wt)
  +ti1 = I.ir_ty(wt)
  +tx = U.ex_at(I.is_ex(st1), ti1)
  +ri = I.infer(fuel, st1, mt, nt, lp, vt, tx, ti1, Nil{})
  +wk = I.whd(I.ir_st(ri), mt, lp, vt, I.ir_ty(ri))
  +st2 = I.ir_st(wk)
  +kx = U.ex_at(I.is_ex(st2), I.ir_ty(wk))
  +u = L.pick_ln(I.ir_ok(ri) && I.is_sortx(kx),
                 R.get(L.LN, 64n, I.is_lnt(st2), I.sort_lvl_of(kx),
                       L.LNun{}),
                 L.LNun{})
  # A declared type that is itself ILL-TYPED -- `infer` reporting the
  # sentinel -- is a rejection, not a failure to decide. `093_projProp5`
  # declares a type mentioning `proj 3` of a Prop structure whose dependent
  # data field is 3, and declining there masked the value check, which
  # already rejects.
  pick_v(U32.is_eq(I.ir_ty(ri), 4294967294), VReject{},
         ck_typed2(I.type_tri(I.not_a_type(I.is_ex(st2), nt, tx), u), fuel,
                   st2, mt, nt, lp, vt, isthm, u, ti1, vi))

def ck_one(+fuel: Nat, +st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
           +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +nmt: R.Tr<T.Nm>,
           +d: K.Dcl) -> V:
  match d:
    case K.DInd{nms, items}:
      +its = items
      # The block's own names are in scope for the checks that read a
      # CONSTRUCTOR's type. A constructor's fields refer to the inductive
      # being declared -- `Acc.intro`'s recursive field has type
      # `forall y, r y x -> Acc r y` -- and with the environment extended
      # only after the declaration is checked, `Acc` was an unknown constant
      # there. Its universe came back unknown, so "is every field a
      # proposition" was undecidable and the whole block declined. That is
      # the order the kernel uses too: the inductive types are added, then
      # the constructors are checked against them.
      #
      # Only these two checks see the extended table. `ind_items` and
      # `ctor_all` are the structural ones, and `scan_consts` in `judge`
      # still answers for genuinely unknown names.
      +ntb = B.add_items_nt(its, nt)
      comb(comb(comb(ind_items(its, I.is_ex(st), nt, vt, VAccept{}),
                     ctor_all(its, I.is_ex(st),
                              ind_names_of(its, Nil{}), VAccept{})),
                block_rec_v(its, I.is_ex(st), I.is_lnt(st), ntb, lp)),
           comb(block_derive_v(its, st, mt, vt, I.is_lnt(st), ntb, lp),
                block_names_v(its, nmt)))
    case K.DNone{}:
      VDecline{}
    case _:
      +pd = d
      comb(self_ref_v(I.is_ex(st), pd),
           ck_typed(fuel, st, mt, nt, lp, vt, K.dcl_is_theorem(pd),
                    K.dcl_type(pd), K.dcl_value(pd)))

# Each declaration is checked against the environment built from the ones
# before it, and only then added. Terms built while checking one declaration
# are invisible to the next, which is correct and means no index threading.
def ck_all(ds: List<&2, K.Dcl>, +fuel: Nat, +st: I.IS,
           +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
           +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +nmt: R.Tr<T.Nm>,
           +acc: V) -> V:
  match ds:
    case Nil{}:
      acc
    case Con{head, tail}:
      +h = head
      ck_all(tail, fuel, st, mt, B.add_nt(h, nt), B.add_lp(h, lp),
             B.add_vt(h, vt), nmt,
             comb(acc, ck_one(fuel, st, mt, nt, lp, vt, nmt, h)))

# `nx` and `nlx` start above every index the export used, so terms built
# while checking cannot collide with the exporter's own numbering.
def judge(+recs: List<&2, D.Rec>, +ds: List<&2, K.Dcl>, +nex: Nat,
          +nlv: Nat, +rounds: Nat, +nx: U32) -> V:
  +ex = B.build_ex(recs, R.TNil{})
  +ln = B.lv_resolve(rounds, nlv, B.build_lv(recs, R.TNil{}), R.TNil{})
  +dn = mark_names(Con{0, declared(ds, Nil{})}, R.TNil{})
  +st : I.IS = I.IS{ex, nx, ln, nx, R.TNil{}, K.build_ht(recs, R.TNil{}),
                    K.find_name(recs, [78, 97, 116], 4294967295),
                    K.find_name(recs,
                                [83, 116, 114, 105, 110, 103], 4294967295),
                    K.build_wk2(recs, R.TNil{})}
  +strt = build_str(ds, R.TNil{})
  comb(comb(pre_check(ds),
            comb(bad_v(scan_consts(nex, 0, ex, dn,
                                   False{})),
                 scan_projs(nex, 0, ex, strt, VAccept{}))),
       ck_all(ds, 8192n, st, build_meta(ds, ex, ln, R.TNil{}), R.TNil{},
              R.TNil{}, R.TNil{}, K.build_nm(recs, R.TNil{}),
              VAccept{}))
