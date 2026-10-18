# Universe levels in normal form.
#
# A level is a maximum over atoms, each atom a base plus an offset: base 0 is
# `Level.zero` and base n+1 is `Level.param` with name index n. So
# `max (u+2) 1` is the atom set {(u+1, 2), (0, 1)}. This is the standard
# normal form and it decides equality for everything except an `imax` whose
# right operand might be zero, which it cannot express and which therefore
# answers LNsym -- "cannot decide" -- so the checker declines rather than
# rejecting a level it does not understand.
#
# Normal forms are NOT computed by an ascending pass over the table. The
# arena's `other/level-index-out-of-order` test declares `il 1 = succ 2`
# before `il 2 = succ 0`, and expects that accepted: the format requires the
# indices be integers, not that references point backwards. See level_resolve.

import Base
import ./scan.bend as S
import ./term.bend as T

type Atom is Data:
  At{base: U32, off: U32}

# A level normal form. `LNmax` is a max over atoms (`base + offset`), which
# covers everything built from zero, succ, max and parameters.
#
# `LNimax` is the form that max-of-atoms cannot express: `imax a b` where `b`
# is neither provably zero nor provably positive -- a bare parameter. Lean
# writes these constantly: the Church-numeral type
# `PN : forall (a : Sort u), (a -> a) -> a -> a` has declared universe
# `imax (succ u) u`. Collapsing that to "symbolic" made every universe
# downstream of a polymorphic declaration undecidable, which declined
# `PN` and, through it, `peano1`, `peano2` and `peano3`.
#
# Keeping it structural costs nothing and buys the only question that
# actually gets asked of it: whether two of them are *the same*. The `off`
# field carries an outer `succ` count, so `succ (imax a b)` stays comparable
# instead of degrading.
type LN is Data:
  LNun{}
  LNsym{}
  LNmax{xs: List<&2, Atom>}
  LNimax{a: LN, b: LN, off: U32}

def ln_zero() -> LN:
  LNmax{[At{0, 0}]}

# (b, k) covers (b', k') when they share a base and the offset is no smaller,
# or when the covered atom is a bare offset: a parameter is at least zero, so
# p + k' is always at least k'.
def covers(+x: Atom, +y: Atom) -> Bool:
  match x y:
    case At{xb, xo} At{yb, yo}:
      (U32.is_eq(xb, yb) || U32.is_eq(yb, 0)) && U32.is_ge(xo, yo)

def any_covers(+y: Atom, xs: List<&2, Atom>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{head, tail}:
      covers(head, y) || any_covers(y, tail)

# Every atom of xs is covered by some atom of ys.
def atoms_sub(xs: List<&2, Atom>, +ys: List<&2, Atom>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{head, tail}:
      any_covers(head, ys) && atoms_sub(tail, ys)

def off_add(+k: U32, xs: List<&2, Atom>) -> List<&2, Atom>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{head, tail}:
      match head:
        case At{b, o}:
          Con{At{b, (o + k : U32)}, off_add(k, tail)}

# True when the level is at least one, which is what lets `imax a b` collapse
# to `max a b`: any atom with a positive offset forces it, since a parameter
# is at least zero.
def some_positive(xs: List<&2, Atom>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{head, tail}:
      match head:
        case At{b, o}:
          U32.is_ge(o, 1) || some_positive(tail)

# True when every atom is the zero atom, so the level is exactly zero.
def all_zero(xs: List<&2, Atom>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{head, tail}:
      match head:
        case At{b, o}:
          U32.is_eq(b, 0) && U32.is_eq(o, 0) && all_zero(tail)

# Three-valued on purpose. Folding "cannot decide" into "not equal" is how a
# checker rejects valid proofs; it cost nine wrong arena answers once already.
type Tri is Data:
  TYes{}
  TNo{}
  TUnk{}

def tri_is_yes(+t: Tri) -> Bool:
  match t:
    case TYes{}:
      True{}
    case _:
      False{}

def tri_is_no(+t: Tri) -> Bool:
  match t:
    case TNo{}:
      True{}
    case _:
      False{}

def pick_tri(+z: Bool, +x: Tri, +y: Tri) -> Tri:
  match z:
    case True{}:
      x
    case False{}:
      y

def tri_of(+z: Bool) -> Tri:
  match z:
    case True{}:
      TYes{}
    case False{}:
      TNo{}

def pick_ln(+z: Bool, +x: LN, +y: LN) -> LN:
  match z:
    case True{}:
      x
    case False{}:
      y

def ln_succ(+a: LN) -> LN:
  match a:
    case LNmax{xs}:
      LNmax{off_add(1, xs)}
    case LNimax{x, y, o}:
      LNimax{x, y, (o + 1 : U32)}
    case LNun{}:
      LNun{}
    case LNsym{}:
      LNsym{}

def ln_add_off(+k: U32, +a: LN) -> LN:
  match a:
    case LNmax{xs}:
      LNmax{off_add(k, xs)}
    case LNimax{x, y, o}:
      LNimax{x, y, (o + k : U32)}
    case LNun{}:
      LNun{}
    case LNsym{}:
      LNsym{}

def ln_max(+a: LN, +b: LN) -> LN:
  match a b:
    case LNun{} _:
      LNun{}
    case _ LNun{}:
      LNun{}
    case LNmax{xs} LNmax{ys}:
      LNmax{List.append(&2, Atom, xs, ys)}
    case _ _:
      LNsym{}

# `imax a b` is zero when b is, and `max a b` when b is at least one. When b
# is a bare parameter it could be either, and no max-of-atoms form expresses
# that -- so it is kept as a structural `LNimax`, which is still comparable
# even though it is not decidable. `imax a a = a` is applied here, as Lean's
# own smart constructor does: without it the universe this checker infers for
# a polymorphic type does not match the one the export declares.
def imax_case(+isz: Bool, +pos: Bool, xs: List<&2, Atom>,
              ys: List<&2, Atom>) -> LN:
  match isz pos:
    case True{} _:
      ln_zero()
    case False{} True{}:
      LNmax{List.append(&2, Atom, xs, ys)}
    case False{} False{}:
      +px = xs
      +py = ys
      +same = atoms_sub(px, py) && atoms_sub(py, px)
      +l : LN = LNmax{px}
      +r : LN = LNmax{py}
      pick_ln(same, l, LNimax{l, r, 0})

# Structural equality, used by the `imax` smart constructor below. Separate
# from `ln_cmp` because that one is semantic for the max-of-atoms case (set
# equality over atoms) and three-valued, and must be defined after this.
def ln_eq(fuel: Nat, +a: LN, +b: LN) -> Bool:
  match fuel a b:
    case 0n _ _:
      False{}
    case 1n+p LNmax{xs} LNmax{ys}:
      +px = xs
      +py = ys
      atoms_sub(px, py) && atoms_sub(py, px)
    case 1n+p LNimax{x1, y1, o1} LNimax{x2, y2, o2}:
      +pf = p
      U32.is_eq(o1, o2) && ln_eq(pf, x1, x2) && ln_eq(pf, y1, y2)
    case 1n+p _ _:
      False{}

def is_zero_ln(+a: LN) -> Bool:
  match a:
    case LNmax{xs}:
      all_zero(xs)
    case _:
      False{}

# The same identities Lean's own `Level.imax` smart constructor applies:
#   imax a 0 = 0,  imax a (succ b) = max a (succ b),  imax a a = a,
#   imax 0 b = b
# and otherwise keep it structural. The last two matter here: without
# `imax a a = a` the universe this checker *infers* for a polymorphic type
# does not match the one the export *declares*, even though both are the
# same level, and the Sort comparison then declines.
def imax_keep(+same: Bool, +azero: Bool, +a: LN, +b: LN) -> LN:
  match same azero:
    case True{} _:
      a
    case False{} True{}:
      b
    case False{} False{}:
      LNimax{a, b, 0}

def ln_imax(+a: LN, +b: LN) -> LN:
  match a b:
    case LNun{} _:
      LNun{}
    case _ LNun{}:
      LNun{}
    case LNmax{xs} LNmax{ys}:
      +py = ys
      imax_case(all_zero(py), some_positive(py), xs, py)
    case _ _:
      +pa : LN = a
      +pb : LN = b
      pick_ln(is_zero_ln(pb), ln_zero(),
              imax_keep(ln_eq(32n, pa, pb), is_zero_ln(pa), pa, pb))

# "Both, three-valued": no unless either is no, otherwise unknown if either
# is unknown. `infer` has its own copy; this module cannot import it.
def tri_both(+a: Tri, +b: Tri) -> Tri:
  match a b:
    case TNo{} _:
      TNo{}
    case _ TNo{}:
      TNo{}
    case TUnk{} _:
      TUnk{}
    case _ TUnk{}:
      TUnk{}
    case _ _:
      TYes{}

# Structural, and three-valued. Two `imax` forms are equal when both halves
# and the offset are; anything else mixing the two shapes is "cannot decide",
# never "no" -- an `imax` really can equal a max-of-atoms for some
# instantiation, so denying it would be unsound.
def ln_cmp_f(fuel: Nat, +a: LN, +b: LN) -> Tri:
  match fuel a b:
    case 0n _ _:
      TUnk{}
    case 1n+p LNmax{xs} LNmax{ys}:
      +px = xs
      +py = ys
      tri_of(atoms_sub(px, py) && atoms_sub(py, px))
    case 1n+p LNimax{x1, y1, o1} LNimax{x2, y2, o2}:
      +pf = p
      tri_both(tri_of(U32.is_eq(o1, o2)),
               tri_both(ln_cmp_f(pf, x1, x2), ln_cmp_f(pf, y1, y2)))
    case 1n+p LNimax{x1, y1, o1} LNmax{ys}:
      TUnk{}
    case 1n+p LNmax{xs} LNimax{x2, y2, o2}:
      TUnk{}
    case 1n+p _ _:
      TUnk{}

def ln_cmp(+a: LN, +b: LN) -> Tri:
  ln_cmp_f(32n, a, b)

# Three-valued, and it matters. `Sort u` for a universe PARAMETER `u` is
# neither provably zero nor provably non-zero: u could be 0. Answering "not
# zero" there told the large-elimination rule that `MyBool : Sort u` is not a
# Prop, so a two-constructor type got large elimination and
# `bugs/large-elim-param` was accepted. Lean is conservative for exactly this
# reason: a universe that might be Prop gets no large elimination.
#
# The same function decides the theorem Prop rule, where "not zero" would
# have rejected a polymorphic theorem.
def ln_is_zero(+a: LN) -> Tri:
  match a:
    case LNmax{xs}:
      +px = xs
      pick_tri(all_zero(px), TYes{},
               pick_tri(some_positive(px), TNo{}, TUnk{}))
    # `imax a b + off` with off > 0 is a successor, so positive. With off 0
    # it is `b` when `b` is zero and `max a b` otherwise, and `b` here is by
    # construction neither -- so: cannot decide.
    case LNimax{x, y, o}:
      pick_tri(U32.is_gt(o, 0), TNo{}, TUnk{})
    case _:
      TUnk{}

# --- substituting a declaration's level parameters -----------------------
# A `const` carries one level argument per parameter of the declaration it
# names, and the declaration's type is read under that substitution.
def find_pos(+v: U32, ps: List<&2, U32>, +i: U32, +miss: U32) -> U32:
  match ps:
    case Nil{}:
      miss
    case Con{head, tail}:
      S.pick(U32.is_eq(head, v), i, find_pos(v, tail, (i + 1 : U32), miss))

def nth_ln(qs: List<&2, LN>, +i: U32) -> LN:
  match qs:
    case Nil{}:
      LNun{}
    case Con{head, tail}:
      pick_ln(U32.is_eq(i, 0), head, nth_ln(tail, (i - 1 : U32)))

# A parameter not in the declaration's list stays free: that is not an error
# here, only something the caller may reject on.
def sub_case(+isz: Bool, +b: U32, +o: U32, +ps: List<&2, U32>,
             +qs: List<&2, LN>) -> LN:
  match isz:
    case True{}:
      LNmax{[At{0, o}]}
    case False{}:
      +pos = find_pos((b - 1 : U32), ps, 0, 4294967295)
      pick_ln(U32.is_eq(pos, 4294967295),
              LNmax{[At{b, o}]},
              ln_add_off(o, nth_ln(qs, pos)))

def atom_subst(+x: Atom, +ps: List<&2, U32>, +qs: List<&2, LN>) -> LN:
  match x:
    case At{b, o}:
      sub_case(U32.is_eq(b, 0), b, o, ps, qs)

def ln_subst_go(xs: List<&2, Atom>, +ps: List<&2, U32>, +qs: List<&2, LN>,
                +acc: LN) -> LN:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      ln_subst_go(tail, ps, qs, ln_max(acc, atom_subst(head, ps, qs)))

# Substituting into an `imax` can make the right half decidable -- `imax u v`
# with `v := 0` is `0` -- so the halves are substituted and the result is
# rebuilt through `ln_imax`, which re-applies those rules.
def ln_subst_f(fuel: Nat, +a: LN, +ps: List<&2, U32>,
               +qs: List<&2, LN>) -> LN:
  match fuel a:
    case 0n _:
      LNun{}
    case 1n+p LNmax{xs}:
      ln_subst_go(xs, ps, qs, ln_zero())
    case 1n+p LNimax{x, y, o}:
      +pf = p
      ln_add_off(o, ln_imax(ln_subst_f(pf, x, ps, qs),
                            ln_subst_f(pf, y, ps, qs)))
    case 1n+p LNun{}:
      LNun{}
    case 1n+p LNsym{}:
      LNsym{}

def ln_subst(+a: LN, +ps: List<&2, U32>, +qs: List<&2, LN>) -> LN:
  ln_subst_f(32n, a, ps, qs)

# --- resolving the level table ------------------------------------------
# References may point forward (`other/level-index-out-of-order`), so normal
# forms are computed by repeated passes rather than one ascending sweep. An
# unresolved child propagates as LNun, so a level whose children are not yet
# known simply stays unknown and a later pass fills it in. Any level still
# unresolved when the rounds run out stays LNun, which compares as "cannot
# decide" and makes the checker decline -- never reject.

type P1 is Type:
  P1{lv: Array<T.Lvl>, ln: Array<LN>, ch: Bool}

def is_un(+a: LN) -> Bool:
  match a:
    case LNun{}:
      True{}
    case _:
      False{}

# 0 zero, 1 succ, 2 max, 3 imax, 4 param.
def op_of(+l: T.Lvl) -> U32:
  match l:
    case T.LZero{}:
      0
    case T.LSucc{x}:
      1
    case T.LMax{a, b}:
      2
    case T.LIMax{a, b}:
      3
    case T.LParam{n}:
      4

def c1_of(+l: T.Lvl) -> U32:
  match l:
    case T.LZero{}:
      0
    case T.LSucc{x}:
      x
    case T.LMax{a, b}:
      a
    case T.LIMax{a, b}:
      a
    case T.LParam{n}:
      n

def c2_of(+l: T.Lvl) -> U32:
  match l:
    case T.LMax{a, b}:
      b
    case T.LIMax{a, b}:
      b
    case _:
      0

def combine(+op: U32, +c1: U32, +ln1: LN, +ln2: LN) -> LN:
  pick_ln(U32.is_eq(op, 0), ln_zero(),
    pick_ln(U32.is_eq(op, 1), ln_succ(ln1),
      pick_ln(U32.is_eq(op, 2), ln_max(ln1, ln2),
        pick_ln(U32.is_eq(op, 3), ln_imax(ln1, ln2),
                LNmax{[At{(c1 + 1 : U32), 0}]}))))

def s4(+i: U32, +op: U32, +c1: U32, +ch: Bool, lv: Array<T.Lvl>, +old: LN,
       +ln1: LN, r: Array<LN> & LN) -> P1:
  match r:
    case Tuple{ln, ln2}:
      +v = combine(op, c1, ln1, ln2)
      +wasun = is_un(old)
      P1{lv, Array.set(LN, ln, i, pick_ln(wasun, v, old)),
         ch || (wasun && Bool.not(is_un(v)))}

def s3(+i: U32, +op: U32, +c1: U32, +c2: U32, +ch: Bool, lv: Array<T.Lvl>,
       +old: LN, r: Array<LN> & LN) -> P1:
  match r:
    case Tuple{ln, ln1}:
      s4(i, op, c1, ch, lv, old, ln1, Array.get(LN, ln, c2))

def s2(+i: U32, +op: U32, +c1: U32, +c2: U32, +ch: Bool, lv: Array<T.Lvl>,
       r: Array<LN> & LN) -> P1:
  match r:
    case Tuple{ln, old}:
      s3(i, op, c1, c2, ch, lv, old, Array.get(LN, ln, c1))

def s1(+i: U32, +ch: Bool, ln: Array<LN>, r: Array<T.Lvl> & T.Lvl) -> P1:
  match r:
    case Tuple{lv, l}:
      +pl = l
      s2(i, op_of(pl), c1_of(pl), c2_of(pl), ch, lv, Array.get(LN, ln, i))

def one_pass(k: Nat, +i: U32, p: P1) -> P1:
  match k p:
    case 0n P1{lv, ln, ch}:
      P1{lv, ln, ch}
    case 1n+q P1{lv, ln, ch}:
      one_pass(q, (i + 1 : U32), s1(i, ch, ln, Array.get(T.Lvl, lv, i)))

# Fixed rounds rather than an early exit: a helper that tested the changed
# flag would have to call back here, and Bend forbids mutual recursion.
def resolve(rounds: Nat, +n: Nat, p: P1) -> P1:
  match rounds:
    case 0n:
      p
    case 1n+q:
      resolve(q, n, one_pass(n, 0, p))
