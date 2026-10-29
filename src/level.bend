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
  # `max (atoms xs) y r`: y an imax that max-of-atoms cannot express, r the
  # REST of the maximum (LNmax{[]} for none, another imax, or another
  # LNmx) -- a chain, so every operation is plain structural recursion on
  # LN itself (a separate list type would need helpers recursing back into
  # ln_eq/ln_cmp: mutual recursion). What `PULift.{r,s} : Sort (max s r 1)`
  # and `cond` over two PULifts become once s is an imax. Equality is
  # structural (order-sensitive): sound for YES, compared YES-or-unknown.
  LNmx{xs: List<&2, Atom>, y: LN, r: LN}

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

def tri_is_unk(+t: Tri) -> Bool:
  match t:
    case TUnk{}:
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

# bump the outer successor count of an imax term (an LNmx's y)
def imax_off(+k: U32, +y: LN) -> LN:
  match y:
    case LNimax{a, b, o}:
      LNimax{a, b, (o + k : U32)}
    case _:
      LNsym{}

def ln_add_off(+k: U32, +a: LN) -> LN:
  match a:
    case LNmax{xs}:
      LNmax{off_add(k, xs)}
    case LNmx{xs, y, r}:
      LNmx{off_add(k, xs), imax_off(k, y), ln_add_off(k, r)}
    case LNimax{x, y, o}:
      LNimax{x, y, (o + k : U32)}
    case LNun{}:
      LNun{}
    case LNsym{}:
      LNsym{}

def ln_succ(+a: LN) -> LN:
  match a:
    case LNmax{xs}:
      LNmax{off_add(1, xs)}
    case LNmx{xs, y, r}:
      LNmx{off_add(1, xs), imax_off(1, y), ln_add_off(1, r)}
    case LNimax{x, y, o}:
      LNimax{x, y, (o + 1 : U32)}
    case LNun{}:
      LNun{}
    case LNsym{}:
      LNsym{}

def atom_small(+x: Atom) -> Bool:
  match x:
    case At{b, o}:
      U32.is_eq(b, 0) && U32.is_le(o, 1)

# every atom of xs is bounded by ys whenever ys >= 1: a constant atom of
# offset <= 1, or one some atom of ys covers. Then `imax xs ys = ys`:
# ys = 0 gives 0 on both sides; ys >= 1 gives max xs ys = ys.
# Subsumes `imax 0 b = b` and `imax b b = b`; also `imax 1 u = u`, which a
# casesOn motive `List a -> Sort u` needs (inferred imax(1,u) vs declared u).
def imax_absorbed(xs: List<&2, Atom>, +ys: List<&2, Atom>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{head, tail}:
      +h = head
      (atom_small(h) || any_covers(h, ys)) && imax_absorbed(tail, ys)

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
      # imax a b = b when a is absorbed by b (see imax_absorbed). Without it
      # `imax (imax 0 u) u` -- the universe of `(h : a = b) -> P -> P`, every
      # noConfusionType -- stayed structural and never matched `u`.
      pick_ln(same || imax_absorbed(px, py), r, LNimax{l, r, 0})

# Structural equality, used by the `imax` smart constructor below. Separate
# from `ln_cmp` because that one is semantic for the max-of-atoms case (set
# equality over atoms) and three-valued, and must be defined after this.
def pick_atoms(+z: Bool, +x: List<&2, Atom>, +y: List<&2, Atom>) -> List<&2, Atom>:
  match z:
    case True{}:
      x
    case False{}:
      y

# drop `0` atoms (base 0, offset 0): max 0 x = x, so they never matter;
# mixed forms built along different paths may or may not carry one
def strip_zero(xs: List<&2, Atom>) -> List<&2, Atom>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{head, tail}:
      match head:
        case At{b, o}:
          +pb = b
          +po = o
          +rest = strip_zero(tail)
          pick_atoms(U32.is_eq(pb, 0) && U32.is_eq(po, 0), rest,
                     Con{At{pb, po}, rest})

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
    case 1n+p LNmx{xs, y1, r1} LNmx{ys, y2, r2}:
      +pf = p
      +px = strip_zero(xs)
      +py = strip_zero(ys)
      atoms_sub(px, py) && atoms_sub(py, px) && ln_eq(pf, y1, y2)
        && ln_eq(pf, r1, r2)
    case 1n+p LNmx{xs, y1, r1} LNimax{x2, y2, o2}:
      +pf = p
      ln_eq(pf, a, LNmx{Nil{}, b, LNmax{Nil{}}})
    case 1n+p LNimax{x1, y1, o1} LNmx{ys, y2, r2}:
      +pf = p
      ln_eq(pf, LNmx{Nil{}, a, LNmax{Nil{}}}, b)
    case 1n+p _ _:
      False{}

# --- canonical order of a mixed chain --------------------------------------
# Lean's level::normalize sorts the arguments of a max and drops duplicates,
# so `max s r 1` (PULift's sort) and `max 1 (max (imax ..) (imax ..))` (the
# declared sort of an auto-generated ctorElimType) compare equal although
# their components arrive in different orders. A mixed chain is kept with
# its atoms merged at the head and its imax components in ascending order of
# a structural key (order-independent over atom sets, offset-independent so
# that adding a successor keeps a chain sorted), without duplicates
# (ln_eq); the order-sensitive structural comparisons below then decide
# set equality. A key collision only leaves a chain unsorted (an unknown,
# never a wrong answer).
def atoms_key(xs: List<&2, Atom>, +h: U32) -> U32:
  match xs:
    case Nil{}:
      h
    case Con{head, tail}:
      match head:
        case At{base, off}:
          atoms_key(tail, (h + ((base * 1000003 : U32) + 1 : U32) : U32))

def ln_key(fuel: Nat, +a: LN) -> U32:
  match fuel a:
    case 0n _:
      0
    case 1n+p LNmax{xs}:
      atoms_key(xs, 7)
    case 1n+p LNimax{x, y, o}:
      +pf = p
      (((ln_key(pf, x) * 31 : U32) + (ln_key(pf, y) * 17 : U32) : U32) + 3 : U32)
    case 1n+p LNmx{xs, y, r}:
      +pf = p
      ((atoms_key(xs, 11) + (ln_key(pf, y) * 13 : U32) : U32) + (ln_key(pf, r) * 7 : U32) : U32)
    case 1n+p _:
      1

def mx_ins_go(+same: Bool, +before: Bool, +y: LN, xs: List<&2, Atom>, +y1: LN,
              +r: LN, +ins_r: LN) -> LN:
  match same before:
    case True{} _:
      LNmx{xs, y1, r}
    case False{} True{}:
      LNmx{xs, y, LNmx{Nil{}, y1, r}}
    case False{} False{}:
      LNmx{xs, y1, ins_r}

# insert the imax component y into the chain c (atoms stay at the head)
def mx_insert(fuel: Nat, +y: LN, +c: LN) -> LN:
  match fuel c:
    case 0n _:
      LNmx{Nil{}, y, c}
    case 1n+p LNmx{xs, y1, r}:
      +py : LN = y
      +py1 : LN = y1
      +pr : LN = r
      mx_ins_go(ln_eq(32n, py, py1), U32.is_lt(ln_key(16n, py), ln_key(16n, py1)),
                py, xs, py1, pr, mx_insert(p, py, pr))
    case 1n+p LNmax{xs}:
      LNmx{xs, y, LNmax{Nil{}}}
    case 1n+p LNimax{x1, y1, o1}:
      mx_insert(p, y, LNmx{Nil{}, c, LNmax{Nil{}}})
    case 1n+p _:
      c

def mx_add_atoms(xs: List<&2, Atom>, +c: LN) -> LN:
  match c:
    case LNmx{ys, y, r}:
      LNmx{List.append(&2, Atom, xs, ys), y, r}
    case LNmax{ys}:
      LNmax{List.append(&2, Atom, xs, ys)}
    case _:
      c

# rebuild a chain in canonical order; anything else is returned as is
def mx_fold(fuel: Nat, +a: LN, +acc: LN) -> LN:
  match fuel a:
    case 0n _:
      acc
    case 1n+p LNmx{xs, y, r}:
      mx_fold(p, r, mx_insert(16n, y, mx_add_atoms(xs, acc)))
    case 1n+p LNimax{x, y, o}:
      mx_insert(16n, a, acc)
    case 1n+p LNmax{xs}:
      mx_add_atoms(xs, acc)
    case 1n+p _:
      a

def mx_norm(+a: LN) -> LN:
  match a:
    case LNmx{xs, y, r}:
      mx_fold(16n, a, LNmax{Nil{}})
    case _:
      a

# Mixing a max-of-atoms with an `imax` has no max-of-atoms form, but two
# cases are exact and common: `max 0 x = x` and `max x x = x`. The first is
# what level SUBSTITUTION hits on every parameter instantiated to an imax --
# ln_subst_go folds atoms into an accumulator that starts at zero -- so
# without it `Eq.{imax u v} (a -> b)` (any equality at a function type in a
# universe-polymorphic statement: congr, congrFun, funext) read Eq's
# parameter type as `Sort LNsym`, undecidable, and declined.
def ln_max0(+a: LN, +b: LN) -> LN:
  match a b:
    case LNun{} _:
      LNun{}
    case _ LNun{}:
      LNun{}
    case LNmax{xs} LNmax{ys}:
      LNmax{List.append(&2, Atom, xs, ys)}
    case LNmax{xs} LNmx{ys, y, r}:
      LNmx{List.append(&2, Atom, xs, ys), y, r}
    case LNmx{xs, y, r} LNmax{ys}:
      LNmx{List.append(&2, Atom, xs, ys), y, r}
    case LNmx{xs, y1, r1} LNmx{ys, y2, r2}:
      LNmx{List.append(&2, Atom, xs, ys), y1,
           ln_max0(r1, LNmx{Nil{}, y2, r2})}
    case LNmx{xs, y1, r1} LNimax{p, q, o}:
      +py1 : LN = y1
      pick_ln(ln_eq(32n, py1, b), a, LNmx{xs, py1, ln_max0(r1, b)})
    case LNimax{p, q, o} LNmx{ys, y2, r2}:
      +py2 : LN = y2
      pick_ln(ln_eq(32n, py2, a), b, LNmx{ys, py2, ln_max0(a, r2)})
    case LNmax{xs} LNimax{p, q, o}:
      +px = xs
      pick_ln(all_zero(px), b, LNmx{px, b, LNmax{Nil{}}})
    case LNimax{p, q, o} LNmax{ys}:
      +py = ys
      pick_ln(all_zero(py), a, LNmx{py, a, LNmax{Nil{}}})
    case LNimax{p1, q1, o1} LNimax{p2, q2, o2}:
      pick_ln(ln_eq(32n, a, b), a, LNmx{Nil{}, a, b})
    case LNmax{xs} _:
      pick_ln(all_zero(xs), b, LNsym{})
    case _ LNmax{ys}:
      pick_ln(all_zero(ys), a, LNsym{})
    case _ _:
      pick_ln(ln_eq(32n, a, b), a, LNsym{})

def ln_max(+a: LN, +b: LN) -> LN:
  mx_norm(ln_max0(a, b))

def is_zero_ln(+a: LN) -> Bool:
  match a:
    case LNmax{xs}:
      all_zero(xs)
    case _:
      False{}

# every atom a constant of offset at most 1, and one of them exactly 1:
# the level is exactly one
def atoms_one(xs: List<&2, Atom>, +seen: Bool) -> Bool:
  match xs:
    case Nil{}:
      seen
    case Con{head, tail}:
      match head:
        case At{base, off}:
          +o2 : U32 = off
          U32.is_eq(base, 0) && U32.is_le(o2, 1)
          && atoms_one(tail, seen || U32.is_eq(o2, 1))

def is_one_ln(+a: LN) -> Bool:
  match a:
    case LNmax{xs}:
      atoms_one(xs, False{})
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

# never zero (Lean's is_not_zero): an atom with a positive offset, an imax
# whose second part is never zero or that carries a successor, or such a
# component of a mixed chain
def ln_pos(fuel: Nat, +a: LN) -> Bool:
  match fuel a:
    case 0n _:
      False{}
    case 1n+p LNmax{xs}:
      some_positive(xs)
    case 1n+p LNimax{x, y, o}:
      U32.is_ge(o, 1) || ln_pos(p, y)
    case 1n+p LNmx{xs, y, r}:
      +pf = p
      some_positive(xs) || ln_pos(pf, y) || ln_pos(pf, r)
    case 1n+p _:
      False{}

# Lean's mk_imax: `imax a b = max a b` when b is never zero
def imax_pos(+pos: Bool, +a: LN, +b: LN) -> LN:
  match pos:
    case True{}:
      ln_max(a, b)
    case False{}:
      # Lean's mk_imax: `imax a b = b` when a is zero OR ONE (`is_one`),
      # whatever b is -- `Π (n : Nat), B` over a structural imax B
      pick_ln(is_zero_ln(b), ln_zero(),
              imax_keep(ln_eq(32n, a, b), is_zero_ln(a) || is_one_ln(a),
                        a, b))

def ln_imax_go(+a: LN, +b: LN) -> LN:
  match a b:
    case LNun{} _:
      LNun{}
    case _ LNun{}:
      LNun{}
    case LNmax{xs} LNmax{ys}:
      +py = ys
      imax_case(all_zero(py), some_positive(py), xs, py)
    case _ _:
      +pb : LN = b
      imax_pos(ln_pos(32n, pb), a, pb)

# imax a 0 = 0 whatever a is -- even an unknown a: a Pi into a Prop is a
# Prop however large its domain (a class of Prop fields over binders the
# oracle cannot size was undecided, and its recursor declined)
def ln_imax_z(+bz: Bool, +a: LN, +b: LN) -> LN:
  match bz:
    case True{}:
      ln_zero()
    case False{}:
      ln_imax_go(a, b)

def ln_imax(+a: LN, +b: LN) -> LN:
  +b2 : LN = b
  ln_imax_z(is_zero_ln(b2), a, b2)

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
    # The imax comparison may answer yes or unknown but never NO: two
    # structurally different imax forms can be semantically equal --
    # `imax(1, u)` and `imax(max(1, u), u)` agree at every u -- so a
    # mismatch of halves proves nothing. The max-of-atoms case above may
    # deny, because the covering-pruned atom set is a canonical form.
    case 1n+p LNimax{x1, y1, o1} LNimax{x2, y2, o2}:
      +pf = p
      pick_tri(tri_is_yes(tri_both(tri_of(U32.is_eq(o1, o2)),
                                   tri_both(ln_cmp_f(pf, x1, x2),
                                            ln_cmp_f(pf, y1, y2)))),
               TYes{}, TUnk{})
    case 1n+p LNimax{x1, y1, o1} LNmax{ys}:
      TUnk{}
    case 1n+p LNmax{xs} LNimax{x2, y2, o2}:
      TUnk{}
    # mixed max: equal atom sets and an equal imax part is YES; anything
    # else unknown (never NO -- the forms are not canonical)
    case 1n+p LNmx{xs, y1, r1} LNmx{ys, y2, r2}:
      +pf = p
      +px = strip_zero(xs)
      +py = strip_zero(ys)
      pick_tri(atoms_sub(px, py) && atoms_sub(py, px)
               && tri_is_yes(ln_cmp_f(pf, y1, y2))
               && tri_is_yes(ln_cmp_f(pf, r1, r2)), TYes{}, TUnk{})
    case 1n+p LNmx{xs, y1, r1} LNimax{x2, y2, o2}:
      +pf = p
      ln_cmp_f(pf, a, LNmx{Nil{}, b, LNmax{Nil{}}})
    case 1n+p LNimax{x1, y1, o1} LNmx{ys, y2, r2}:
      +pf = p
      ln_cmp_f(pf, LNmx{Nil{}, a, LNmax{Nil{}}}, b)
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
    # max with a positive atom is positive; otherwise the imax part decides
    case LNmx{xs, y, r}:
      pick_tri(some_positive(xs), TNo{}, TUnk{})
    case _:
      TUnk{}

# --- substituting a declaration's level parameters -----------------------
# A `const` carries one level argument per parameter of the declaration it
# names, and the declaration's type is read under that substitution.
def find_pos_go(ps: List<&2, U32>, +v: U32, +hit: Bool, +i: U32,
                +miss: U32) -> U32:
  match ps hit:
    case _ True{}:
      (i - 1 : U32)
    case Nil{} False{}:
      miss
    case Con{head, tail} False{}:
      find_pos_go(tail, v, U32.is_eq(head, v), (i + 1 : U32), miss)

def find_pos(+v: U32, ps: List<&2, U32>, +i: U32, +miss: U32) -> U32:
  find_pos_go(ps, v, False{}, i, miss)

def nth_ln_go(qs: List<&2, LN>, +stop: Bool, +i: U32) -> LN:
  match qs stop:
    case Nil{} _:
      LNun{}
    case Con{head, tail} True{}:
      head
    case Con{head, tail} False{}:
      nth_ln_go(tail, U32.is_eq(i, 1), (i - 1 : U32))

def nth_ln(qs: List<&2, LN>, +i: U32) -> LN:
  nth_ln_go(qs, U32.is_eq(i, 0), i)

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
    case 1n+p LNmx{xs, y, r}:
      +pf = p
      ln_max(ln_max(ln_subst_go(xs, ps, qs, ln_zero()),
                    ln_subst_f(pf, y, ps, qs)),
             ln_subst_f(pf, r, ps, qs))
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
