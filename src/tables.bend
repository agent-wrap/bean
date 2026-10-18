# The term tables, as reusable tries rather than Arrays.
#
# Arrays are faster to index but are `Type`, so each read hands the array back
# and nothing can read one twice without threading it through a helper -- and
# Bend forbids that helper calling back. Tries are `Data`, so the kernel's
# functions can read them freely and stay ordinary recursive functions. That
# trade buys back the entire shape of the kernel for a logarithmic lookup.
#
# It also removes two hazards the Array path had: index wrapping, and having
# to compute a safe table depth from the data.

import Base
import ./scan.bend as S
import ./decode.bend as D
import ./term.bend as T
import ./level.bend as L
import ./store.bend as K
import ./trie.bend as R

def build_ex(rs: List<&2, D.Rec>, +t: R.Tr<T.Ex>) -> R.Tr<T.Ex>:
  match rs:
    case Nil{}:
      t
    case Con{head, tail}:
      match head:
        case D.Rec{kind, ix, flds, b1, b2, sb}:
          +k = kind
          build_ex(tail,
            R.sub(T.Ex, K.is_ex_kind(k),
                  R.set(T.Ex, 64n, t, ix,
                        T.mk_ex(k, ((b1 * 256 : U32) + b2 : U32), flds, sb),
                        T.EBad{}),
                  t))

def build_lv(rs: List<&2, D.Rec>, +t: R.Tr<T.Lvl>) -> R.Tr<T.Lvl>:
  match rs:
    case Nil{}:
      t
    case Con{head, tail}:
      match head:
        case D.Rec{kind, ix, flds, b1, b2, sb}:
          +k = kind
          build_lv(tail,
            R.sub(T.Lvl, K.is_lvl_kind(k),
                  R.set(T.Lvl, 32n, t, ix, T.mk_lvl(k, flds), T.LZero{}),
                  t))

# Name index 0 is `Name.anonymous` and level index 0 is `Level.zero`; neither
# is ever emitted, and the tries' defaults supply them.
def build_nt(ds: List<&2, K.Dcl>, +t: R.Tr<U32>) -> R.Tr<U32>:
  match ds:
    case Nil{}:
      t
    case Con{head, tail}:
      +h = head
      +nm = K.dcl_name(h)
      +ty = K.dcl_type(h)
      build_nt(tail,
        R.sub(U32, U32.is_gt(nm, 0),
              R.set(U32, 32n, t, nm, ty, 4294967295), t))

def build_lp(ds: List<&2, K.Dcl>, +t: R.Tr<List<&2, U32>>) -> R.Tr<List<&2, U32>>:
  match ds:
    case Nil{}:
      t
    case Con{head, tail}:
      +h = head
      +nm = K.dcl_name(h)
      build_lp(tail,
        R.sub(List<&2, U32>, U32.is_gt(nm, 0),
              R.set(List<&2, U32>, 32n, t, nm, K.dcl_lparams(h), Nil{}),
              t))

# Only `def` values are unfoldable. Theorem bodies are opaque in recent Lean,
# and an `opaque` declaration is opaque by construction, so neither goes in.
def build_vt(ds: List<&2, K.Dcl>, +t: R.Tr<U32>) -> R.Tr<U32>:
  match ds:
    case Nil{}:
      t
    case Con{head, tail}:
      match head:
        case K.DDef{n, lps, ty, v}:
          build_vt(tail, R.set(U32, 32n, t, n, v, 4294967295))
        case _:
          build_vt(tail, t)

# An inductive block introduces its types, constructors and recursors into
# the environment. The recursor type comes from the export, which is only
# safe because a block whose recursor cannot be derived and matched makes the
# whole file decline -- so a trusted type can never contribute to an accept.
def item_name(+it: K.IItem) -> U32:
  match it:
    case K.IInd{nm, lps, ty, np, ni, nn, cs}:
      nm
    case K.ICtor{nm, lps, ty, ind, np, nf, ci}:
      nm
    case K.IRec{nm, lps, ty, np, ni, nmo, kf}:
      nm
    case _:
      0

def item_type(+it: K.IItem) -> U32:
  match it:
    case K.IInd{nm, lps, ty, np, ni, nn, cs}:
      ty
    case K.ICtor{nm, lps, ty, ind, np, nf, ci}:
      ty
    case K.IRec{nm, lps, ty, np, ni, nmo, kf}:
      ty
    case _:
      4294967295

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

def add_items_nt(items: List<&2, K.IItem>, +t: R.Tr<U32>) -> R.Tr<U32>:
  match items:
    case Nil{}:
      t
    case Con{head, tail}:
      +h = head
      +nm = item_name(h)
      add_items_nt(tail,
        R.sub(U32, U32.is_gt(nm, 0),
              R.set(U32, 32n, t, nm, item_type(h), 4294967295), t))

def add_items_lp(items: List<&2, K.IItem>,
                 +t: R.Tr<List<&2, U32>>) -> R.Tr<List<&2, U32>>:
  match items:
    case Nil{}:
      t
    case Con{head, tail}:
      +h = head
      +nm = item_name(h)
      add_items_lp(tail,
        R.sub(List<&2, U32>, U32.is_gt(nm, 0),
              R.set(List<&2, U32>, 32n, t, nm, item_lps(h), Nil{}), t))

# --- adding one declaration to the environment --------------------------
# A declaration is only in scope for the ones AFTER it. Building the tables
# from every declaration at once let `tutorial/014_selfProof` -- a theorem
# whose proof names itself -- resolve its own name and be accepted. These
# add one declaration, and the checker extends the environment only after
# checking it.
def add_nt(+d: K.Dcl, +t: R.Tr<U32>) -> R.Tr<U32>:
  match d:
    case K.DInd{nms, items}:
      add_items_nt(items, t)
    case _:
      +nm = K.dcl_name(d)
      R.sub(U32, U32.is_gt(nm, 0),
            R.set(U32, 32n, t, nm, K.dcl_type(d), 4294967295), t)

def add_lp(+d: K.Dcl, +t: R.Tr<List<&2, U32>>) -> R.Tr<List<&2, U32>>:
  match d:
    case K.DInd{nms, items}:
      add_items_lp(items, t)
    case _:
      +nm = K.dcl_name(d)
      R.sub(List<&2, U32>, U32.is_gt(nm, 0),
            R.set(List<&2, U32>, 32n, t, nm, K.dcl_lparams(d), Nil{}), t)

def add_vt(+d: K.Dcl, +t: R.Tr<U32>) -> R.Tr<U32>:
  match d:
    case K.DDef{n, lps, ty, v}:
      R.set(U32, 32n, t, n, v, 4294967295)
    case _:
      t

# --- level normal forms, order-independently -----------------------------
# References may point forward (`other/level-index-out-of-order` declares
# il 1 = succ 2 before il 2), so this is a bounded fixpoint: an unresolved
# child propagates as LNun and a later round fills it in.
def lv_one(+i: U32, +lv: R.Tr<T.Lvl>, +ln: R.Tr<L.LN>) -> R.Tr<L.LN>:
  +l = R.get(T.Lvl, 32n, lv, i, T.LZero{})
  +old = R.get(L.LN, 32n, ln, i, L.LNun{})
  +v = L.combine(L.op_of(l), L.c1_of(l),
                 R.get(L.LN, 32n, ln, L.c1_of(l), L.LNun{}),
                 R.get(L.LN, 32n, ln, L.c2_of(l), L.LNun{}))
  R.set(L.LN, 32n, ln, i, L.pick_ln(L.is_un(old), v, old), L.LNun{})

def lv_pass(n: Nat, +i: U32, +lv: R.Tr<T.Lvl>, +ln: R.Tr<L.LN>) -> R.Tr<L.LN>:
  match n:
    case 0n:
      ln
    case 1n+p:
      lv_pass(p, (i + 1 : U32), lv, lv_one(i, lv, ln))

def lv_resolve(rounds: Nat, +n: Nat, +lv: R.Tr<T.Lvl>,
               +ln: R.Tr<L.LN>) -> R.Tr<L.LN>:
  match rounds:
    case 0n:
      ln
    case 1n+p:
      lv_resolve(p, n, lv, lv_pass(n, 0, lv, ln))
