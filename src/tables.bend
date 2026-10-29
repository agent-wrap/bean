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

# The node is built and inserted only for a record of the right kind (a
# Bool match: arguments are strict, so `R.sub(kind_ok, R.set(..), t)` paid
# an insertion for every record of the export)
def ex_step(+go: Bool, +t: R.Tr<T.Ex>, +ix: U32, +k: U32, +b: U32,
            +flds: List<&2, D.Fld>, +sb: List<&2, U32>) -> R.Tr<T.Ex>:
  match go:
    case True{}:
      R.set(T.Ex, 64n, t, ix, T.mk_ex(k, b, flds, sb), T.EBad{})
    case False{}:
      t

def build_ex(rs: List<&2, D.Rec>, +t: R.Tr<T.Ex>) -> R.Tr<T.Ex>:
  match rs:
    case Nil{}:
      t
    case Con{head, tail}:
      match head:
        case D.Rec{kind, ix, flds, b1, b2, sb}:
          +k = kind
          build_ex(tail,
            ex_step(K.is_ex_kind(k), t, ix, k, ((b1 * 256 : U32) + b2 : U32),
                    flds, sb))
        case D.RecK{kind, ix, b1, b2, ka, kb, kc, kd}:
          build_ex(tail,
            R.set(T.Ex, 64n, t, ix,
                  T.mk_exk(kind, ((b1 * 256 : U32) + b2 : U32), ka, kb, kc, kd),
                  T.EBad{}))

def lv_step(+go: Bool, +t: R.Tr<T.Lvl>, +ix: U32, +k: U32,
            +flds: List<&2, D.Fld>) -> R.Tr<T.Lvl>:
  match go:
    case True{}:
      R.set(T.Lvl, 64n, t, ix, T.mk_lvl(k, flds), T.LZero{})
    case False{}:
      t

def build_lv(rs: List<&2, D.Rec>, +t: R.Tr<T.Lvl>) -> R.Tr<T.Lvl>:
  match rs:
    case Nil{}:
      t
    case Con{head, tail}:
      match head:
        case D.Rec{kind, ix, flds, b1, b2, sb}:
          +k = kind
          build_lv(tail, lv_step(K.is_lvl_kind(k), t, ix, k, flds))
        case D.RecK{kind, ix, b1, b2, ka, kb, kc, kd}:
          build_lv(tail, t)

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
        R.set_if(U32, U32.is_gt(nm, 0), t, nm, ty, 4294967295))

def build_lp(ds: List<&2, K.Dcl>, +t: R.Tr<List<&2, U32>>) -> R.Tr<List<&2, U32>>:
  match ds:
    case Nil{}:
      t
    case Con{head, tail}:
      +h = head
      +nm = K.dcl_name(h)
      build_lp(tail,
        R.set_if(List<&2, U32>, U32.is_gt(nm, 0), t, nm, K.dcl_lparams(h), Nil{}))

# Only `def` values are unfoldable. Theorem bodies are opaque in recent Lean,
# and an `opaque` declaration is opaque by construction, so neither goes in.
def build_vt(ds: List<&2, K.Dcl>, +t: R.Tr<U32>) -> R.Tr<U32>:
  match ds:
    case Nil{}:
      t
    case Con{head, tail}:
      match head:
        case K.DDef{n, lps, ty, v}:
          build_vt(tail, R.set(U32, 64n, t, n, v, 4294967295))
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
        R.set_if(U32, U32.is_gt(nm, 0), t, nm, item_type(h), 4294967295))

def add_items_lp(items: List<&2, K.IItem>,
                 +t: R.Tr<List<&2, U32>>) -> R.Tr<List<&2, U32>>:
  match items:
    case Nil{}:
      t
    case Con{head, tail}:
      +h = head
      +nm = item_name(h)
      add_items_lp(tail,
        R.set_if(List<&2, U32>, U32.is_gt(nm, 0), t, nm, item_lps(h), Nil{}))

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
      R.set_if(U32, U32.is_gt(nm, 0), t, nm, K.dcl_type(d), 4294967295)

def add_lp(+d: K.Dcl, +t: R.Tr<List<&2, U32>>) -> R.Tr<List<&2, U32>>:
  match d:
    case K.DInd{nms, items}:
      add_items_lp(items, t)
    case _:
      +nm = K.dcl_name(d)
      R.set_if(List<&2, U32>, U32.is_gt(nm, 0), t, nm, K.dcl_lparams(d), Nil{})

# a constant's value for delta: definitions, and theorems -- Lean 4's
# is_delta takes any constant with has_value(), so an iota major
# `thm a b : And p q` unfolds to `And.intro ..` (cslib's
# Rat.instEncodable._proof_3). A theorem's value is kept under n + 2^31 and
# read ONLY by iota on a major premise (km WIth): unfolding proofs in delta,
# projections or the lazy loop made std run past 44 min and turned two
# rejects of the bugs/ suite (proj-/rec-of-subst-prop) into declines
def add_vt(+d: K.Dcl, +t: R.Tr<U32>) -> R.Tr<U32>:
  match d:
    case K.DDef{n, lps, ty, v}:
      R.set(U32, 64n, t, n, v, 4294967295)
    case K.DThm{n, lps, ty, v}:
      R.set(U32, 64n, t, (n + 2147483648 : U32), v, 4294967295)
    case _:
      t

# --- level normal forms, order-independently -----------------------------
# References may point forward (`other/level-index-out-of-order` declares
# il 1 = succ 2 before il 2), so this is a bounded fixpoint: an unresolved
# child propagates as LNun and a later round fills it in.
# A resolved level is left alone (no trie write: every R.set copies a path
# and drops the old one -- term_drop dominated init's 60 s load with 32
# full passes over its levels), and the passes stop once one of them
# leaves nothing unresolved: an in-order export resolves in one pass.
def lv_one2(+known: Bool, +i: U32, +lv: R.Tr<T.Lvl>,
            +ln: R.Tr<L.LN>) -> R.Tr<L.LN> & U32:
  match known:
    case True{}:
      (ln, 0)
    case False{}:
      +l = R.get(T.Lvl, 64n, lv, i, T.LZero{})
      +v : L.LN = L.combine(L.op_of(l), L.c1_of(l),
                            R.get(L.LN, 64n, ln, L.c1_of(l), L.LNun{}),
                            R.get(L.LN, 64n, ln, L.c2_of(l), L.LNun{}))
      +v2 : L.LN = v
      +un : Bool = L.is_un(v2)
      (R.set_if(L.LN, Bool.not(un), ln, i, v2, L.LNun{}), S.pick(un, 1, 0))

def lv_one(+i: U32, +lv: R.Tr<T.Lvl>, +ln: R.Tr<L.LN>) -> R.Tr<L.LN> & U32:
  +ln2 : R.Tr<L.LN> = ln
  lv_one2(Bool.not(L.is_un(R.get(L.LN, 64n, ln2, i, L.LNun{}))), i, lv, ln2)

def lv_acc(+pend: U32, r: R.Tr<L.LN> & U32) -> R.Tr<L.LN> & U32:
  match r:
    case Tuple{ln, u}:
      (ln, (pend + u : U32))

def lv_pass(n: Nat, +i: U32, +lv: R.Tr<T.Lvl>,
            st: R.Tr<L.LN> & U32) -> R.Tr<L.LN> & U32:
  match n st:
    case 0n _:
      st
    case 1n+p Tuple{ln, pend}:
      lv_pass(p, (i + 1 : U32), lv, lv_acc(pend, lv_one(i, lv, ln)))

def lv_pass_if(+go: Bool, +n: Nat, +lv: R.Tr<T.Lvl>,
               st: R.Tr<L.LN> & U32) -> R.Tr<L.LN> & U32:
  match go:
    case True{}:
      lv_pass(n, 0, lv, st)
    case False{}:
      st

# state: the table and the count of levels still unresolved after the
# last pass (1 before any pass)
def lv_resolve_s(rounds: Nat, +n: Nat, +lv: R.Tr<T.Lvl>,
                 st: R.Tr<L.LN> & U32) -> R.Tr<L.LN>:
  match rounds st:
    case 0n Tuple{ln, pend}:
      ln
    case 1n+p Tuple{ln, pend}:
      +go : Bool = U32.is_ne(pend, 0)
      lv_resolve_s(p, n, lv, lv_pass_if(go, n, lv, (ln, S.pick(go, 0, 0))))

def lv_resolve(rounds: Nat, +n: Nat, +lv: R.Tr<T.Lvl>,
               +ln: R.Tr<L.LN>) -> R.Tr<L.LN>:
  lv_resolve_s(rounds, n, lv, (ln, 1))

