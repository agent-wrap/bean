# Flat, Array-backed term stores -- the port's M1 (docs/port-plan.md).
#
# Same contents as the trie builders in tables.bend, held in Bend's Array,
# which bench/array.bend shows is a flat in-place buffer at runtime
# (~1 ns/access) rather than the O(log n) graph walk the trie pays. Array is
# `Type` (one owner), so every builder threads it linearly, and every read
# below passes its (array & value) pair back in through a parameter.
#
# Sizing: Array indexes WRAP (bend-notes.md), so each table is sized from
# its own kind's maximum index -- never from max_any_ix, whose hygiene
# counters reach 4.2e9 and would demand an impossible depth.

import Base
import ./scan.bend as S
import ./decode.bend as D
import ./term.bend as T
import ./level.bend as L
import ./store.bend as K
import ./trie.bend as R

# Smallest depth whose 2^depth strictly exceeds mx (so index mx fits).
def fdepth(+mx: U32) -> Nat:
  Nat.add(U32.log2(U32.max(mx, 1)), 1n)

def max_nm_ix(rs: List<&2, D.Rec>, +acc: U32) -> U32:
  match rs:
    case Nil{}:
      acc
    case Con{head, tail}:
      +h = head
      +i = D.Rec.ix(h)
      max_nm_ix(tail,
                S.pick(K.is_nm_kind(D.Rec.kind(h)) && U32.is_gt(i, acc),
                       i, acc))

# --- builders -------------------------------------------------------------
def fset_ex(z: Bool, +ix: U32, +v: T.Ex, a: Array<T.Ex>) -> Array<T.Ex>:
  match z:
    case True{}:
      Array.set(T.Ex, a, ix, v)
    case False{}:
      a

def fb_ex(rs: List<&2, D.Rec>, a: Array<T.Ex>) -> Array<T.Ex>:
  match rs:
    case Nil{}:
      a
    case Con{head, tail}:
      match head:
        # (the debug mains' path: a list's handle names no table entry --
        # fmain routes the records through fb_route instead)
        case D.Rec{kind, ix, flds, b1, b2, sb}:
          +k = kind
          +i2 : U32 = ix
          fb_ex(tail,
                fset_ex(K.is_ex_kind(k), i2,
                        T.mk_ex(k, ((b1 * 256 : U32) + b2 : U32), flds,
                                T.xhandle(i2)),
                        a))
        case D.RecK{kind, ix, b1, b2, ka, kb, kc, kd}:
          fb_ex(tail, Array.set(T.Ex, a, ix,
                                T.mk_exk(kind, ((b1 * 256 : U32) + b2 : U32),
                                         ka, kb, kc, kd)))

def fset_lv(z: Bool, +ix: U32, +v: T.Lvl, a: Array<T.Lvl>) -> Array<T.Lvl>:
  match z:
    case True{}:
      Array.set(T.Lvl, a, ix, v)
    case False{}:
      a

def fb_lv(rs: List<&2, D.Rec>, a: Array<T.Lvl>) -> Array<T.Lvl>:
  match rs:
    case Nil{}:
      a
    case Con{head, tail}:
      match head:
        case D.Rec{kind, ix, flds, b1, b2, sb}:
          +k = kind
          fb_lv(tail, fset_lv(K.is_lvl_kind(k), ix, T.mk_lvl(k, flds), a))
        case D.RecK{kind, ix, b1, b2, ka, kb, kc, kd}:
          fb_lv(tail, a)

def fset_nm(z: Bool, +ix: U32, +v: T.Nm, a: Array<T.Nm>) -> Array<T.Nm>:
  match z:
    case True{}:
      Array.set(T.Nm, a, ix, v)
    case False{}:
      a

def fb_nm(rs: List<&2, D.Rec>, a: Array<T.Nm>) -> Array<T.Nm>:
  match rs:
    case Nil{}:
      a
    case Con{head, tail}:
      match head:
        case D.Rec{kind, ix, flds, b1, b2, sb}:
          +k = kind
          fb_nm(tail, fset_nm(K.is_nm_kind(k), ix, T.mk_nm(k, flds, sb), a))
        case D.RecK{kind, ix, b1, b2, ka, kb, kc, kd}:
          fb_nm(tail, a)

# --- level normal forms, flat --------------------------------------------
# The same bounded fixpoint as tables.bend's lv_resolve, over Arrays. The
# read chain for one index is a pipeline of defs, each consuming the
# previous Array op's (array & value) pair as a parameter; callers sit
# BELOW their callees because live code may only call upward.

# last step: ln[i] := pick(is_un(old), combine(...), old)
def flv_d(r: Array<L.LN> & L.LN, +op: U32, +c1: U32, +c1v: L.LN,
          +c2v: L.LN, +i: U32,
          lv: Array<T.Lvl>) -> Array<T.Lvl> & Array<L.LN>:
  match r:
    case Tuple{ln, old}:
      +o = old
      (lv, Array.set(L.LN, ln, i,
                     L.pick_ln(L.is_un(o), L.combine(op, c1, c1v, c2v), o)))

# read ln[i] (the old value)
def flv_c(r: Array<L.LN> & L.LN, +op: U32, +c1: U32, +c1v: L.LN,
          +i: U32, lv: Array<T.Lvl>) -> Array<T.Lvl> & Array<L.LN>:
  match r:
    case Tuple{ln, c2v}:
      flv_d(Array.get(L.LN, ln, i), op, c1, c1v, c2v, i, lv)

# read ln[c2]
def flv_b(r: Array<L.LN> & L.LN, +op: U32, +c1: U32, +c2: U32,
          +i: U32, lv: Array<T.Lvl>) -> Array<T.Lvl> & Array<L.LN>:
  match r:
    case Tuple{ln, c1v}:
      flv_c(Array.get(L.LN, ln, c2), op, c1, c1v, i, lv)

# read ln[c1]; the level node is reusable here so its parts can fan out
def flv_a2(+l: T.Lvl, +i: U32, lv: Array<T.Lvl>,
           ln: Array<L.LN>) -> Array<T.Lvl> & Array<L.LN>:
  flv_b(Array.get(L.LN, ln, L.c1_of(l)), L.op_of(l), L.c1_of(l),
        L.c2_of(l), i, lv)

# read lv[i]
def flv_a(r: Array<T.Lvl> & T.Lvl, +i: U32,
          ln: Array<L.LN>) -> Array<T.Lvl> & Array<L.LN>:
  match r:
    case Tuple{lv, l}:
      flv_a2(l, i, lv, ln)

def flv_one(+i: U32, st: Array<T.Lvl> & Array<L.LN>)
    -> Array<T.Lvl> & Array<L.LN>:
  match st:
    case Tuple{lv, ln}:
      flv_a(Array.get(T.Lvl, lv, i), i, ln)

def flv_pass(n: Nat, +i: U32, st: Array<T.Lvl> & Array<L.LN>)
    -> Array<T.Lvl> & Array<L.LN>:
  match n:
    case 0n:
      st
    case 1n+p:
      flv_pass(p, (i + 1 : U32), flv_one(i, st))

def flv_resolve(rounds: Nat, +n: Nat, st: Array<T.Lvl> & Array<L.LN>)
    -> Array<T.Lvl> & Array<L.LN>:
  match rounds:
    case 0n:
      st
    case 1n+p:
      flv_resolve(p, n, flv_pass(n, 0, st))

# --- streaming the expressions straight into the store -------------------
# (fmain's nx path) An expression record is set into the flat store as its
# batch is decoded, and dropped; every other record is kept, in order. The
# list of decoded records was half a worker's peak (init: 2.5 of 4.9 GB) --
# the arena's runner has 16 GB. An index at or past the store's capacity is
# counted (Bend's array indexes wrap): the caller declines.
def rt_set(+ok: Bool, a: Array<T.Ex>, +ix: U32, +v: T.Ex) -> Array<T.Ex>:
  match ok:
    case True{}:
      Array.set(T.Ex, a, ix, v)
    case False{}:
      a

# the record's list interned (L.lst_in: the first equal list's handle, else
# this record's xhandle), so that an instantiated constant hash-conses onto
# the export's node
def rt_put(+ok: Bool, a: Array<T.Ex>, +i2: U32, +k: U32, +bi: U32,
           +flds: List<&2, D.Fld>, r: (R.Tr<L.LN> & U32) & Bool,
           +bd: U32) -> Array<T.Ex> & (U32 & R.Tr<L.LN>):
  match r:
    case Tuple{Tuple{lt, h}, nw}:
      (rt_set(ok, a, i2, T.mk_ex(k, bi, flds, h)),
       (S.pick(ok, bd, (bd + 1 : U32)), lt))

def rt_rec(+isx: Bool, +k: U32, +ix: U32, flds: List<&2, D.Fld>, +b1: U32,
           +b2: U32, sb: List<&2, U32>, st: (Array<T.Ex> & (U32 & R.Tr<L.LN>)) & List<&2, D.Rec>,
           +cap: U32) -> (Array<T.Ex> & (U32 & R.Tr<L.LN>)) & List<&2, D.Rec>:
  match isx st:
    case True{} Tuple{Tuple{a, Tuple{bad, lt}}, acc}:
      +i2 : U32 = ix
      +k2 : U32 = k
      +f2 : List<&2, D.Fld> = flds
      (rt_put(U32.is_lt(i2, cap), a, i2, k2, ((b1 * 256 : U32) + b2 : U32), f2,
              L.lst_in(lt, T.xhandle(i2), T.ex_list(k2, f2, sb)), bad), acc)
    case False{} Tuple{ab, acc}:
      (ab, Con{D.Rec{k, ix, flds, b1, b2, sb}, acc})

def rt_one(r: D.Rec, st: (Array<T.Ex> & (U32 & R.Tr<L.LN>)) & List<&2, D.Rec>,
           +cap: U32) -> (Array<T.Ex> & (U32 & R.Tr<L.LN>)) & List<&2, D.Rec>:
  match r st:
    case D.Rec{kind, ix, flds, b1, b2, sb} _:
      +k = kind
      rt_rec(K.is_ex_kind(k), k, ix, flds, b1, b2, sb, st, cap)
    case D.RecK{kind, ix, b1, b2, ka, kb, kc, kd} Tuple{Tuple{a, Tuple{bad, lt}}, acc}:
      +i2 : U32 = ix
      +bd : U32 = bad
      +ok : Bool = U32.is_lt(i2, cap)
      ((rt_set(ok, a, i2, T.mk_exk(kind, ((b1 * 256 : U32) + b2 : U32), ka, kb,
                                    kc, kd)),
        (S.pick(ok, bd, (bd + 1 : U32)), lt)), acc)

# kept records come out reversed (the caller reverses them)
def fb_route(rs: List<&2, D.Rec>, st: (Array<T.Ex> & (U32 & R.Tr<L.LN>)) & List<&2, D.Rec>,
             +cap: U32) -> (Array<T.Ex> & (U32 & R.Tr<L.LN>)) & List<&2, D.Rec>:
  match rs:
    case Nil{}:
      st
    case Con{head, tail}:
      fb_route(tail, rt_one(head, st, cap), cap)

def rev_recs(xs: List<&2, D.Rec>, acc: List<&2, D.Rec>) -> List<&2, D.Rec>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      rev_recs(t, Con{h, acc})
