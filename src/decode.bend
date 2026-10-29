# Record decoder: turns each NDJSON line into its integer fields.
#
# Integer fields are attributed to the key they belong to, not read
# positionally. Keys are *usually* serialised in alphabetical order, but not
# always: 26 of the 446,351 records in the small corpus write a binder as
# name, type, body, binderInfo instead of binderInfo, body, name, type. A
# positional reader silently swaps a binder's name and body on those, which
# is the kind of defect that surfaces as a wrong verdict much later.
#
# The two accumulators are complementary, which is why they are separate
# functions rather than one: a digit inside a string is excluded from the
# number path (it needs `not in a string`) and so lands in the string path --
# exactly right for `natVal`, whose value is a decimal string that can exceed
# 2^64 and so cannot be a machine integer in a language with no U64.

import Base
import ./scan.bend as S

# A decoded field: the hash of the key it came from, its value, and the
# ordinal of the object it sits in. The ordinal matters for `inductive`
# records, which nest arrays of objects that all repeat the same keys, so a
# key alone does not identify a field.
# A bare `U32 & U32` would be affine (`&` defaults to &1), and the
# accumulator has to be reusable.
type Fld is Data:
  Fld{g: U32, v: U32, ob: U32}

# ix     the record's index value
# cur    integer being read
# innum  mid-integer
# flds   (key signature, value) pairs, newest first
# sb     payload string bytes, newest first
# b1 b2  first two bytes of binderInfo: de default, im implicit,
#        in instImplicit, st strictImplicit
type Acc is Data:
  Acc{
    ix: U32,
    cur: U32,
    innum: Bool,
    flds: List<&2, Fld>,
    sb: List<&2, U32>,
    b1: U32,
    b2: U32,
  }

def Acc.start() -> Acc:
  Acc{0, 0, False{}, Nil{}, Nil{}, 0, 0}

def is_digit(+c: U32) -> Bool:
  U32.is_ge(c, 48) && U32.is_le(c, 57)

# Keys whose value is the record's payload string. `strVal` and `struct` pack
# to the same signature, but `struct` is integer-valued, so the string path
# never fires on it.
def is_strkey(+g: U32) -> Bool:
  U32.is_eq(g, 114225) || U32.is_eq(g, 3242329664) || U32.is_eq(g, 3402962736)

# JSON simple escapes. `\"`, `\\` and `\/` denote themselves and fall
# through. `\uXXXX` is not implemented: it needs hex parsing and UTF-8
# re-encoding, and it occurs nowhere in init, std, cedar or mathlib -- the
# only escapes those use are \" \\ \n \r.
def unescape(+c: U32) -> U32:
  S.pick(U32.is_eq(c, 110), 10,
    S.pick(U32.is_eq(c, 116), 9,
      S.pick(U32.is_eq(c, 114), 13,
        S.pick(U32.is_eq(c, 98), 8,
          S.pick(U32.is_eq(c, 102), 12, c)))))

def num_step(+dig: Bool, +isix: Bool, +ch: U32, +g: U32, +ob: U32, acc: Acc) -> Acc:
  match dig isix acc:
    case True{} _ Acc{ix, cur, innum, flds, sb, b1, b2}:
      Acc{ix, ((cur * 10 : U32) + (ch - 48 : U32) : U32), True{}, flds, sb, b1, b2}
    case False{} True{} Acc{ix, cur, True{}, flds, sb, b1, b2}:
      Acc{cur, 0, False{}, flds, sb, b1, b2}
    case False{} False{} Acc{ix, cur, True{}, flds, sb, b1, b2}:
      Acc{ix, 0, False{}, Con{Fld{g, cur, ob}, flds}, sb, b1, b2}
    case False{} _ Acc{ix, cur, False{}, flds, sb, b1, b2}:
      Acc{ix, cur, False{}, flds, sb, b1, b2}

# A boolean value, recorded as 1 or 0 under its own key.
#
# The format writes `true`/`false` bare, and the scanner's number path only
# accumulates digits, so these were being dropped. `k` on a recursor is one
# of them, and it is a claim the kernel has to check: an export may assert
# that a recursor reduces K-like when its inductive does not qualify.
#
# Only the FIRST byte is acted on -- `t` or `f` in value position, outside
# any string or key. No other value in this format begins with either: the
# string-valued fields (`binderInfo`, `safety`, `hints`, `kind`) are quoted,
# so `instr` excludes them.
def bool_step(+cap: Bool, +ch: U32, +g: U32, +ob: U32, acc: Acc) -> Acc:
  match cap acc:
    case True{} Acc{ix, cur, innum, flds, sb, b1, b2}:
      Acc{ix, cur, innum,
          Con{Fld{g, S.pick(U32.is_eq(ch, 116), 1, 0), ob}, flds}, sb,
          b1, b2}
    case False{} Acc{ix, cur, innum, flds, sb, b1, b2}:
      Acc{ix, cur, innum, flds, sb, b1, b2}

def str_step(+cap: Bool, +ch: U32, acc: Acc) -> Acc:
  match cap acc:
    case True{} Acc{ix, cur, innum, flds, sb, b1, b2}:
      Acc{ix, cur, innum, flds, Con{ch, sb}, b1, b2}
    case False{} Acc{ix, cur, innum, flds, sb, b1, b2}:
      Acc{ix, cur, innum, flds, sb, b1, b2}

def bi_step(+cap: Bool, +ch: U32, acc: Acc) -> Acc:
  match cap acc:
    case True{} Acc{ix, cur, innum, flds, sb, b1, b2}:
      +p1 = b1
      +p2 = b2
      +c = ch
      +fresh = U32.is_eq(p1, 0)
      Acc{ix, cur, innum, flds, sb,
          S.pick(fresh, c, p1),
          S.pick(fresh, p2, S.pick(U32.is_eq(p2, 0), c, p2))}
    case False{} Acc{ix, cur, innum, flds, sb, b1, b2}:
      Acc{ix, cur, innum, flds, sb, b1, b2}

# `before` is the lexical state as it was when `ch` was read, so "inside a
# string" and "in value position" describe this byte rather than the next.
def accumulate(+ch: U32, +before: S.Sc, acc: Acc) -> Acc:
  +instr = S.Sc.instr(before)
  +inkey = S.Sc.inkey(before)
  +g = S.Sc.key(before)
  # Not gated on value position: no key in this format contains a digit, and
  # digits inside a string are excluded by `not instr` and belong to the
  # string path instead.
  +numeric = is_digit(ch) && Bool.not(instr) && Bool.not(inkey)
  # `esc` is the flag as it stood before this byte, so esc = True means this
  # byte is the escaped character itself.
  +esc = S.Sc.esc(before)
  +special = U32.is_eq(ch, 34) || U32.is_eq(ch, 92)
  # A byte belongs to the payload when inside a string and it is neither the
  # unescaped closing quote nor the backslash that introduces an escape.
  +body = instr && (esc || Bool.not(special))
  +out = S.pick(esc, unescape(ch), ch)
  +isbool = (U32.is_eq(ch, 116) || U32.is_eq(ch, 102))
            && Bool.not(instr) && Bool.not(inkey) && S.Sc.inval(before)
  bi_step(body && U32.is_eq(g, 1403128184), out,
          str_step(body && is_strkey(g), out,
                   bool_step(isbool, ch, g, S.Sc.obj(before),
                             num_step(numeric, S.is_index_sig(g), ch, g,
                                      S.Sc.obj(before), acc))))

# One decoded record. `flds` holds (key signature, value) pairs in
# serialisation order, so a field is read by its key rather than its position.
type Rec is Data:
  Rec{
    kind: U32,
    ix: U32,
    flds: List<&2, Fld>,
    b1: U32,
    b2: U32,
    sb: List<&2, U32>,
  }
  # an expression record of fixed arity (bvar, sort, app, lam, forallE,
  # letE, proj) with its fields in place: a..d in T.mk_exk's order. 27.7M
  # navier-stokes records as field lists were 7 GB per worker
  RecK{kind: U32, ix: U32, b1: U32, b2: U32, a: U32, b: U32, c: U32, d: U32}

def rev_u32(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      rev_u32(tail, Con{head, acc})

def rev_pair(xs: List<&2, Fld>, acc: List<&2, Fld>) -> List<&2, Fld>:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      rev_pair(tail, Con{head, acc})

def d_fld(xs: List<&2, Fld>, +g: U32, +dflt: U32) -> U32:
  match xs:
    case Nil{}:
      dflt
    case Con{Fld{fg, fv, fo}, tail}:
      d_fld(tail, g, S.pick(U32.is_eq(fg, g), fv, dflt))

def is_k_kind(+k: U32) -> Bool:
  U32.is_eq(k, 3036037) || U32.is_eq(k, 3536286) || U32.is_eq(k, 96801)
  || U32.is_eq(k, 106904) || U32.is_eq(k, 3617176333)
  || U32.is_eq(k, 3318154) || U32.is_eq(k, 3449693)

# the field keys of a..d per kind (see T.mk_exk)
def kg1(+k: U32) -> U32:
  S.pick(U32.is_eq(k, 3036037), 3036037,
         S.pick(U32.is_eq(k, 3536286), 3536286,
                S.pick(U32.is_eq(k, 96801), 3272,
                       S.pick(U32.is_eq(k, 3449693), 3618459877, 3373707))))

def kg2(+k: U32) -> U32:
  S.pick(U32.is_eq(k, 96801), 96854,
         S.pick(U32.is_eq(k, 3449693), 104125, 3575610))

def kg3(+k: U32) -> U32:
  S.pick(U32.is_eq(k, 3449693), 3402992597,
         S.pick(U32.is_eq(k, 3318154), 111972721, 3029410))

def kg4(+k: U32) -> U32:
  S.pick(U32.is_eq(k, 3318154), 3029410, 0)

def mk_rec2(+fixed: Bool, +kind: U32, +ix: U32, flds: List<&2, Fld>,
            sb: List<&2, U32>, +b1: U32, +b2: U32) -> Rec:
  match fixed:
    case True{}:
      +f : List<&2, Fld> = flds
      RecK{kind, ix, b1, b2, d_fld(f, kg1(kind), 0), d_fld(f, kg2(kind), 0),
           d_fld(f, kg3(kind), 0), d_fld(f, kg4(kind), 0)}
    case False{}:
      Rec{kind, ix, rev_pair(flds, Nil{}), b1, b2, rev_u32(sb, Nil{})}

def mk_rec(+kind: U32, acc: Acc) -> Rec:
  match acc:
    case Acc{ix, cur, innum, flds, sb, b1, b2}:
      mk_rec2(is_k_kind(kind), kind, ix, flds, sb, b1, b2)

# Every record ends with `}` before its newline, and `}` is a non-digit, so
# the pending integer is already flushed by the time the newline arrives.
def next_acc(+nl: Bool, +ch: U32, +before: S.Sc, +acc: Acc) -> Acc:
  match nl:
    case True{}:
      Acc.start()
    case False{}:
      accumulate(ch, before, acc)

def next_recs(+nl: Bool, +st: S.Sc, +acc: Acc, out: List<&2, Rec>) -> List<&2, Rec>:
  match nl:
    case True{}:
      Con{mk_rec(S.Sc.kind(st), acc), out}
    case False{}:
      out

# Emits one Rec per line, newest first.
def decode(bs: List<&2, U32>, +st: S.Sc, +acc: Acc, out: List<&2, Rec>) -> List<&2, Rec>:
  match bs:
    case Nil{}:
      out
    case Con{head, tail}:
      +ch = head
      +nl = U32.is_eq(ch, 10)
      +stt = st
      +a = acc
      decode(tail, S.next_state(nl, ch, stt), next_acc(nl, ch, stt, a),
             next_recs(nl, stt, a, out))

def Rec.kind(+r: Rec) -> U32:
  match r:
    case Rec{kind, ix, flds, b1, b2, sb}:
      kind
    case RecK{kind, ix, b1, b2, a, b, c, d}:
      kind

def Rec.ix(+r: Rec) -> U32:
  match r:
    case Rec{kind, ix, flds, b1, b2, sb}:
      ix
    case RecK{kind, ix, b1, b2, a, b, c, d}:
      ix

# Streaming variant of `decode`: consumes one chunk and returns the carried
# scanner/accumulator state alongside the records so far, so the next chunk
# resumes exactly where this one stopped. Threaded in file order, so the final
# `out` is identical to a single-shot `decode` over the whole file.
def decode_resume(bs: List<&2, U32>, +st: S.Sc, +acc: Acc,
                  out: List<&2, Rec>) -> S.Sc & Acc & List<&2, Rec>:
  match bs:
    case Nil{}:
      Tuple{st, Tuple{acc, out}}
    case Con{head, tail}:
      +ch = head
      +nl = U32.is_eq(ch, 10)
      +stt = st
      +a = acc
      decode_resume(tail, S.next_state(nl, ch, stt), next_acc(nl, ch, stt, a),
                    next_recs(nl, stt, a, out))
