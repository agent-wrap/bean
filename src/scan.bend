# Byte-level scanner for the lean4export NDJSON stream (format 3.1.0).
#
# Each line is one record. Its kind is the first top-level key that is not an
# index key (`in`, `ie`, `il`). A key is identified by the polynomial hash
# h = h*31 + byte over its bytes, which tools/keycodes.json confirms is
# collision-free across all 73 keys the format uses. An earlier scheme packed
# the first two bytes and the length; it collided on six pairs, and fatally on
# numParams / numNested / numFields / numMinors, which are exactly the fields
# an inductive declaration cannot be read without telling apart.
#
# Substring search would be wrong: a Name's string value can be any Lean
# identifier, including "app" or "lam", so a key counts only at depth 1 and
# only in key position. That needs brace, string and escape tracking, which is
# why this is a state machine and not a search.
#
# It also numbers objects. An `inductive` record nests arrays of objects --
# the types, their constructors, the recursors, and each recursor's rules --
# and every one of those repeats the same keys, so a field has to be
# attributed to the object it came from as well as to its key.
#
# It consumes exactly one byte per step with the byte list first, so Bend's
# termination checker accepts it structurally: no fuel, no @unsafe.
#
# Verified line-for-line against a real JSON parser on all 196 small-corpus
# files by tools/census-check.py and tools/decode-check.py.

import Base

type BC is Data:
  BQuote{}
  BBrace{}
  BBrack{}
  BCurly{}
  BSquare{}
  BColon{}
  BComma{}
  BBack{}
  BOther{}

type Mode is Data:
  MStr{}
  MKey{}
  MTop{}

# d    brace depth (top-level keys sit at depth 1)
# s    inside a string
# e    previous byte was a backslash
# v    in value position (after a `:`, before the next `,`)
# y    reading a key's bytes
# h    rolling hash of the key being read
# n    record kind: hash of the first non-index key
# g    hash of the key most recently closed, so values can be attributed
# o    next object ordinal to hand out
# c    ordinal of the innermost open object
# k    enclosing ordinals, innermost first
type Sc is Data:
  Sc{
    d: U32,
    s: Bool,
    e: Bool,
    v: Bool,
    y: Bool,
    h: U32,
    n: U32,
    g: U32,
    o: U32,
    c: U32,
    k: List<&2, U32>,
  }

def Sc.start() -> Sc:
  Sc{0, False{}, False{}, False{}, False{}, 0, 0, 0, 0, 0, Nil{}}

def Sc.kind(+st: Sc) -> U32:
  match st:
    case Sc{d, s, e, v, y, h, n, g, o, c, k}:
      n

def Sc.key(+st: Sc) -> U32:
  match st:
    case Sc{d, s, e, v, y, h, n, g, o, c, k}:
      g

def Sc.obj(+st: Sc) -> U32:
  match st:
    case Sc{d, s, e, v, y, h, n, g, o, c, k}:
      c

def Sc.instr(+st: Sc) -> Bool:
  match st:
    case Sc{d, s, e, v, y, h, n, g, o, c, k}:
      s

def Sc.esc(+st: Sc) -> Bool:
  match st:
    case Sc{d, s, e, v, y, h, n, g, o, c, k}:
      e

def Sc.inkey(+st: Sc) -> Bool:
  match st:
    case Sc{d, s, e, v, y, h, n, g, o, c, k}:
      y

# A computed Bool cannot be a `match` scrutinee, so each test becomes a helper
# over its own parameter, and defs may only call defs written above them.
def pick(+z: Bool, +x: U32, +y: U32) -> U32:
  match z:
    case True{}:
      x
    case False{}:
      y

def pick_b(+z: Bool, +x: Bool, +y: Bool) -> Bool:
  match z:
    case True{}:
      x
    case False{}:
      y

def pick_l(+z: Bool, +x: List<&2, U32>, +y: List<&2, U32>) -> List<&2, U32>:
  match z:
    case True{}:
      x
    case False{}:
      y

def top_or(xs: List<&2, U32>, +dflt: U32) -> U32:
  match xs:
    case Nil{}:
      dflt
    case Con{head, tail}:
      head

def pop_or(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{head, tail}:
      tail

def bc_other(+z: Bool) -> BC:
  match z:
    case True{}:
      BBack{}
    case False{}:
      BOther{}

def bc_comma(+z: Bool, +c: U32) -> BC:
  match z:
    case True{}:
      BComma{}
    case False{}:
      bc_other(U32.is_eq(c, 92))

def bc_colon(+z: Bool, +c: U32) -> BC:
  match z:
    case True{}:
      BColon{}
    case False{}:
      bc_comma(U32.is_eq(c, 44), c)

def bc_square(+z: Bool, +c: U32) -> BC:
  match z:
    case True{}:
      BSquare{}
    case False{}:
      bc_colon(U32.is_eq(c, 58), c)

def bc_curly(+z: Bool, +c: U32) -> BC:
  match z:
    case True{}:
      BCurly{}
    case False{}:
      bc_square(U32.is_eq(c, 93), c)

def bc_brack(+z: Bool, +c: U32) -> BC:
  match z:
    case True{}:
      BBrack{}
    case False{}:
      bc_curly(U32.is_eq(c, 125), c)

def bc_brace(+z: Bool, +c: U32) -> BC:
  match z:
    case True{}:
      BBrace{}
    case False{}:
      bc_brack(U32.is_eq(c, 91), c)

def bc_quote(+z: Bool, +c: U32) -> BC:
  match z:
    case True{}:
      BQuote{}
    case False{}:
      bc_brace(U32.is_eq(c, 123), c)

def bclass(+c: U32) -> BC:
  bc_quote(U32.is_eq(c, 34), c)

def mode_of(+s: Bool, +y: Bool) -> Mode:
  match s y:
    case True{} _:
      MStr{}
    case False{} True{}:
      MKey{}
    case False{} False{}:
      MTop{}

# 3365 "in", 3356 "ie", 3363 "il".
def is_index_sig(+g: U32) -> Bool:
  U32.is_eq(g, 3365) || U32.is_eq(g, 3356) || U32.is_eq(g, 3363)

# The first non-index key a record shows is its kind; later keys are ignored.
def resolve(+g: U32, +n: U32) -> U32:
  pick(U32.is_eq(n, 0), pick(is_index_sig(g), n, g), n)

# Inside a string value. The escape flag is checked before the byte, so a
# quoted backslash never ends the string.
#
# The state is passed flat rather than as an `Sc`: a scrutinee must be a
# parameter and scrutinees must follow binder order, so a field destructured
# from a record cannot be matched alongside an earlier argument.
def step_str(+bc: BC, +e: Bool, +d: U32, +s: Bool, +v: Bool, +y: Bool,
             +h: U32, +n: U32, +g: U32, +o: U32, +c: U32,
             +k: List<&2, U32>) -> Sc:
  match bc e:
    case _ True{}:
      Sc{d, s, False{}, v, y, h, n, g, o, c, k}
    case BBack{} False{}:
      Sc{d, s, True{}, v, y, h, n, g, o, c, k}
    case BQuote{} False{}:
      Sc{d, False{}, False{}, v, y, h, n, g, o, c, k}
    case _ False{}:
      Sc{d, s, e, v, y, h, n, g, o, c, k}

# Reading a key's bytes. On the closing quote the hash is resolved: the first
# non-index key becomes the record's kind, and every closed key is recorded in
# `g` so the value that follows can be attributed to it.
def step_key(+bc: BC, +ch: U32, +d: U32, +s: Bool, +e: Bool, +v: Bool,
             +y: Bool, +h: U32, +n: U32, +g: U32, +o: U32, +c: U32,
             +k: List<&2, U32>) -> Sc:
  match bc:
    case BQuote{}:
      Sc{d, s, e, v, False{}, h, resolve(h, n), h, o, c, k}
    case _:
      Sc{d, s, e, v, y, ((h * 31 : U32) + ch : U32), n, g, o, c, k}

# Outside any string: brace depth, whether the next quote opens a key or a
# string value, and object numbering. An object's contents start with a key,
# an array's with a value -- getting that wrong at depth 2 made nested keys
# read as string values.
def step_top(+bc: BC, +d: U32, +s: Bool, +e: Bool, +v: Bool, +y: Bool,
             +h: U32, +n: U32, +g: U32, +o: U32, +c: U32,
             +k: List<&2, U32>) -> Sc:
  match bc:
    case BQuote{}:
      Sc{d, v, e, v, pick_b(v, False{}, True{}), pick(v, h, 0), n, g, o, c, k}
    case BBrace{}:
      Sc{(d + 1 : U32), s, e, False{}, y, h, n, g, (o + 1 : U32), o,
         Con{c, k}}
    case BCurly{}:
      Sc{(d - 1 : U32), s, e, True{}, y, h, n, g, o, top_or(k, 0),
         pop_or(k)}
    case BBrack{}:
      Sc{(d + 1 : U32), s, e, True{}, y, h, n, g, o, c, k}
    case BSquare{}:
      Sc{(d - 1 : U32), s, e, True{}, y, h, n, g, o, c, k}
    case BColon{}:
      Sc{d, s, e, True{}, y, h, n, g, o, c, k}
    # Unconditional: no array in this format holds strings, so after a comma
    # inside one the next byte is a digit or `{`, and neither consults `v`.
    case BComma{}:
      Sc{d, s, e, False{}, y, h, n, g, o, c, k}
    case BBack{}:
      Sc{d, s, e, v, y, h, n, g, o, c, k}
    case BOther{}:
      Sc{d, s, e, v, y, h, n, g, o, c, k}

def step_mode(+m: Mode, +bc: BC, +ch: U32, +d: U32, +s: Bool, +e: Bool,
              +v: Bool, +y: Bool, +h: U32, +n: U32, +g: U32, +o: U32,
              +c: U32, +k: List<&2, U32>) -> Sc:
  match m:
    case MStr{}:
      step_str(bc, e, d, s, v, y, h, n, g, o, c, k)
    case MKey{}:
      step_key(bc, ch, d, s, e, v, y, h, n, g, o, c, k)
    case MTop{}:
      step_top(bc, d, s, e, v, y, h, n, g, o, c, k)

def step(+ch: U32, +st: Sc) -> Sc:
  match st:
    case Sc{d, s, e, v, y, h, n, g, o, c, k}:
      step_mode(mode_of(s, y), bclass(ch), ch, d, s, e, v, y, h, n, g, o, c, k)

# A newline ends a record: emit its kind and start over. Both of these are
# pure, because a dispatch helper that chose between stepping and emitting
# would have to call `scan` back, and Bend forbids mutual recursion.
def next_state(+nl: Bool, +ch: U32, +st: Sc) -> Sc:
  match nl:
    case True{}:
      Sc.start()
    case False{}:
      step(ch, st)

def next_out(+nl: Bool, +st: Sc, out: List<&2, U32>) -> List<&2, U32>:
  match nl:
    case True{}:
      Con{Sc.kind(st), out}
    case False{}:
      out

# Emits one kind code per line, newest first.
def scan(bs: List<&2, U32>, +st: Sc, out: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      out
    case Con{head, tail}:
      +ch = head
      +nl = U32.is_eq(ch, 10)
      scan(tail, next_state(nl, ch, st), next_out(nl, st, out))
