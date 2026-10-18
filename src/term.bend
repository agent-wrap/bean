# Term representation and the index-addressed store.
#
# Children are stored as the export's own integer indices, never as nested
# terms. The export is already a hash-consed DAG -- one expression in the
# magma test is referenced 1,615 times -- so reading it as a tree explodes,
# and the indices are exactly the address space a memo table needs. Bend has
# no U64 and no hash map, so nothing else would serve; `bench/array.bend`
# measures Array at about 1 ns per access, flat, which makes this viable.
#
# Index 0 is `Name.anonymous` and `Level.zero` implicitly: the exporter never
# emits a record for either. Expression indices start at 0 and are emitted.

import Base
import ./scan.bend as S
import ./decode.bend as D

type Nm is Data:
  NAnon{}
  NStr{pre: U32, s: List<&2, U32>}
  NNum{pre: U32, i: U32}

type Lvl is Data:
  LZero{}
  LSucc{l: U32}
  LMax{a: U32, b: U32}
  LIMax{a: U32, b: U32}
  LParam{n: U32}

# `bi` is the first two bytes of binderInfo packed as b1*256+b2:
# de default, im implicit, in instImplicit, st strictImplicit.
type Ex is Data:
  EBad{}
  EBVar{i: U32}
  ESort{l: U32}
  EConst{n: U32, us: List<&2, U32>}
  EApp{f: U32, a: U32}
  ELam{n: U32, t: U32, b: U32, bi: U32}
  EAll{n: U32, t: U32, b: U32, bi: U32}
  ELet{n: U32, t: U32, v: U32, b: U32}
  EProj{tn: U32, i: U32, s: U32}
  ENat{d: List<&2, U32>}
  EStr{d: List<&2, U32>}

# Looks a field up by the signature of its key. Threading the answer through
# the default rather than returning early keeps this self-recursive: a helper
# that branched on the comparison would have to call back here, and Bend
# forbids mutual recursion. Single-valued fields occur once, so last == first.
def fld(+xs: List<&2, D.Fld>, +g: U32, +dflt: U32) -> U32:
  match xs:
    case Nil{}:
      dflt
    case Con{head, tail}:
      match head:
        case D.Fld{fg, fv, fo}:
          fld(tail, g, S.pick(U32.is_eq(fg, g), fv, dflt))

def cons_fld(+z: Bool, d: D.Fld, acc: List<&2, D.Fld>) -> List<&2, D.Fld>:
  match z:
    case True{}:
      Con{d, acc}
    case False{}:
      acc

def cons_if(+z: Bool, +v: U32, +acc: List<&2, U32>) -> List<&2, U32>:
  match z:
    case True{}:
      Con{v, acc}
    case False{}:
      acc

# Every field under one key, in order: the universe list of a `const`, the
# two operands of a `max`, a declaration's `levelParams`.
def gather(+xs: List<&2, D.Fld>, +g: U32, +acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case D.Fld{fg, fv, fo}:
          gather(tail, g, cons_if(U32.is_eq(fg, g), fv, acc))

def head_or(+xs: List<&2, U32>, +dflt: U32) -> U32:
  match xs:
    case Nil{}:
      dflt
    case Con{head, tail}:
      head

def tail_of(+xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{head, tail}:
      tail

# Two operands under one key, in source order: `max` and `imax` serialise
# theirs as a bare array.
def pair_under(+flds: List<&2, D.Fld>, +g: U32) -> U32 & U32:
  +ys = D.rev_u32(gather(flds, g, Nil{}), Nil{})
  (head_or(ys, 0), head_or(tail_of(ys), 0))

# A match cannot scrutinise a computed value, so the pair goes into a def
# that matches its own parameter.
def mk_max(r: U32 & U32) -> Lvl:
  match r:
    case Tuple{a, b}:
      LMax{a, b}

def mk_imax(r: U32 & U32) -> Lvl:
  match r:
    case Tuple{a, b}:
      LIMax{a, b}

# --- level dispatch ------------------------------------------------------
# 3541570 succ, 107876 max, 3235931 imax, 106436749 param.
def lvl_param(+z: Bool, +flds: List<&2, D.Fld>) -> Lvl:
  match z:
    case True{}:
      LParam{fld(flds, 106436749, 0)}
    case False{}:
      LZero{}

def lvl_imax(+z: Bool, +k: U32, +flds: List<&2, D.Fld>) -> Lvl:
  match z:
    case True{}:
      mk_imax(pair_under(flds, 3235931))
    case False{}:
      lvl_param(U32.is_eq(k, 106436749), flds)

def lvl_max(+z: Bool, +k: U32, +flds: List<&2, D.Fld>) -> Lvl:
  match z:
    case True{}:
      mk_max(pair_under(flds, 107876))
    case False{}:
      lvl_imax(U32.is_eq(k, 3235931), k, flds)

def lvl_succ(+z: Bool, +k: U32, +flds: List<&2, D.Fld>) -> Lvl:
  match z:
    case True{}:
      LSucc{fld(flds, 3541570, 0)}
    case False{}:
      lvl_max(U32.is_eq(k, 107876), k, flds)

def mk_lvl(+k: U32, +flds: List<&2, D.Fld>) -> Lvl:
  lvl_succ(U32.is_eq(k, 3541570), k, flds)

# --- name dispatch -------------------------------------------------------
# 114225 str, 109446 num; 111267 pre, 105 i.
def nm_num(+z: Bool, +flds: List<&2, D.Fld>) -> Nm:
  match z:
    case True{}:
      NNum{fld(flds, 111267, 0), fld(flds, 105, 0)}
    case False{}:
      NAnon{}

def nm_str(+z: Bool, +k: U32, +flds: List<&2, D.Fld>, +sb: List<&2, U32>) -> Nm:
  match z:
    case True{}:
      NStr{fld(flds, 111267, 0), sb}
    case False{}:
      nm_num(U32.is_eq(k, 109446), flds)

def mk_nm(+k: U32, +flds: List<&2, D.Fld>, +sb: List<&2, U32>) -> Nm:
  nm_str(U32.is_eq(k, 114225), k, flds, sb)

# --- expression dispatch -------------------------------------------------
# Kinds:  3036037 bvar, 3536286 sort, 94844771 const, 96801 app,
#         106904 lam, 3617176333 forallE, 3318154 letE, 3449693 proj,
#         3242329664 natVal, 3402962736 strVal.
# Fields: 3373707 name, 3575610 type, 3029410 body, 111972721 value,
#         3272 fn, 96854 arg, 3618459877 typeName, 104125 idx,
#         3402992597 struct, 3742 us.
# `struct` and `strVal` no longer share a signature: the key hash is
# collision-free over the whole key set (tools/keycodes.json).
def ex_str(+z: Bool, +sb: List<&2, U32>) -> Ex:
  match z:
    case True{}:
      EStr{sb}
    case False{}:
      EBad{}

def ex_nat(+z: Bool, +k: U32, +sb: List<&2, U32>) -> Ex:
  match z:
    case True{}:
      ENat{sb}
    case False{}:
      ex_str(U32.is_eq(k, 3402962736), sb)

def ex_proj(+z: Bool, +k: U32, +flds: List<&2, D.Fld>, +sb: List<&2, U32>) -> Ex:
  match z:
    case True{}:
      EProj{fld(flds, 3618459877, 0), fld(flds, 104125, 0), fld(flds, 3402992597, 0)}
    case False{}:
      ex_nat(U32.is_eq(k, 3242329664), k, sb)

def ex_let(+z: Bool, +k: U32, +flds: List<&2, D.Fld>, +sb: List<&2, U32>) -> Ex:
  match z:
    case True{}:
      ELet{fld(flds, 3373707, 0), fld(flds, 3575610, 0),
           fld(flds, 111972721, 0), fld(flds, 3029410, 0)}
    case False{}:
      ex_proj(U32.is_eq(k, 3449693), k, flds, sb)

def ex_all(+z: Bool, +k: U32, +bi: U32, +flds: List<&2, D.Fld>,
           +sb: List<&2, U32>) -> Ex:
  match z:
    case True{}:
      EAll{fld(flds, 3373707, 0), fld(flds, 3575610, 0),
           fld(flds, 3029410, 0), bi}
    case False{}:
      ex_let(U32.is_eq(k, 3318154), k, flds, sb)

def ex_lam(+z: Bool, +k: U32, +bi: U32, +flds: List<&2, D.Fld>,
           +sb: List<&2, U32>) -> Ex:
  match z:
    case True{}:
      ELam{fld(flds, 3373707, 0), fld(flds, 3575610, 0),
           fld(flds, 3029410, 0), bi}
    case False{}:
      ex_all(U32.is_eq(k, 3617176333), k, bi, flds, sb)

def ex_app(+z: Bool, +k: U32, +bi: U32, +flds: List<&2, D.Fld>,
           +sb: List<&2, U32>) -> Ex:
  match z:
    case True{}:
      EApp{fld(flds, 3272, 0), fld(flds, 96854, 0)}
    case False{}:
      ex_lam(U32.is_eq(k, 106904), k, bi, flds, sb)

def ex_const(+z: Bool, +k: U32, +bi: U32, +flds: List<&2, D.Fld>,
             +sb: List<&2, U32>) -> Ex:
  match z:
    case True{}:
      EConst{fld(flds, 3373707, 0),
             D.rev_u32(gather(flds, 3742, Nil{}), Nil{})}
    case False{}:
      ex_app(U32.is_eq(k, 96801), k, bi, flds, sb)

def ex_sort(+z: Bool, +k: U32, +bi: U32, +flds: List<&2, D.Fld>,
            +sb: List<&2, U32>) -> Ex:
  match z:
    case True{}:
      ESort{fld(flds, 3536286, 0)}
    case False{}:
      ex_const(U32.is_eq(k, 94844771), k, bi, flds, sb)

def ex_bvar(+z: Bool, +k: U32, +bi: U32, +flds: List<&2, D.Fld>,
            +sb: List<&2, U32>) -> Ex:
  match z:
    case True{}:
      EBVar{fld(flds, 3036037, 0)}
    case False{}:
      ex_sort(U32.is_eq(k, 3536286), k, bi, flds, sb)

def mk_ex(+k: U32, +bi: U32, +flds: List<&2, D.Fld>, +sb: List<&2, U32>) -> Ex:
  ex_bvar(U32.is_eq(k, 3036037), k, bi, flds, sb)
