# The index-addressed store, and the declaration list.
#
# `Array<T>` is a `Type`, so it has exactly one owner; a record holding three
# of them is affine and has to be threaded linearly through the fold that
# fills it. That is the cost of in-place update without giving up purity.
#
# Which table a record belongs to is derived from its kind, not from which
# index key it carried, so the decoder does not need to remember that.

import Base
import ./scan.bend as S
import ./decode.bend as D
import ./term.bend as T
import ./trie.bend as R2

type Dcl is Data:
  DNone{}
  DAxiom{n: U32, lps: List<&2, U32>, t: U32}
  DDef{n: U32, lps: List<&2, U32>, t: U32, v: U32}
  DThm{n: U32, lps: List<&2, U32>, t: U32, v: U32}
  DOpaque{n: U32, lps: List<&2, U32>, t: U32, v: U32}
  DQuot{n: U32, lps: List<&2, U32>, t: U32}
  # An inductive block declares its types, constructors and recursors all at
  # once. Every one of those carries a `name` field, and `name` has its own
  # key signature, so gathering that one key over the whole record yields
  # exactly the set of constants the block introduces -- without having to
  # decode the block's structure yet.
  DInd{nms: List<&2, U32>, items: List<&2, IItem>}

type Store is Type:
  Store{
    nms: Array<T.Nm>,
    lvls: Array<T.Lvl>,
    exprs: Array<T.Ex>,
  }

def Store.new(+d: Nat) -> Store:
  Store{Array.new(T.Nm, d, T.NAnon{}),
        Array.new(T.Lvl, d, T.LZero{}),
        Array.new(T.Ex, d, T.EBad{})}

def is_nm_kind(+k: U32) -> Bool:
  U32.is_eq(k, 114225) || U32.is_eq(k, 109446)

def is_lvl_kind(+k: U32) -> Bool:
  U32.is_eq(k, 3541570) || U32.is_eq(k, 107876)
  || U32.is_eq(k, 3235931) || U32.is_eq(k, 106436749)

def is_ex_kind(+k: U32) -> Bool:
  U32.is_eq(k, 3036037) || U32.is_eq(k, 3536286) || U32.is_eq(k, 94844771)
  || U32.is_eq(k, 96801) || U32.is_eq(k, 106904) || U32.is_eq(k, 3617176333)
  || U32.is_eq(k, 3318154) || U32.is_eq(k, 3449693) || U32.is_eq(k, 3242329664)
  || U32.is_eq(k, 3402962736)


# --- inductive blocks ----------------------------------------------------
# An `inductive` record carries the inductive types, their constructors and
# the recursors together, as arrays of objects that all repeat the same keys.
# Fields are therefore grouped by the object ordinal the scanner assigns, and
# each group classified by a key only its kind has. Those keys are why the
# old two-byte key signature had to go: numParams, numNested, numFields and
# numMinors all collided under it.
#
# 3373707 name, 1678233130 levelParams, 3575610 type, 1130910892 numParams,
# 3435386177 numIndices, 1077394461 numNested, 3110742887 induct,
# 3053434 cidx, 851630559 numFields, 2733857351 numMotives,
# 1052306052 numMinors, 1861416103 nfields, 3064340 ctor, 112893 rhs.
type IItem is Data:
  IOther{}
  IInd{nm: U32, lps: List<&2, U32>, ty: U32, np: U32, ni: U32, nn: U32, cs: List<&2, U32>}
  ICtor{nm: U32, lps: List<&2, U32>, ty: U32, ind: U32, np: U32, nf: U32, ci: U32}
  # `kf` is the export's `k` flag: a claim that this recursor reduces
  # K-like, which the kernel must check rather than trust.
  IRec{nm: U32, lps: List<&2, U32>, ty: U32, np: U32, ni: U32, nmo: U32,
       kf: U32}
  IRule{ct: U32, nf: U32, rhs: U32}

def mem_u(+v: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{head, tail}:
      U32.is_eq(head, v) || mem_u(v, tail)

def obs_of(xs: List<&2, D.Fld>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case D.Fld{g, v, ob}:
          +po = ob
          +a = acc
          obs_of(tail, S.pick_l(mem_u(po, a), a, Con{po, a}))

def flds_rev(xs: List<&2, D.Fld>, +ob: U32,
             acc: List<&2, D.Fld>) -> List<&2, D.Fld>:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case D.Fld{g, v, ob2}:
          +po = ob2
          flds_rev(tail, ob,
                   T.cons_fld(U32.is_eq(po, ob), D.Fld{g, v, po}, acc))

def has_key(+fs: List<&2, D.Fld>, +g: U32) -> Bool:
  Bool.not(U32.is_eq(T.fld(fs, g, 4294967295), 4294967295))

def mk_item4(+z: Bool, +fs: List<&2, D.Fld>) -> IItem:
  match z:
    case True{}:
      IInd{T.fld(fs, 3373707, 0),
           D.rev_u32(T.gather(fs, 1678233130, Nil{}), Nil{}),
           T.fld(fs, 3575610, 0), T.fld(fs, 1130910892, 0),
           T.fld(fs, 3435386177, 0), T.fld(fs, 1077394461, 0),
           D.rev_u32(T.gather(fs, 94994655, Nil{}), Nil{})}
    case False{}:
      IOther{}

def mk_item3(+z: Bool, +fs: List<&2, D.Fld>) -> IItem:
  match z:
    case True{}:
      IRec{T.fld(fs, 3373707, 0),
           D.rev_u32(T.gather(fs, 1678233130, Nil{}), Nil{}),
           T.fld(fs, 3575610, 0), T.fld(fs, 1130910892, 0),
           T.fld(fs, 3435386177, 0), T.fld(fs, 2733857351, 0),
           T.fld(fs, 107, 0)}
    case False{}:
      mk_item4(has_key(fs, 1077394461), fs)

def mk_item2(+z: Bool, +fs: List<&2, D.Fld>) -> IItem:
  match z:
    case True{}:
      ICtor{T.fld(fs, 3373707, 0),
            D.rev_u32(T.gather(fs, 1678233130, Nil{}), Nil{}),
            T.fld(fs, 3575610, 0), T.fld(fs, 3110742887, 0),
            T.fld(fs, 1130910892, 0), T.fld(fs, 851630559, 0),
            T.fld(fs, 3053434, 0)}
    case False{}:
      mk_item3(has_key(fs, 2733857351), fs)

def item_rule(+z: Bool, +fs: List<&2, D.Fld>) -> IItem:
  match z:
    case True{}:
      IRule{T.fld(fs, 3064340, 0), T.fld(fs, 1861416103, 0),
            T.fld(fs, 112893, 0)}
    case False{}:
      mk_item2(has_key(fs, 3110742887), fs)

def mk_item(+fs: List<&2, D.Fld>) -> IItem:
  item_rule(has_key(fs, 1861416103), fs)

def items_of(obs: List<&2, U32>, +all: List<&2, D.Fld>,
             acc: List<&2, IItem>) -> List<&2, IItem>:
  match obs:
    case Nil{}:
      acc
    case Con{head, tail}:
      items_of(tail, all,
               Con{mk_item(D.rev_pair(flds_rev(all, head, Nil{}), Nil{})), acc})

def dcl_quot(+z: Bool, +nm: U32, +lps: List<&2, U32>, +ty: U32) -> Dcl:
  match z:
    case True{}:
      DQuot{nm, lps, ty}
    case False{}:
      DNone{}

def dcl_opaque(+z: Bool, +k: U32, +nm: U32, +lps: List<&2, U32>,
               +ty: U32, +vl: U32) -> Dcl:
  match z:
    case True{}:
      DOpaque{nm, lps, ty, vl}
    case False{}:
      dcl_quot(U32.is_eq(k, 3482377), nm, lps, ty)

def dcl_axiom(+z: Bool, +k: U32, +nm: U32, +lps: List<&2, U32>,
              +ty: U32, +vl: U32) -> Dcl:
  match z:
    case True{}:
      DAxiom{nm, lps, ty}
    case False{}:
      dcl_opaque(U32.is_eq(k, 3284272161), k, nm, lps, ty, vl)

def dcl_thm(+z: Bool, +k: U32, +nm: U32, +lps: List<&2, U32>,
            +ty: U32, +vl: U32) -> Dcl:
  match z:
    case True{}:
      DThm{nm, lps, ty, vl}
    case False{}:
      dcl_axiom(U32.is_eq(k, 93260912), k, nm, lps, ty, vl)

def dcl_def(+z: Bool, +k: U32, +nm: U32, +lps: List<&2, U32>,
            +ty: U32, +vl: U32) -> Dcl:
  match z:
    case True{}:
      DDef{nm, lps, ty, vl}
    case False{}:
      dcl_thm(U32.is_eq(k, 114809), k, nm, lps, ty, vl)

# Inductive blocks carry types, constructors and recursors together and need
# their own decoding; they are recognised but not yet read.
def dcl_ind(+z: Bool, +k: U32, +nm: U32, +lps: List<&2, U32>,
            +ty: U32, +vl: U32, +flds: List<&2, D.Fld>) -> Dcl:
  match z:
    case True{}:
      DInd{D.rev_u32(T.gather(flds, 3373707, Nil{}), Nil{}),
           items_of(obs_of(flds, Nil{}), flds, Nil{})}
    case False{}:
      dcl_def(U32.is_eq(k, 99333), k, nm, lps, ty, vl)

# 1678233130 levelParams, 3373707 name, 3575610 type, 111972721 value.
def mk_dcl(+k: U32, +flds: List<&2, D.Fld>) -> Dcl:
  +nm = T.fld(flds, 3373707, 0)
  +lps = D.rev_u32(T.gather(flds, 1678233130, Nil{}), Nil{})
  +ty = T.fld(flds, 3575610, 0)
  +vl = T.fld(flds, 111972721, 0)
  dcl_ind(U32.is_eq(k, 3927072785), k, nm, lps, ty, vl, flds)

def set_nm(+i: U32, v: T.Nm, st: Store) -> Store:
  match st:
    case Store{nms, lvls, exprs}:
      Store{Array.set(T.Nm, nms, i, v), lvls, exprs}

def set_lvl(+i: U32, v: T.Lvl, st: Store) -> Store:
  match st:
    case Store{nms, lvls, exprs}:
      Store{nms, Array.set(T.Lvl, lvls, i, v), exprs}

def set_ex(+i: U32, v: T.Ex, st: Store) -> Store:
  match st:
    case Store{nms, lvls, exprs}:
      Store{nms, lvls, Array.set(T.Ex, exprs, i, v)}

def place_cat(+isn: Bool, +isl: Bool, +ise: Bool, +k: U32, +ix: U32,
              +bi: U32, +flds: List<&2, D.Fld>, +sb: List<&2, U32>,
              st: Store) -> Store:
  match isn isl ise:
    case True{} _ _:
      set_nm(ix, T.mk_nm(k, flds, sb), st)
    case False{} True{} _:
      set_lvl(ix, T.mk_lvl(k, flds), st)
    case False{} False{} True{}:
      set_ex(ix, T.mk_ex(k, bi, flds, sb), st)
    case False{} False{} False{}:
      st

def place(+r: D.Rec, st: Store) -> Store:
  match r:
    case D.Rec{kind, ix, flds, b1, b2, sb}:
      place_cat(is_nm_kind(kind), is_lvl_kind(kind), is_ex_kind(kind),
                kind, ix, ((b1 * 256 : U32) + b2 : U32), flds, sb, st)

def is_dcl_kind(+k: U32) -> Bool:
  U32.is_eq(k, 99333) || U32.is_eq(k, 114809) || U32.is_eq(k, 93260912)
  || U32.is_eq(k, 3284272161) || U32.is_eq(k, 3482377) || U32.is_eq(k, 3927072785)

def cons_dcl(+z: Bool, d: Dcl, ds: List<&2, Dcl>) -> List<&2, Dcl>:
  match z:
    case True{}:
      Con{d, ds}
    case False{}:
      ds

def add_dcl(+r: D.Rec, ds: List<&2, Dcl>) -> List<&2, Dcl>:
  match r:
    case D.Rec{kind, ix, flds, b1, b2, sb}:
      cons_dcl(is_dcl_kind(kind), mk_dcl(kind, flds), ds)

# Just the declarations, with no Array store: the checker reads terms from
# tries instead, so nothing here needs an Array.
# Names, so that a recursor's name can be compared with the one the kernel
# would derive -- `I.rec` -- rather than taken from the export.
def nm_step(+go: Bool, +t: R2.Tr<T.Nm>, +ix: U32, +k: U32,
            +flds: List<&2, D.Fld>, +sb: List<&2, U32>) -> R2.Tr<T.Nm>:
  match go:
    case True{}:
      R2.set(T.Nm, 64n, t, ix, T.mk_nm(k, flds, sb), T.NAnon{})
    case False{}:
      t

def build_nm(rs: List<&2, D.Rec>, +t: R2.Tr<T.Nm>) -> R2.Tr<T.Nm>:
  match rs:
    case Nil{}:
      t
    case Con{head, tail}:
      match head:
        case D.Rec{kind, ix, flds, b1, b2, sb}:
          +k = kind
          build_nm(tail, nm_step(is_nm_kind(k), t, ix, k, flds, sb))

# --- reducibility heights ------------------------------------------------
# Lean's `ReducibilityHints`, which the export carries in a `def`'s `hints`
# field: `"abbrev"`, `{"regular": n}`, or `"opaque"`. They exist to ORDER
# delta unfolding -- the kernel unfolds the definition of greater height
# first when comparing two different constants, and unfolding in the wrong
# order is exponential. `perf/fueled-chain` is 84 prelude definitions built
# to punish exactly that.
#
# Only the `regular` case needs reading, and the scanner already captures it:
# `hints` is an object there, so `regular` is an ordinary nested key and its
# value is a number. `"abbrev"` and `"opaque"` are plain strings with no
# nested key, so they are indistinguishable here -- both come back as "no
# regular key". Both are treated as the maximum height, which is right for
# `abbrev` (unfold first) and merely conservative for `opaque`: a `def` with
# the `opaque` *hint* still has a value and unfolding it is sound, unlike an
# `opaque` *declaration*, which has no value and never enters `vt` at all.
def height_of(+fs: List<&2, D.Fld>) -> U32:
  +h = T.fld(fs, 1086463900, 4294967295)
  S.pick(U32.is_eq(h, 4294967295), 4294967294, h)

# a def's height under `name + off` (only def records insert)
def ht_step(+go: Bool, +t: R2.Tr<U32>, +off: U32,
            +fs: List<&2, D.Fld>) -> R2.Tr<U32>:
  match go:
    case True{}:
      R2.set(U32, 64n, t, (T.fld(fs, 3373707, 0) + off : U32),
             height_of(fs), 4294967295)
    case False{}:
      t

def build_ht(rs: List<&2, D.Rec>, +t: R2.Tr<U32>) -> R2.Tr<U32>:
  match rs:
    case Nil{}:
      t
    case Con{head, tail}:
      match head:
        case D.Rec{kind, ix, flds, b1, b2, sb}:
          +k = kind
          build_ht(tail, ht_step(U32.is_eq(k, 99333), t, 0, flds))

# --- finding a name by its text ------------------------------------------
# `Nat` and `String` have to be named to type a literal: `infer` on
# `ENat`/`EStr` must answer with the constant, and the export's name INDEX
# for it is not fixed -- it is whatever ordinal the file happened to use. So
# the name table is scanned once for a top-level `str` name whose bytes
# match, and the index is carried in the state.
#
# `pre = 0` is required: the name must be top-level, so a `Foo.Nat` elsewhere
# in the file cannot be mistaken for it.
def bytes_eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{h1, t1} Con{h2, t2}:
      U32.is_eq(h1, h2) && bytes_eq(t1, t2)
    case _ _:
      False{}

def find_name(+rs: List<&2, D.Rec>, +want: List<&2, U32>,
              +acc: U32) -> U32:
  match rs:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case D.Rec{kind, ix, flds, b1, b2, sb}:
          +k = kind
          +fs = flds
          +pix = ix
          find_name(tail, want,
                    S.pick(U32.is_eq(k, 114225)
                           && U32.is_eq(T.fld(fs, 111267, 1), 0)
                           && bytes_eq(sb, want),
                           pix, acc))

# The quotient package's four names, which the kernel needs by identity to
# implement `Quot.lift` and `Quot.ind` reduction. The export declares them as
# `quot` declarations with a `kind` string, but the scanner captures one
# string payload per record and a `quot` record has others, so they are found
# by NAME instead: `Quot` at top level, then `mk`, `lift` and `ind` under it.
#
# Slot 0 is `Quot.lift`, 1 is `Quot.ind`, 2 is `Quot.mk`. A name the file
# never declares stays 4294967295 and the corresponding rule never fires.
def find_under(+rs: List<&2, D.Rec>, +pre: U32, +want: List<&2, U32>,
               +acc: U32) -> U32:
  match rs:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case D.Rec{kind, ix, flds, b1, b2, sb}:
          +k = kind
          +fs = flds
          +pix = ix
          find_under(tail, pre, want,
                     S.pick(U32.is_eq(k, 114225)
                            && U32.is_eq(T.fld(fs, 111267, 4294967295), pre)
                            && bytes_eq(sb, want),
                            pix, acc))

def build_quot(+rs: List<&2, D.Rec>, +t: R2.Tr<U32>) -> R2.Tr<U32>:
  +q = find_name(rs, [81, 117, 111, 116], 4294967295)
  R2.set(U32, 64n, R2.set(U32, 64n,
           R2.set(U32, 64n, t, 0,
                  find_under(rs, q, [108, 105, 102, 116], 4294967295),
                  4294967295),
           1, find_under(rs, q, [105, 110, 100], 4294967295), 4294967295),
         2, find_under(rs, q, [109, 107], 4294967295), 4294967295)

# Slots 3 and 4 are `Nat.zero` and `Nat.succ`, needed to compare a literal
# with a numeral in constructor form.
def build_wk(+rs: List<&2, D.Rec>, +t: R2.Tr<U32>) -> R2.Tr<U32>:
  +n = find_name(rs, [78, 97, 116], 4294967295)
  R2.set(U32, 64n,
         R2.set(U32, 64n, build_quot(rs, t), 3,
                find_under(rs, n, [122, 101, 114, 111], 4294967295),
                4294967295),
         4, find_under(rs, n, [115, 117, 99, 99], 4294967295), 4294967295)

# Slots 5..9: `Nat.add`, `Nat.sub`, `Nat.ble`, `Bool.true`, `Bool.false` --
# the literal operations the kernel computes directly, and the two values
# `Nat.ble` answers with.
def build_wk2(+rs: List<&2, D.Rec>, +t: R2.Tr<U32>) -> R2.Tr<U32>:
  +n = find_name(rs, [78, 97, 116], 4294967295)
  +b = find_name(rs, [66, 111, 111, 108], 4294967295)
  R2.set(U32, 64n,
  R2.set(U32, 64n,
    R2.set(U32, 64n,
      R2.set(U32, 64n,
        R2.set(U32, 64n,
          R2.set(U32, 64n, build_wk(rs, t), 5,
                 find_under(rs, n, [97, 100, 100], 4294967295), 4294967295),
          6, find_under(rs, n, [115, 117, 98], 4294967295), 4294967295),
        7, find_under(rs, n, [98, 108, 101], 4294967295), 4294967295),
      8, find_under(rs, b, [116, 114, 117, 101], 4294967295), 4294967295),
    9, find_under(rs, b, [102, 97, 108, 115, 101], 4294967295),
    4294967295),
  # key 10: `String`, so the flat machine can type a string literal
  # (it threads qtt but, unlike the trie engine's IS, has no strn field)
  10, find_name(rs, [83, 116, 114, 105, 110, 103], 4294967295), 4294967295)

# keys 11..15: Nat.mul, Nat.pow, Nat.div, Nat.mod, Nat.beq -- the rest of
# the literal operations Lean's kernel computes directly
def build_wk3(+rs: List<&2, D.Rec>, +t: R2.Tr<U32>) -> R2.Tr<U32>:
  +n = find_name(rs, [78, 97, 116], 4294967295)
  R2.set(U32, 64n,
  R2.set(U32, 64n,
  R2.set(U32, 64n,
  R2.set(U32, 64n,
  R2.set(U32, 64n, build_wk2(rs, t),
    11, find_under(rs, n, [109, 117, 108], 4294967295), 4294967295),
    12, find_under(rs, n, [112, 111, 119], 4294967295), 4294967295),
    13, find_under(rs, n, [100, 105, 118], 4294967295), 4294967295),
    14, find_under(rs, n, [109, 111, 100], 4294967295), 4294967295),
    15, find_under(rs, n, [98, 101, 113], 4294967295), 4294967295)


# definition heights for the machine's lazy delta probe, keyed name + 2^31
# in the same small table as the literal-operation names
def add_hts(rs: List<&2, D.Rec>, +t: R2.Tr<U32>) -> R2.Tr<U32>:
  match rs:
    case Nil{}:
      t
    case Con{head, tail}:
      match head:
        case D.Rec{kind, ix, flds, b1, b2, sb}:
          +k = kind
          +fs = flds
          add_hts(tail, ht_step(U32.is_eq(k, 99333), t, 2147483648, fs))

# --- every well-known name in two passes ---------------------------------
# find_name / find_under each walk the whole record list (6.4M records in
# init), and the tables below need 23 names: ~27 passes, about 50 s. These
# resolve every ROOT name in one pass, then every name UNDER a found root in
# a second. Same answer as find_name / find_under: the LAST matching record.
def I_hd(xs: List<&2, U32>) -> U32:
  match xs:
    case Con{h, t}:
      h
    case Nil{}:
      4294967294

def I_tl(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{h, t}:
      t
    case Nil{}:
      Nil{}

def fm_upd(wants: List<&2, List<&2, U32>>, +pres: List<&2, U32>,
           +pre: U32, +sb: List<&2, U32>, +pix: U32,
           acc: List<&2, U32>) -> List<&2, U32>:
  match wants acc:
    case Con{w, wt} Con{a, at}:
      +ps = pres
      Con{S.pick(U32.is_eq(I_hd(ps), pre) && bytes_eq(w, sb), pix, a),
          fm_upd(wt, I_tl(ps), pre, sb, pix, at)}
    case _ _:
      Nil{}

# a name record's update, only for name records (a Bool match: `S.pick`
# would evaluate the update on every record)
def fm_step(+go: Bool, +wants: List<&2, List<&2, U32>>,
            +pres: List<&2, U32>, +pre: U32, +sb: List<&2, U32>,
            +pix: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match go:
    case True{}:
      fm_upd(wants, pres, pre, sb, pix, acc)
    case False{}:
      acc

# `pres` gives each wanted name's prefix (0: a root name)
def find_many(rs: List<&2, D.Rec>, +wants: List<&2, List<&2, U32>>,
              +pres: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case D.Rec{kind, ix, flds, b1, b2, sb}:
          +k = kind
          +fs = flds
          find_many(tail, wants, pres,
                    fm_step(U32.is_eq(k, 114225), wants, pres,
                            T.fld(fs, 111267, 4294967295), sb, ix, acc))

def nth_or(xs: List<&2, U32>, +i: U32) -> U32:
  match xs:
    case Nil{}:
      4294967295
    case Con{h, t}:
      S.pick(U32.is_eq(i, 0), h, nth_or(t, (i - 1 : U32)))

def nones(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{4294967295, nones(p)}

def set_keys(ks: List<&2, U32>, vs: List<&2, U32>,
             +t: R2.Tr<U32>) -> R2.Tr<U32>:
  match ks vs:
    case Con{k, kt} Con{v, vt}:
      set_keys(kt, vt, R2.set(U32, 64n, t, k, v, 4294967295))
    case _ _:
      t

# keys 0..2 Quot.lift/ind/mk; 3, 4 Nat.zero/succ; 5..9 Nat.add/sub/ble,
# Bool.true/false; 10 String; 11..15 Nat.mul/pow/div/mod/beq (the literal
# operations Lean's kernel computes directly); 16..19 optParam, autoParam,
# outParam, semiOutParam -- the type annotations Lean's
# consume_type_annotations drops from the binder types of an inductive's
# params, indices and fields when it derives the recursor; 20 Nat
def build_wk4(+rs: List<&2, D.Rec>, +t: R2.Tr<U32>) -> R2.Tr<U32>:
  +roots : List<&2, U32> =
    find_many(rs, [[81, 117, 111, 116], [78, 97, 116], [66, 111, 111, 108],
                   [83, 116, 114, 105, 110, 103],
                   [111, 112, 116, 80, 97, 114, 97, 109],
                   [97, 117, 116, 111, 80, 97, 114, 97, 109],
                   [111, 117, 116, 80, 97, 114, 97, 109],
                   [115, 101, 109, 105, 79, 117, 116, 80, 97, 114, 97, 109]],
              [0, 0, 0, 0, 0, 0, 0, 0], nones(8n))
  +q : U32 = nth_or(roots, 0)
  +n : U32 = nth_or(roots, 1)
  +b : U32 = nth_or(roots, 2)
  +un : List<&2, U32> =
    find_many(rs, [[108, 105, 102, 116], [105, 110, 100], [109, 107],
                   [122, 101, 114, 111], [115, 117, 99, 99],
                   [97, 100, 100], [115, 117, 98], [98, 108, 101],
                   [116, 114, 117, 101], [102, 97, 108, 115, 101],
                   [109, 117, 108], [112, 111, 119], [100, 105, 118],
                   [109, 111, 100], [98, 101, 113]],
              [q, q, q, n, n, n, n, n, b, b, n, n, n, n, n], nones(15n))
  set_keys([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15], un,
    set_keys([10, 16, 17, 18, 19, 20],
             [nth_or(roots, 3), nth_or(roots, 4), nth_or(roots, 5),
              nth_or(roots, 6), nth_or(roots, 7), n], t))

def decls_of(rs: List<&2, D.Rec>, ds: List<&2, Dcl>) -> List<&2, Dcl>:
  match rs:
    case Nil{}:
      ds
    case Con{head, tail}:
      decls_of(tail, add_dcl(head, ds))

def build(rs: List<&2, D.Rec>, st: Store, ds: List<&2, Dcl>) -> Store & List<&2, Dcl>:
  match rs:
    case Nil{}:
      (st, ds)
    case Con{head, tail}:
      +h = head
      build(tail, place(h, st), add_dcl(h, ds))

# The loops that resolve levels and scan for unknown constants are bounded by
# the table extents rather than by the array size: indices are approximately
# dense, so this turns a fixed 262k-iteration cost per file into a few
# hundred for a small test.
# Accessors used by the table builders; the kernel has its own copies that
# also understand inductive blocks.
# an inductive block's items (empty for any other declaration)
def dcl_items(+d: Dcl) -> List<&2, IItem>:
  match d:
    case DInd{nms, items}:
      items
    case _:
      Nil{}

def dcl_name(+d: Dcl) -> U32:
  match d:
    case DAxiom{n, lps, t}:
      n
    case DDef{n, lps, t, v}:
      n
    case DThm{n, lps, t, v}:
      n
    case DOpaque{n, lps, t, v}:
      n
    case DQuot{n, lps, t}:
      n
    case _:
      0

def dcl_type(+d: Dcl) -> U32:
  match d:
    case DAxiom{n, lps, t}:
      t
    case DDef{n, lps, t, v}:
      t
    case DThm{n, lps, t, v}:
      t
    case DOpaque{n, lps, t, v}:
      t
    case DQuot{n, lps, t}:
      t
    case _:
      4294967295

def dcl_lparams(+d: Dcl) -> List<&2, U32>:
  match d:
    case DAxiom{n, lps, t}:
      lps
    case DDef{n, lps, t, v}:
      lps
    case DThm{n, lps, t, v}:
      lps
    case DOpaque{n, lps, t, v}:
      lps
    case DQuot{n, lps, t}:
      lps
    case _:
      Nil{}

def dcl_value(+d: Dcl) -> U32:
  match d:
    case DDef{n, lps, t, v}:
      v
    case DThm{n, lps, t, v}:
      v
    case DOpaque{n, lps, t, v}:
      v
    case _:
      4294967295

def dcl_is_theorem(+d: Dcl) -> Bool:
  match d:
    case DThm{n, lps, t, v}:
      True{}
    case _:
      False{}

def max_lvl_ix(rs: List<&2, D.Rec>, +acc: U32) -> U32:
  match rs:
    case Nil{}:
      acc
    case Con{head, tail}:
      +h = head
      +i = D.Rec.ix(h)
      max_lvl_ix(tail, S.pick(is_lvl_kind(D.Rec.kind(h)) && U32.is_gt(i, acc), i, acc))

def max_ex_ix(rs: List<&2, D.Rec>, +acc: U32) -> U32:
  match rs:
    case Nil{}:
      acc
    case Con{head, tail}:
      +h = head
      +i = D.Rec.ix(h)
      max_ex_ix(tail, S.pick(is_ex_kind(D.Rec.kind(h)) && U32.is_gt(i, acc), i, acc))

# Array indexes WRAP in Bend, so an index past the array size silently reads
# the wrong slot rather than failing. `perf/magma-string-n4` has 321,312
# expressions, which overflowed a depth-18 (262,144 slot) table and produced
# a wrong rejection. Tables are therefore sized from the data.
#
# The bound covers every record's own index AND every integer field, because
# a field is a reference and may name an index no record declares. That
# over-approximates -- name, level and expression references are mixed into
# one bound -- which is the safe direction, since it only makes the tables
# larger.
# Only keys that are actually table references count towards the bound.
# `Name.num`'s `i` is a hygiene counter, not an index: in
# perf/magma-string-n4 it is 4,288,742,172, which pushed the computed depth
# to 32 and made `Array.new` abort with "an array past the deepest block
# class 31". The abort exits 1, and the arena reads exit 1 as *reject* -- so
# a crash was indistinguishable from a verdict. Counts (`idx`, `cidx`,
# `numFields`, `nfields`, `bvar`, ...) are excluded for the same reason.
def is_ref_key(+g: U32) -> Bool:
  U32.is_eq(g, 3575610) || U32.is_eq(g, 3029410) || U32.is_eq(g, 111972721)
  || U32.is_eq(g, 3272) || U32.is_eq(g, 96854) || U32.is_eq(g, 3402992597)
  || U32.is_eq(g, 112893) || U32.is_eq(g, 3373707) || U32.is_eq(g, 111267)
  || U32.is_eq(g, 3618459877) || U32.is_eq(g, 3110742887) || U32.is_eq(g, 3064340)
  || U32.is_eq(g, 94994655) || U32.is_eq(g, 96673) || U32.is_eq(g, 106436749)
  || U32.is_eq(g, 3536286) || U32.is_eq(g, 3541570) || U32.is_eq(g, 107876)
  || U32.is_eq(g, 3235931) || U32.is_eq(g, 3742) || U32.is_eq(g, 1678233130)

def max_fld(xs: List<&2, D.Fld>, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case D.Fld{g, v, ob}:
          +pv = v
          max_fld(tail, S.pick(is_ref_key(g) && U32.is_gt(pv, acc), pv, acc))

def max_any_ix(rs: List<&2, D.Rec>, +acc: U32) -> U32:
  match rs:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case D.Rec{kind, ix, flds, b1, b2, sb}:
          +pix = ix
          +a1 = S.pick(U32.is_gt(pix, acc), pix, acc)
          max_any_ix(tail, max_fld(flds, a1))

def nat_pick(+z: Bool, +a: Nat, +b: Nat) -> Nat:
  match z:
    case True{}:
      a
    case False{}:
      b

# Smallest d with 2^d > n. Runs a fixed number of rounds and stabilises once
# the capacity passes n, because a helper that tested the condition would
# have to call back and Bend forbids mutual recursion.
def depth_for(fuel: Nat, +n: U32, +cap: U32, +d: Nat) -> Nat:
  match fuel:
    case 0n:
      d
    case 1n+p:
      +done = U32.is_gt(cap, n)
      depth_for(p, n, S.pick(done, cap, (cap * 2 : U32)),
                nat_pick(done, d, Succ{d}))
