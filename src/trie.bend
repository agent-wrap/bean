# An immutable index-to-value map that is `Data`, and therefore reusable.
#
# This is the piece that decides the shape of the whole kernel. `Array<T>` is
# a `Type`: it has exactly one owner, so every read hands the array back and a
# function that reads it twice must thread it through a helper -- and since
# Bend forbids mutual recursion, that helper cannot call back. That is what
# forces a kernel over Arrays to become an explicit stack machine.
#
# A trie built from ordinary constructors is `Data` when its values are, so a
# `+t: Tr<&2, A>` parameter can be read as often as a function likes. Ordinary
# recursive functions over the term graph become writable again.
#
# Keys are laid out as in a 4-ary heap: node k has children 4k+1 .. 4k+4, so
# descending from the root with key k > 0 moves into child (k-1) mod 4 with key
# (k-1) / 4. That is a bijection, so the trie is dense in the keys used and its
# depth is logarithmic -- 12 levels for the keys of a large export, where the
# binary layout copied and dropped 23 nodes per insertion (the recursor
# judging of init, trie-bound, took 40 of its 70 s of load).
#
# `get` carries the answer in an accumulator and descends into TNil rather than
# returning early, because returning early needs a helper that branches on the
# key and then calls back. Fuel bounds the descent at the key's bit width.

import Base

type Tr<-A: Data> is Data:
  TNil{}
  TNode{v: A, c0: Tr<A>, c1: Tr<A>, c2: Tr<A>, c3: Tr<A>}

def sub(-A: Data, +z: Bool, +x: Tr<A>, +y: Tr<A>) -> Tr<A>:
  match z:
    case True{}:
      x
    case False{}:
      y

def val(-A: Data, +z: Bool, +x: A, +y: A) -> A:
  match z:
    case True{}:
      x
    case False{}:
      y

# the child of index j (0..3)
def kid(-A: Data, +j: U32, +c0: Tr<A>, +c1: Tr<A>, +c2: Tr<A>,
        +c3: Tr<A>) -> Tr<A>:
  sub(A, U32.is_lt(j, 2), sub(A, U32.is_eq(j, 0), c0, c1),
      sub(A, U32.is_eq(j, 2), c2, c3))

def get(-A: Data, fuel: Nat, +t: Tr<A>, +k: U32, +acc: A) -> A:
  match fuel t:
    case 0n _:
      acc
    case 1n+p TNil{}:
      acc
    case 1n+p TNode{v, c0, c1, c2, c3}:
      +here = U32.is_eq(k, 0)
      +k1 = (k - 1 : U32)
      get(A, p,
          sub(A, here, TNil{}, kid(A, (k1 % 4 : U32), c0, c1, c2, c3)),
          (k1 / 4 : U32),
          val(A, here, v, acc))

# the node with child j replaced
def with(-A: Data, +j: U32, +v: A, +c0: Tr<A>, +c1: Tr<A>, +c2: Tr<A>,
         +c3: Tr<A>, +nc: Tr<A>) -> Tr<A>:
  +j2 : U32 = j
  +n2 : Tr<A> = nc
  TNode{v, sub(A, U32.is_eq(j2, 0), n2, c0), sub(A, U32.is_eq(j2, 1), n2, c1),
        sub(A, U32.is_eq(j2, 2), n2, c2), sub(A, U32.is_eq(j2, 3), n2, c3)}

def set(-A: Data, fuel: Nat, +t: Tr<A>, +k: U32, +x: A,
        +dflt: A) -> Tr<A>:
  match fuel t:
    case 0n _:
      TNil{}
    case 1n+p TNil{}:
      set(A, p, TNode{dflt, TNil{}, TNil{}, TNil{}, TNil{}}, k, x, dflt)
    case 1n+p TNode{v, c0, c1, c2, c3}:
      # Exactly one recursive call. Bend evaluates arguments strictly, so
      # putting a `set` in each branch of a choice would descend both sides
      # and cost 4^depth instead of depth.
      +here = U32.is_eq(k, 0)
      +k1 = (k - 1 : U32)
      +j = (k1 % 4 : U32)
      +p0 = c0
      +p1 = c1
      +p2 = c2
      +p3 = c3
      +pv = v
      +nc = set(A, p, kid(A, j, p0, p1, p2, p3), (k1 / 4 : U32), x, dflt)
      sub(A, here,
          TNode{x, p0, p1, p2, p3},
          with(A, j, pv, p0, p1, p2, p3, nc))

# a set only when `go`. `sub(go, set(..), t)` computes the set either way --
# arguments are strict -- which made every whole-export table pass pay a
# trie insertion per RECORD (init: 6.4M) instead of per relevant record
def set_if(-A: Data, +go: Bool, +t: Tr<A>, +k: U32, +x: A,
           +dflt: A) -> Tr<A>:
  match go:
    case True{}:
      set(A, 64n, t, k, x, dflt)
    case False{}:
      t
