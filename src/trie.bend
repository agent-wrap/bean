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
# Keys are laid out as in a binary heap: node k has children 2k+1 and 2k+2, so
# descending from the root with key k > 0 moves into child (k-1) mod 2 with key
# (k-1) / 2. That is a bijection, so the trie is dense in the keys used and its
# depth is logarithmic.
#
# `get` carries the answer in an accumulator and descends into TNil rather than
# returning early, because returning early needs a helper that branches on the
# key and then calls back. Fuel bounds the descent at the key's bit width.

import Base

type Tr<-A: Data> is Data:
  TNil{}
  TNode{v: A, l: Tr<A>, r: Tr<A>}

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

def get(-A: Data, fuel: Nat, +t: Tr<A>, +k: U32, +acc: A) -> A:
  match fuel t:
    case 0n _:
      acc
    case 1n+p TNil{}:
      acc
    case 1n+p TNode{v, l, r}:
      +here = U32.is_eq(k, 0)
      +k1 = (k - 1 : U32)
      get(A, p,
          sub(A, here, TNil{}, sub(A, U32.is_even(k1), l, r)),
          (k1 / 2 : U32),
          val(A, here, v, acc))

def set(-A: Data, fuel: Nat, +t: Tr<A>, +k: U32, +x: A,
        +dflt: A) -> Tr<A>:
  match fuel t:
    case 0n _:
      TNil{}
    case 1n+p TNil{}:
      set(A, p, TNode{dflt, TNil{}, TNil{}}, k, x, dflt)
    case 1n+p TNode{v, l, r}:
      # Exactly one recursive call. Bend evaluates arguments strictly, so
      # putting a `set` in each branch of a choice would descend both sides
      # and cost 2^depth instead of depth.
      +here = U32.is_eq(k, 0)
      +k1 = (k - 1 : U32)
      +goleft = U32.is_even(k1)
      +pl = l
      +pr = r
      +pv = v
      +nc = set(A, p, sub(A, goleft, pl, pr), (k1 / 2 : U32), x, dflt)
      sub(A, here,
          TNode{x, pl, pr},
          sub(A, goleft, TNode{pv, nc, pr}, TNode{pv, pl, nc}))
