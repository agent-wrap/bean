# Can Bend's Array serve as the kernel's index-addressed store?
#
# The export hands out dense integer indices for every name, level and
# expression; Bend has no U64 and no hash map, so a pre-sized Array keyed by
# those indices is the only candidate store/memo address space. This measures
# the cost: allocation at depth d (2^d slots), a strided write pass, a read
# pass. Array is a persistent binary trie, so each access walks d levels, and
# at mathlib scale d is about 26.

import Base

def writes(n: Nat, +stride: U32, +i: U32, a: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+p:
      writes(p, stride, (i + stride : U32), Array.set(U32, a, i, i))

# The read's (array, value) pair arrives as a parameter: a match cannot
# scrutinise a computed value, and a helper that destructured it would have to
# call `reads` back, which Bend forbids.
def reads(n: Nat, +stride: U32, +i: U32, +acc: U32,
          r: Array<U32> & U32) -> Array<U32> & U32:
  match n r:
    case 0n Tuple{a, v}:
      (a, (acc + v : U32))
    case 1n+p Tuple{a, v}:
      reads(p, stride, (i + stride : U32), (acc + v : U32),
            Array.get(U32, a, i))

def total(r: Array<U32> & U32) -> U32:
  match r:
    case Tuple{a, acc}:
      acc

def run(d: Nat, +n: Nat, +stride: U32) -> U32:
  total(reads(n, stride, stride, 0,
              Array.get(U32, writes(n, stride, 0, Array.new(U32, d, 0)), 0)))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("d26 n60000000: " ++ U32.show(run(26n, 60000000n, 7)))
