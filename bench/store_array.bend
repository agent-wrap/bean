# Head-to-head: Data trie (src/trie.bend copy) vs flat Array, same workload.
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

def tget(-A: Data, fuel: Nat, +t: Tr<A>, +k: U32, +acc: A) -> A:
  match fuel t:
    case 0n _:
      acc
    case 1n+p TNil{}:
      acc
    case 1n+p TNode{v, l, r}:
      +here = U32.is_eq(k, 0)
      +k1 = (k - 1 : U32)
      tget(A, p,
          sub(A, here, TNil{}, sub(A, U32.is_even(k1), l, r)),
          (k1 / 2 : U32),
          val(A, here, v, acc))

def tset(-A: Data, fuel: Nat, +t: Tr<A>, +k: U32, +x: A,
        +dflt: A) -> Tr<A>:
  match fuel t:
    case 0n _:
      TNil{}
    case 1n+p TNil{}:
      tset(A, p, TNode{dflt, TNil{}, TNil{}}, k, x, dflt)
    case 1n+p TNode{v, l, r}:
      +here = U32.is_eq(k, 0)
      +k1 = (k - 1 : U32)
      +goleft = U32.is_even(k1)
      +pl = l
      +pr = r
      +pv = v
      +nc = tset(A, p, sub(A, goleft, pl, pr), (k1 / 2 : U32), x, dflt)
      sub(A, here,
          TNode{x, pl, pr},
          sub(A, goleft, TNode{pv, nc, pr}, TNode{pv, pl, nc}))

# write pass then read pass over the trie, stride 7 in a 2^22 key space
def twrites(n: Nat, +stride: U32, +i: U32, +t: Tr<U32>) -> Tr<U32>:
  match n:
    case 0n:
      t
    case 1n+p:
      twrites(p, stride, ((i + stride : U32) % 4194304 : U32),
              tset(U32, 32n, t, i, i, 0))

def treads(n: Nat, +stride: U32, +i: U32, +acc: U32, +t: Tr<U32>) -> U32:
  match n:
    case 0n:
      acc
    case 1n+p:
      treads(p, stride, ((i + stride : U32) % 4194304 : U32),
             (acc + tget(U32, 32n, t, i, 0) : U32), t)

def trun(+n: Nat, +stride: U32) -> U32:
  treads(n, stride, 0, 0, twrites(n, stride, 0, TNil{}))

# same workload on the flat Array, threaded
def awrites(n: Nat, +stride: U32, +i: U32, a: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+p:
      awrites(p, stride, ((i + stride : U32) % 4194304 : U32),
              Array.set(U32, a, i, i))

def areads(n: Nat, +stride: U32, +i: U32, +acc: U32,
           r: Array<U32> & U32) -> Array<U32> & U32:
  match n r:
    case 0n Tuple{a, v}:
      (a, (acc + v : U32))
    case 1n+p Tuple{a, v}:
      areads(p, stride, ((i + stride : U32) % 4194304 : U32), (acc + v : U32),
             Array.get(U32, a, i))

def atotal(r: Array<U32> & U32) -> U32:
  match r:
    case Tuple{a, acc}:
      acc

def arun(+n: Nat, +stride: U32) -> U32:
  atotal(areads(n, stride, 0, 0,
                Array.get(U32, awrites(n, stride, 0, Array.new(U32, 22n, 0)), 0)))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("array n4M: " ++ U32.show(arun(4000000n, 7)))
