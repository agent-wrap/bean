# Prototype of the flat-store kernel machine shape:
#   one recursive def, Data frame stack, affine Arrays threaded in a state
#   tuple, every Array.get result re-entering via a parameter.
import Base

type Fr is Data:
  FGet{i: U32}     # reg := A[i]
  FPut{i: U32}     # B[i] := 2*reg
  FSum{i: U32}     # acc += B[i]

type Kstk is Data:
  KNil{}
  KCon{f: Fr, k: Kstk}

# --- state shufflers (pure, defined above the machine) -------------------
# State: ((A & B) & (reg & acc))
def ld_a(r: Array<U32> & U32, b: Array<U32>,
         +acc: U32) -> (Array<U32> & Array<U32>) & (U32 & U32):
  match r:
    case Tuple{a, v}:
      ((a, b), (v, acc))

def ld_b(r: Array<U32> & U32, a: Array<U32>, +reg: U32,
         +acc: U32) -> (Array<U32> & Array<U32>) & (U32 & U32):
  match r:
    case Tuple{b, v}:
      ((a, b), (reg, (acc + v : U32)))

def st_b(b: Array<U32>, a: Array<U32>, +i: U32, +reg: U32,
         +acc: U32) -> (Array<U32> & Array<U32>) & (U32 & U32):
  ((a, Array.set(U32, b, i, (reg * 2 : U32))), (reg, acc))

# --- the machine ----------------------------------------------------------
def mach(fuel: Nat, +stk: Kstk,
         st: (Array<U32> & Array<U32>) & (U32 & U32)) -> U32:
  match fuel stk st:
    case 0n _ _:
      4294967295
    case 1n+p KNil{} Tuple{arrs, Tuple{reg, acc}}:
      acc
    case 1n+p KCon{FGet{i}, k} Tuple{Tuple{a, b}, Tuple{reg, acc}}:
      mach(p, k, ld_a(Array.get(U32, a, i), b, acc))
    case 1n+p KCon{FPut{i}, k} Tuple{Tuple{a, b}, Tuple{reg, acc}}:
      mach(p, k, st_b(b, a, i, reg, acc))
    case 1n+p KCon{FSum{i}, k} Tuple{Tuple{a, b}, Tuple{reg, acc}}:
      mach(p, k, ld_b(Array.get(U32, b, i), a, reg, acc))

# --- program builder: for i in 0..n: reg:=A[i]; B[i]:=2reg; acc+=B[i] -----
def prog(n: Nat, +i: U32, +k: Kstk) -> Kstk:
  match n:
    case 0n:
      k
    case 1n+p:
      prog(p, (i + 1 : U32),
           KCon{FGet{i}, KCon{FPut{i}, KCon{FSum{i}, k}}})

def seed(n: Nat, +i: U32, a: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+p:
      seed(p, (i + 1 : U32), Array.set(U32, a, i, i))

def main() -> IO(Unit):
  do IO<Unit>:
    # n=2M: expected acc = 2 * sum(0..n-1) = n*(n-1) mod 2^32
    IO.print("mach n2M: " ++ U32.show(
      mach(99999999n, prog(2000000n, 0, KNil{}),
           ((seed(2000000n, 0, Array.new(U32, 21n, 0)),
             Array.new(U32, 21n, 0)), (0, 0)))))
