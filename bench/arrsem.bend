# Probe: what does Array.new(T, n, d) allocate, and what do get/set do out
# of range? km's expression store relies on this.
import Base

def cat2(pr: Array<U32> & U32, +s: String) -> Array<U32> & String:
  match pr:
    case Tuple{a, v}:
      (a, s ++ U32.show(v) ++ " ")

def g(pr: Array<U32> & U32, +i: U32) -> Array<U32> & String:
  match pr:
    case Tuple{a, v}:
      +s : String = U32.show(v) ++ " "
      cat2(Array.get(U32, a, i), s)

def fin2(pr: Array<U32> & U32, +s: String) -> String:
  match pr:
    case Tuple{a, v}:
      s ++ U32.show(v)

def fin(pr: Array<U32> & String, +i: U32) -> String:
  match pr:
    case Tuple{a, s}:
      fin2(Array.get(U32, a, i), s)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("new(3n,5) set100=1000 then get 4 | 36 | 100: "
      ++ fin(g(Array.get(U32, Array.set(U32, Array.new(U32, 3n, 5), 100, 1000), 4), 36), 100))
    IO.print("new(3n,5) set4=44 then get 100 | 12 | 4: "
      ++ fin(g(Array.get(U32, Array.set(U32, Array.new(U32, 3n, 5), 4, 44), 100), 12), 4))
