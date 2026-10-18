# Prints one packed record-kind code per line of an export, newest line
# first. Checked against the same census computed in Python by
# tools/census-check.py: if every code agrees on every file, the scanner
# reads the format exactly.

import Base
import ./scan.bend as S

def show_codes(xs: List<&2, U32>, acc: String) -> String:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      show_codes(tail, U32.show(head) ++ "\n" ++ acc)

def unwrap_arg(m: Maybe<&1, String>) -> String:
  match m:
    case None{}:
      ""
    case Some{value}:
      value

def open_or_fail(r: Result<&1, &1, U32 & String, File>) -> IO(File):
  match r:
    case Fail{error}:
      match error:
        case Tuple{code, msg}:
          IO.die(File, 3, "cannot read input: " ++ msg)
    case Done{value}:
      IO.pure(File, value)

def main() -> IO(Unit):
  do IO<Unit>:
    av : List<&1, String> <- IO.args()
    path : String = unwrap_arg(List.get(&1, String, av, 1n))
    oh : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    f : File <- open_or_fail(oh)
    pr : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 16777216)
    bs : List<&2, U32> <- IO.pass(List<&2, U32>, Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, pr))
    IO.print(show_codes(S.scan(bs, S.Sc.start(), Nil{}), ""))
