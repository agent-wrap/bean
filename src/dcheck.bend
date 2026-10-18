# Prints each decoded record as
#   <kind> <index> <bi1> <bi2> |<payload string>| <int fields...>
# newest line last, for tools/decode-check.py to diff against the same thing
# computed with a real JSON parser.

import Base
import ./scan.bend as S
import ./decode.bend as D

def show_ints(xs: List<&2, U32>, acc: String) -> String:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      show_ints(tail, acc ++ " " ++ U32.show(head))

def show_flds(xs: List<&2, D.Fld>, acc: String) -> String:
  match xs:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case D.Fld{g, v, ob}:
          show_flds(tail, acc ++ " " ++ U32.show(g) ++ ":" ++ U32.show(v)
                          ++ "@" ++ U32.show(ob))

def show_rec(r: D.Rec) -> String:
  match r:
    case D.Rec{kind, ix, flds, b1, b2, sb}:
      # The payload is printed as byte values, not as text: Bend's String is a
      # sequence of codepoints and IO.print UTF-8-encodes it, so a raw UTF-8
      # byte would be encoded a second time.
      show_flds(flds,
        show_ints(sb,
          U32.show(kind) ++ " " ++ U32.show(ix) ++ " " ++ U32.show(b1) ++ " "
          ++ U32.show(b2) ++ " |") ++ " |")

def show_recs(rs: List<&2, D.Rec>, acc: String) -> String:
  match rs:
    case Nil{}:
      acc
    case Con{head, tail}:
      show_recs(tail, show_rec(head) ++ "\n" ++ acc)

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
    IO.print(show_recs(D.decode(bs, S.Sc.start(), D.Acc.start(), Nil{}), ""))
