import Base

def bump(z: Bool, acc: U32 & U32) -> U32 & U32:
  match z acc:
    case True{} Tuple{nb, nl}:
      ((nb + 1 : U32), (nl + 1 : U32))
    case False{} Tuple{nb, nl}:
      ((nb + 1 : U32), nl)

def tally(bs: List<&2, U32>, acc: U32 & U32) -> U32 & U32:
  match bs:
    case Nil{}:
      acc
    case Con{head, tail}:
      tally(tail, bump(U32.is_eq(head, 10), acc))

def unwrap(m: Maybe<&1, String>) -> String:
  match m:
    case None{}:
      ""
    case Some{value}:
      value

def drain(
  fuel: Nat,
  +chunk: U32,
  pr: File & Result<&1, &1, U32 & String, List<&2, U32>>,
  acc: U32 & U32,
) -> IO(U32 & U32):
  match fuel pr:
    case 0n Tuple{f, r}:
      do IO<U32 & U32>:
        File.close(f)
        IO.print_err("fuel exhausted")
        IO.pure(U32 & U32, acc)
    case 1n+p Tuple{f, r}:
      do IO<U32 & U32>:
        bs : List<&2, U32> <- IO.pass(List<&2, U32>, r)
        nxt : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, chunk)
        drain(p, chunk, nxt, tally(bs, acc))

def report(acc: U32 & U32) -> String:
  match acc:
    case Tuple{nb, nl}:
      "bytes " ++ U32.show(nb) ++ " lines " ++ U32.show(nl)

def main() -> IO(Unit):
  do IO<Unit>:
    av : List<&1, String> <- IO.args()
    path : String = unwrap(List.get(&1, String, av, 1n))
    +chunk : U32 = 1048576
    f : File <- IO.try(File, File.open(path, "r"))
    pr : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, chunk)
    acc : U32 & U32 <- drain(8192n, chunk, pr, (0, 0))
    IO.print(report(acc))
