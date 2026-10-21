# Per-declaration differential: check.bend's ck_typed (trie) against the
# machine's fck_typed, walking the declarations with identical incremental
# environments. Prints the first diverging declaration and both verdicts.
import Base
import ./scan.bend as S
import ./decode.bend as D
import ./term.bend as T
import ./level.bend as L
import ./store.bend as K
import ./trie.bend as R
import ./tables.bend as B
import ./subst.bend as U
import ./infer.bend as I
import ./check.bend as C
import ./fstore.bend as F
import ./km.bend as M

def v_u32(+v: C.V) -> U32:
  match v:
    case C.VAccept{}:
      0
    case C.VReject{}:
      1
    case C.VDecline{}:
      2

def fkd_fold(kr: ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>))
    -> (Array<T.Ex> & U32) & U32:
  match kr:
    case Tuple{Tuple{fs, v}, lv}:
      (fs, v)

def is_typed(+d: K.Dcl) -> Bool:
  match d:
    case K.DInd{nms, items}:
      False{}
    case K.DNone{}:
      False{}
    case _:
      True{}

def refs(fs: Array<T.Ex> & U32, +basenx: U32) -> Array<T.Ex> & U32:
  match fs:
    case Tuple{ex, nx}:
      (ex, (basenx + 65536 : U32))

# one pipelined loop: the machine verdict of declaration i arrives at
# iteration i+1 through `fr` and is compared against the trie verdict saved
# at iteration i
def fkd(ds: List<&2, K.Dcl>, +n: U32, +st: I.IS, +mt: R.Tr<I.Meta>,
        +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
        +basenx: U32, +natn: U32, +qtt: R.Tr<U32>, +bad: U32, +fb: U32,
        +fbv: U32, +tbv: U32, +ptyv: U32, +pran: Bool,
        fr: (Array<T.Ex> & U32) & U32) -> String:
  match ds fr:
    case Nil{} Tuple{fs, mv}:
      +m2 : U32 = mv
      +miss : Bool = pran && Bool.not(U32.is_eq(m2, ptyv))
      +isf : Bool = U32.is_eq(fb, 4294967295)
      "ckdiff bad " ++ U32.show((bad + S.pick(miss, 1, 0) : U32))
      ++ " first " ++ U32.show(S.pick(miss && isf, (n - 1 : U32), fb))
      ++ " fbean " ++ U32.show(S.pick(miss && isf, m2, fbv))
      ++ " bean " ++ U32.show(S.pick(miss && isf, ptyv, tbv))
    case Con{head, tail} Tuple{fs, mv}:
      +h = head
      +h2 = h
      +ist : Bool = is_typed(h2)
      +m2 : U32 = mv
      +miss : Bool = pran && Bool.not(U32.is_eq(m2, ptyv))
      +isf : Bool = U32.is_eq(fb, 4294967295)
      +tyv : U32 = S.pick(ist,
                          v_u32(C.ck_typed(8192n, st, mt, nt, lp, vt,
                                           K.dcl_is_theorem(h2),
                                           K.dcl_type(h2),
                                           K.dcl_value(h2))),
                          0)
      fkd(tail, (n + 1 : U32), st, mt, B.add_nt(h2, nt),
          B.add_lp(h2, lp), B.add_vt(h2, vt), basenx, natn, qtt,
          (bad + S.pick(miss, 1, 0) : U32),
          S.pick(miss && isf, (n - 1 : U32), fb),
          S.pick(miss && isf, m2, fbv),
          S.pick(miss && isf, ptyv, tbv), tyv, ist,
          fkd_fold(M.fck_typed(1000000000n, refs(fs, basenx),
                               I.is_lnt(st), I.is_nlx(st), mt, lp, vt,
                               qtt, natn, R.TNil{}, nt,
                               K.dcl_is_theorem(h2),
                               S.pick(ist, K.dcl_type(h2), 4294967295),
                               S.pick(ist, K.dcl_value(h2),
                                      4294967295), basenx)))

def fjd(+recs: List<&2, D.Rec>) -> String:
  +ds = K.decls_of(recs, Nil{})
  +nex = U32.to_nat((K.max_ex_ix(recs, 0) + 1 : U32))
  +nlv = U32.to_nat((K.max_lvl_ix(recs, 0) + 1 : U32))
  +nx = (K.max_any_ix(recs, 0) + 1 : U32)
  +ex = B.build_ex(recs, R.TNil{})
  +ln = B.lv_resolve(32n, nlv, B.build_lv(recs, R.TNil{}), R.TNil{})
  +natn = K.find_name(recs, [78, 97, 116], 4294967295)
  +qtt = K.build_wk2(recs, R.TNil{})
  +st : I.IS = I.IS{ex, nx, ln, nx, R.TNil{}, K.build_ht(recs, R.TNil{}),
                    natn,
                    K.find_name(recs, [83, 116, 114, 105, 110, 103],
                                4294967295), qtt}
  fkd(ds, 0, st, C.build_meta(ds, ex, ln, R.TNil{}), R.TNil{}, R.TNil{},
      R.TNil{}, nx, natn, qtt, 0, 4294967295, 9, 9, 0, False{},
      ((F.fb_ex(recs, Array.new(T.Ex, Nat.add(F.fdepth((nx + 131072 : U32)), 1n),
                                T.EBad{})), nx), 0))

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
    pr : File & Result<&1, &1, U32 & String, List<&2, U32>>
      <- File.read_bytes(f, 33554432)
    bs : List<&2, U32> <- IO.pass(List<&2, U32>,
      Pair.snd(File, Result<&1, &1, U32 & String, List<&2, U32>>, pr))
    IO.print(fjd(D.decode(bs, S.Sc.start(), D.Acc.start(), Nil{})))
