# DEBUG ENTRY (not the checker): per-declaration verdicts of the flat
# checker. Prints: scans word (4294966272 + 16*pre + 4*consts + projs), then
# for each declaration: name_index*1024 (0 for inductive blocks) + 64*structural +
# typed_verdict + 16*incomplete + 32*corrupt (verdict 0/1/2, 3 = sentinel).
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
          IO.die(File, 3, "cannot read input (errno " ++ U32.show(code) ++ "): " ++ msg)
    case Done{value}:
      IO.pure(File, value)

# Pure: pull the record list out of a threaded decode triple.
def trip_out(trip: S.Sc & D.Acc & List<&2, D.Rec>) -> List<&2, D.Rec>:
  match trip:
    case Tuple{st, Tuple{acc, out}}:
      out

# Single self-recursive streaming reader, after bench/probe.bend's `drain`:
# the read-pair `pr` and the carried decode triple are PARAMETERS, so every
# match is on a field scrutinee and nothing is mutually recursive. Each step
# pulls one chunk, folds its bytes into the triple with `decode_resume` (an
# empty chunk folds to a no-op, so reads past EOF are harmless), drops the
# bytes, and reads the next chunk. `fuel` (1200 * 8 MB = 9.4 GB) bounds the
# step count; the file is consumed well before it, and the remaining steps are
# cheap empty reads. One chunk of bytes lives at a time -- no read-size cap,
# nothing to truncate, so no truncation guard.
def stream(fuel: Nat, +chunk: U32,
           pr: File & Result<&1, &1, U32 & String, List<&2, U32>>,
           trip: S.Sc & D.Acc & List<&2, D.Rec>) -> IO(List<&2, D.Rec>):
  match fuel pr trip:
    case 0n Tuple{f, r} Tuple{st, Tuple{acc, out}}:
      do IO<List<&2, D.Rec>>:
        bs : List<&2, U32> <- IO.pass(List<&2, U32>, r)
        File.close(f)
        IO.pure(List<&2, D.Rec>, trip_out(D.decode_resume(bs, st, acc, out)))
    case 1n+p Tuple{f, r} Tuple{st, Tuple{acc, out}}:
      do IO<List<&2, D.Rec>>:
        bs : List<&2, U32> <- IO.pass(List<&2, U32>, r)
        nxt : File & Result<&1, &1, U32 & String, List<&2, U32>>
          <- File.read_bytes(f, chunk)
        stream(p, chunk, nxt, D.decode_resume(bs, st, acc, out))


def vcode(+v: C.V) -> U32:
  match v:
    case C.VAccept{}:
      0
    case C.VReject{}:
      1
    case C.VDecline{}:
      2

# term dump for probes: preorder tokens of a node (fuel-bounded)
# App 1, Lam 2, Pi 3, Let 4, Proj 5 tn i, Const 6 n, BVar 7 i, Sort 8,
# Nat 9 value, Str 10, Bad 11
def dmp(fuel: Nat, pr: Array<T.Ex> & T.Ex, work: List<&2, U32>,
        acc: List<&2, U32>) -> Array<T.Ex> & List<&2, U32>:
  match fuel pr:
    case 0n Tuple{a, nd}:
      (a, acc)
    case 1n+p Tuple{a, nd}:
      match nd:
        case T.EApp{f, g}:
          dmp(p, Array.get(T.Ex, a, f), Con{g, work}, Con{1, acc})
        case T.ELam{n, t, b, bi}:
          dmp(p, Array.get(T.Ex, a, t), Con{b, work}, Con{2, acc})
        case T.EAll{n, t, b, bi}:
          dmp(p, Array.get(T.Ex, a, t), Con{b, work}, Con{3, acc})
        case T.ELet{n, t, v, b}:
          dmp(p, Array.get(T.Ex, a, t), Con{v, Con{b, work}}, Con{4, acc})
        case T.EProj{tn, i, sx}:
          dmp(p, Array.get(T.Ex, a, sx), work, Con{i, Con{tn, Con{5, acc}}})
        case T.EConst{n, us}:
          match work:
            case Nil{}:
              (a, Con{n, Con{6, acc}})
            case Con{h, t}:
              dmp(p, Array.get(T.Ex, a, h), t, Con{n, Con{6, acc}})
        case T.EBVar{i}:
          match work:
            case Nil{}:
              (a, Con{i, Con{7, acc}})
            case Con{h, t}:
              dmp(p, Array.get(T.Ex, a, h), t, Con{i, Con{7, acc}})
        case T.ESort{l}:
          match work:
            case Nil{}:
              (a, Con{8, acc})
            case Con{h, t}:
              dmp(p, Array.get(T.Ex, a, h), t, Con{8, acc})
        case T.ENat{d}:
          match work:
            case Nil{}:
              (a, Con{I.dec_u32(d, 0), Con{9, acc}})
            case Con{h, t}:
              dmp(p, Array.get(T.Ex, a, h), t, Con{I.dec_u32(d, 0), Con{9, acc}})
        case T.EStr{d}:
          match work:
            case Nil{}:
              (a, Con{10, acc})
            case Con{h, t}:
              dmp(p, Array.get(T.Ex, a, h), t, Con{10, acc})
        case _:
          match work:
            case Nil{}:
              (a, Con{11, acc})
            case Con{h, t}:
              dmp(p, Array.get(T.Ex, a, h), t, Con{11, acc})

def dmp2(pr: Array<T.Ex> & List<&2, U32>, +y: U32) -> Array<T.Ex> & List<&2, U32>:
  match pr:
    case Tuple{a, acc}:
      dmp(400n, Array.get(T.Ex, a, y), Nil{}, Con{4294966001, acc})

def dump_fin(pr: Array<T.Ex> & List<&2, U32>,
             +nx: U32) -> (Array<T.Ex> & U32) & List<&2, U32>:
  match pr:
    case Tuple{a, acc}:
      +n2 : U32 = nx
      ((a, n2), Con{4294966002, Con{n2, acc}})

# the two terms a probe recorded (keys 4294967288 / 4294967287), reversed
# token lists after a 4294966000 marker
def dump_pair(fs: Array<T.Ex> & U32, +x: U32,
              +y: U32) -> (Array<T.Ex> & U32) & List<&2, U32>:
  match fs:
    case Tuple{ex, nx}:
      dump_fin(dmp2(dmp(400n, Array.get(T.Ex, ex, x), Nil{},
                        Con{4294966000, Nil{}}), y), nx)

def dump_if(+z: Bool, fs: Array<T.Ex> & U32, +x: U32,
            +y: U32) -> (Array<T.Ex> & U32) & List<&2, U32>:
  match z:
    case True{}:
      dump_pair(fs, x, y)
    case False{}:
      (fs, Nil{})

# typed result code: verdict | 16*incomplete | 32*corrupt (before downgrade)
def dfold2(r: (Array<T.Ex> & U32) & List<&2, U32>,
           +c: U32) -> (Array<T.Ex> & U32) & List<&2, U32>:
  match r:
    case Tuple{fs, d}:
      (fs, Con{c, d})

def dfold(kr: ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>),
          +sv: C.V) -> (Array<T.Ex> & U32) & List<&2, U32>:
  match kr:
    case Tuple{Tuple{fs, v}, Tuple{lt, wm}}:
      +w2 : R.Tr<U32> = wm
      +cor : U32 = S.pick(U32.is_eq(R.get(U32, 64n, w2, 4294967291,
                                          4294967295), 4294967295), 0, 32)
      +inc : U32 = S.pick(U32.is_eq(R.get(U32, 64n, w2, 4294967292,
                                          4294967295), 4294967295), 0, 16)
      +v2 : U32 = v
      # probe breadcrumb (key 4294967290): its value replaces the code,
      # offset by 512 so it stays readable after the name*1024 packing
      +pr : U32 = R.get(U32, 64n, w2, 4294967290, 4294967295)
      +dx : U32 = R.get(U32, 64n, w2, 4294967288, 4294967295)
      +dy : U32 = R.get(U32, 64n, w2, 4294967287, 4294967295)
      dfold2(dump_if(Bool.not(U32.is_eq(dx, 4294967295)), fs, dx, dy),
             S.pick(U32.is_eq(pr, 4294967295),
                    (vcode(sv) * 64 + S.pick(U32.is_lt(v2, 3), v2, 3) + inc
                     + cor : U32),
                    (512 + pr : U32)))

def done(fs: Array<T.Ex> & U32, +c: U32) -> (Array<T.Ex> & U32) & List<&2, U32>:
  (fs, Con{c, Nil{}})

def fck_one_d(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
            +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +nmt: R.Tr<T.Nm>,
            +d: K.Dcl, +basenx: U32, +natn: U32, +qtt: R.Tr<U32>,
            fs: Array<T.Ex> & U32) -> (Array<T.Ex> & U32) & List<&2, U32>:
  match d fs:
    case K.DInd{nms, items} Tuple{ex, nx}:
      +its = items
      +ntb = B.add_items_nt(its, nt)
      done((ex, nx),
       (vcode(C.comb(C.comb(C.comb(C.ind_items(its, I.is_ex(st), nt, vt,
                                        C.VAccept{}),
                            C.ctor_all(its, I.is_ex(st),
                                       C.ind_names_of(its, Nil{}),
                                       C.VAccept{})),
                     C.block_rec_v(its, I.is_ex(st), I.is_lnt(st), ntb,
                                   lp)),
              C.comb(C.block_derive_v(its, st, mt, vt, I.is_lnt(st), ntb,
                                      lp),
                     C.block_names_v(its, nmt)))) * 64 : U32))
    case K.DNone{} Tuple{ex, nx}:
      done((ex, nx), 128)
    case _ Tuple{ex, nx}:
      +pd = d
      dfold(M.fck_typed(1000000000n, (ex, nx), I.is_lnt(st),
                           I.is_nlx(st), mt, lp, vt, qtt, natn, R.TNil{},
                           nt, K.dcl_is_theorem(pd), K.dcl_type(pd),
                           K.dcl_value(pd), basenx),
               C.self_ref_v(I.is_ex(st), pd))

# a declaration's code (labelled with its name) followed by any probe dump
def push_codes(+pn: U32, cl: List<&2, U32>,
               acc: List<&2, U32>) -> List<&2, U32>:
  match cl:
    case Nil{}:
      acc
    case Con{c, d}:
      Con{(pn * 1024 + c : U32), List.append(&2, U32, d, acc)}

def fck_all_d(ds: List<&2, K.Dcl>, +st: I.IS, +mt: R.Tr<I.Meta>,
            +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
            +nmt: R.Tr<T.Nm>, +basenx: U32, +natn: U32, +qtt: R.Tr<U32>,
            +i: U32, +pn: U32, acc: List<&2, U32>,
            fr: (Array<T.Ex> & U32) & List<&2, U32>) -> List<&2, U32>:
  match ds fr:
    case Nil{} Tuple{fs, c}:
      push_codes(pn, c, acc)
    case Con{head, tail} Tuple{fs, c}:
      +h = head
      fck_all_d(tail, st, mt, B.add_nt(h, nt), B.add_lp(h, lp),
              B.add_vt(h, vt), nmt, basenx, natn, qtt, (i + 1 : U32),
              K.dcl_name(h),
              # fr carries the PREVIOUS declaration's code: label it pn
              push_codes(pn, c, acc),
              fck_one_d(st, mt, nt, lp, vt, nmt, h, basenx, natn, qtt, fs))

def fjudge_d(+recs: List<&2, D.Rec>, +ds: List<&2, K.Dcl>, +nex: Nat,
           +nlv: Nat, +rounds: Nat, +nx: U32) -> List<&2, U32>:
  +ex = B.build_ex(recs, R.TNil{})
  +ln = B.lv_resolve(rounds, nlv, B.build_lv(recs, R.TNil{}), R.TNil{})
  +dn = C.mark_names(Con{0, C.declared(ds, Nil{})}, R.TNil{})
  +natn = K.find_name(recs, [78, 97, 116], 4294967295)
  +qtt = K.build_wk3(recs, R.TNil{})
  +st : I.IS = I.IS{ex, nx, ln, nx, R.TNil{}, K.build_ht(recs, R.TNil{}),
                    natn,
                    K.find_name(recs,
                                [83, 116, 114, 105, 110, 103],
                                4294967295),
                    qtt}
  +strt = C.build_str(ds, R.TNil{})
  Con{(4294966272 + vcode(C.pre_check(ds)) * 16
       + vcode(C.bad_v(C.scan_consts(nex, 0, ex, dn, False{}))) * 4
       + vcode(C.scan_projs(nex, 0, ex, strt, C.VAccept{})) : U32),
      fck_all_d(ds, st, C.build_meta(ds, ex, ln, R.TNil{}), R.TNil{},
                 R.TNil{}, R.TNil{}, K.build_nm(recs, R.TNil{}), nx,
                 natn, qtt, 0, 0, Nil{},
                 ((M.klb_init(U32.to_nat(nx), 0, M.khalf(nx),
                   F.fb_ex(recs,
                           Array.new(T.Ex, Nat.add(M.sdepth(nx), 1n),
                                     T.EBad{}))),
                   (nx + 1048576 : U32)), Con{0, Nil{}}))}

def show_all(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{head, tail}:
      U32.show(head) ++ " " ++ show_all(tail)

def judge_d(+recs: List<&2, D.Rec>) -> String:
  +nex = U32.to_nat((K.max_ex_ix(recs, 0) + 1 : U32))
  +nlv = U32.to_nat((K.max_lvl_ix(recs, 0) + 1 : U32))
  show_all(fjudge_d(recs, K.decls_of(recs, Nil{}), nex, nlv, 32n,
          (K.max_any_ix(recs, 0) + 1 : U32)))

def main() -> IO(Unit):
  do IO<Unit>:
    av : List<&1, String> <- IO.args()
    path : String = unwrap_arg(List.get(&1, String, av, 1n))
    oh : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    f : File <- open_or_fail(oh)
    pr : File & Result<&1, &1, U32 & String, List<&2, U32>>
      <- File.read_bytes(f, 8388608)
    recs : List<&2, D.Rec> <- stream(1200n, 8388608, pr,
      Tuple{S.Sc.start(), Tuple{D.Acc.start(), Nil{}}})
    IO.print(judge_d(recs))
