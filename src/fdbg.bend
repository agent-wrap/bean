# DEBUG ENTRY (not the checker): per-declaration verdicts of the flat
# checker. Prints: scans word (4294966272 + 16*pre + 4*consts + projs), then
# for each declaration: name_index*1024 (0 for inductive blocks; their low
# bits are the structural parts, see fck_one_d) + 64*structural +
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
import ./fcheck.bend as FC

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
# a constant's level ids after its name: `l, 15` pairs (the level pass
# prints them as LV lines like a Sort's), closed by 16
def dmp_us(us: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match us:
    case Nil{}:
      Con{16, acc}
    case Con{h, t}:
      dmp_us(t, Con{h, Con{15, acc}})

def dmp(fuel: Nat, pr: Array<T.Ex> & T.Ex, work: List<&2, U32>,
        acc: List<&2, U32>, +lt: R.Tr<L.LN>) -> Array<T.Ex> & List<&2, U32>:
  match fuel pr:
    case 0n Tuple{a, nd}:
      (a, acc)
    case 1n+p Tuple{a, nd}:
      match nd:
        case T.EApp{f, g}:
          dmp(p, Array.get(T.Ex, a, f), Con{g, work}, Con{1, acc}, lt)
        case T.ELam{n, t, b, bi}:
          dmp(p, Array.get(T.Ex, a, t), Con{b, work}, Con{2, acc}, lt)
        case T.EAll{n, t, b, bi}:
          dmp(p, Array.get(T.Ex, a, t), Con{b, work}, Con{3, acc}, lt)
        case T.ELet{n, t, v, b}:
          dmp(p, Array.get(T.Ex, a, t), Con{v, Con{b, work}}, Con{4, acc}, lt)
        case T.EProj{tn, i, sx}:
          dmp(p, Array.get(T.Ex, a, sx), work, Con{i, Con{tn, Con{5, acc}}}, lt)
        case T.EConst{n, us}:
          match work:
            case Nil{}:
              (a, dmp_us(L.lst_get(lt, us), Con{n, Con{6, acc}}))
            case Con{h, t}:
              dmp(p, Array.get(T.Ex, a, h), t, dmp_us(L.lst_get(lt, us), Con{n, Con{6, acc}}), lt)
        case T.EBVar{i}:
          match work:
            case Nil{}:
              (a, Con{i, Con{7, acc}})
            case Con{h, t}:
              dmp(p, Array.get(T.Ex, a, h), t, Con{i, Con{7, acc}}, lt)
        case T.ESort{l}:
          match work:
            case Nil{}:
              (a, Con{l, Con{12, acc}})
            case Con{h, t}:
              dmp(p, Array.get(T.Ex, a, h), t, Con{l, Con{12, acc}}, lt)
        case T.ENat{d}:
          match work:
            case Nil{}:
              (a, Con{I.dec_u32(L.lst_get(lt, d), 0), Con{9, acc}})
            case Con{h, t}:
              dmp(p, Array.get(T.Ex, a, h), t, Con{I.dec_u32(L.lst_get(lt, d), 0), Con{9, acc}}, lt)
        case T.EStr{d}:
          match work:
            case Nil{}:
              (a, Con{10, acc})
            case Con{h, t}:
              dmp(p, Array.get(T.Ex, a, h), t, Con{10, acc}, lt)
        case _:
          match work:
            case Nil{}:
              (a, Con{11, acc})
            case Con{h, t}:
              dmp(p, Array.get(T.Ex, a, h), t, Con{11, acc}, lt)

def dmp2(pr: Array<T.Ex> & List<&2, U32>, +y: U32,
         +lt: R.Tr<L.LN>) -> Array<T.Ex> & List<&2, U32>:
  match pr:
    case Tuple{a, acc}:
      dmp(400n, Array.get(T.Ex, a, y), Nil{}, Con{4294966001, acc}, lt)

# the levels of the Sort nodes in a dump (tokens `l, 12`), as records
# 13 l <level> after a 4294966003 marker: level tokens 30 unknown, 31
# symbolic, 32 n (base off)*n a max of atoms, 33 off <a> <b> an imax,
# 34 n (base off)*n <y> <r> a mixed chain
def lnser_atoms(xs: List<&2, L.Atom>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{L.At{b, o}, t}:
      lnser_atoms(t, Con{o, Con{b, acc}})

def lnlen(xs: List<&2, L.Atom>, +n: U32) -> U32:
  match xs:
    case Nil{}:
      n
    case Con{h, t}:
      lnlen(t, (n + 1 : U32))

def lnser(fuel: Nat, l: L.LN, acc: List<&2, U32>) -> List<&2, U32>:
  match fuel l:
    case 0n _:
      Con{35, acc}
    case 1n+p L.LNun{}:
      Con{30, acc}
    case 1n+p L.LNsym{}:
      Con{31, acc}
    case 1n+p L.LNmax{xs}:
      +xs2 : List<&2, L.Atom> = xs
      lnser_atoms(xs2, Con{lnlen(xs2, 0), Con{32, acc}})
    case 1n+p L.LNimax{a, b, off}:
      +p2 : Nat = p
      lnser(p2, b, lnser(p2, a, Con{off, Con{33, acc}}))
    case 1n+p L.LNmx{xs, y, r}:
      +p2 : Nat = p
      +xs2 : List<&2, L.Atom> = xs
      lnser(p2, r, lnser(p2, y, lnser_atoms(xs2, Con{lnlen(xs2, 0), Con{34, acc}})))
    case 1n+p L.LNlst{xs}:
      Con{36, acc}

def lvl_rec1(+go: Bool, +a: U32, +lt: R.Tr<L.LN>,
             acc: List<&2, U32>) -> List<&2, U32>:
  match go:
    case True{}:
      lnser(64n, R.get(L.LN, 64n, lt, a, L.LNun{}), Con{a, Con{13, acc}})
    case False{}:
      acc

def lvl_recs(toks: List<&2, U32>, +lt: R.Tr<L.LN>,
             acc: List<&2, U32>) -> List<&2, U32>:
  match toks:
    case Con{a, Con{b, rest}}:
      +a2 : U32 = a
      +b2 : U32 = b
      +lt2 : R.Tr<L.LN> = lt
      lvl_recs(Con{b2, rest}, lt2, lvl_rec1(U32.is_eq(b2, 12) || U32.is_eq(b2, 15), a2, lt2, acc))
    case _:
      acc

def lvl_pass(pr: Array<T.Ex> & List<&2, U32>,
             +lt: R.Tr<L.LN>) -> Array<T.Ex> & List<&2, U32>:
  match pr:
    case Tuple{a, acc}:
      +acc2 : List<&2, U32> = acc
      (a, lvl_recs(acc2, lt, Con{4294966003, acc2}))

def dump_fin(pr: Array<T.Ex> & List<&2, U32>,
             +nx: U32) -> (Array<T.Ex> & U32) & List<&2, U32>:
  match pr:
    case Tuple{a, acc}:
      +n2 : U32 = nx
      ((a, n2), Con{4294966002, Con{n2, acc}})

# the two terms a probe recorded (keys 4294967288 / 4294967287), reversed
# token lists after a 4294966000 marker
def dump_pair(fs: Array<T.Ex> & U32, +x: U32,
              +y: U32, +lt: R.Tr<L.LN>) -> (Array<T.Ex> & U32) & List<&2, U32>:
  match fs:
    case Tuple{ex, nx}:
      +x2 : U32 = x
      +y2 : U32 = y
      dump_fin(lvl_pass(dmp2(dmp(400n, Array.get(T.Ex, ex, x2), Nil{},
                                 Con{y2, Con{x2, Con{4294966000, Nil{}}}}, lt),
                             y2, lt),
                        lt), nx)

def dump_if(+z: Bool, fs: Array<T.Ex> & U32, +x: U32,
            +y: U32, +lt: R.Tr<L.LN>) -> (Array<T.Ex> & U32) & List<&2, U32>:
  match z:
    case True{}:
      dump_pair(fs, x, y, lt)
    case False{}:
      (fs, Nil{})

# typed result code: verdict | 16*incomplete | 32*corrupt (before downgrade)
def dfold2(r: (Array<T.Ex> & U32) & List<&2, U32>,
           +c: U32) -> (Array<T.Ex> & U32) & List<&2, U32>:
  match r:
    case Tuple{fs, d}:
      (fs, Con{c, d})

def kpb2(+none: Bool, +pb: U32, d: List<&2, U32>) -> List<&2, U32>:
  match none:
    case True{}:
      d
    case False{}:
      Con{4294966003, Con{pb, d}}

def kpb(+pb: U32, d: List<&2, U32>) -> List<&2, U32>:
  kpb2(U32.is_eq(pb, 4294967295), pb, d)

# the older event register (key 4294967286) after the code, if set
def dfold3(+pb: U32, r: (Array<T.Ex> & U32) & List<&2, U32>,
           +c: U32) -> (Array<T.Ex> & U32) & List<&2, U32>:
  match r:
    case Tuple{fs, d}:
      (fs, Con{c, kpb(pb, d)})

def dfoldF(pr: Array<T.Ex> & U32, +nx: U32, +v: U32, +wm: R.Tr<U32>,
           +sv: C.V, +base: U32, +lt: R.Tr<L.LN>) -> (Array<T.Ex> & U32) & List<&2, U32>:
  match pr:
    case Tuple{ex, fl}:
      +w2 : R.Tr<U32> = wm
      +f2 : U32 = fl
      +cor : U32 = S.pick(U32.is_eq(U32.and(f2, 2), 0), 0, 32)
      +inc : U32 = S.pick(U32.is_eq(U32.and(f2, 4), 0), 0, 16)
      +v2 : U32 = v
      # probe breadcrumb (key 4294967290): its value replaces the code,
      # offset by 512 so it stays readable after the name*1024 packing
      +pr2 : U32 = R.get(U32, 64n, w2, 4294967290, 4294967295)
      +nxf : U32 = nx
      +ovf : Bool = U32.is_ge(nxf, M.khalf(base))
      +dx : U32 = R.get(U32, 64n, w2, 4294967288, 4294967295)
      +dy : U32 = R.get(U32, 64n, w2, 4294967287, 4294967295)
      +pb : U32 = R.get(U32, 64n, w2, 4294967286, 4294967295)
      dfold3(pb, dump_if(Bool.not(U32.is_eq(dx, 4294967295)), (ex, nxf),
                         dx, dy, lt),
             S.pick(U32.is_eq(pr2, 4294967295),
                    (vcode(sv) * 64 + S.pick(U32.is_lt(v2, 3), v2, 3) + inc
                     + cor + S.pick(ovf, 256, 0) : U32),
                    (512 + pr2 : U32)))

def dfold(kr: ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>),
          +sv: C.V, +base: U32) -> (Array<T.Ex> & U32) & List<&2, U32>:
  match kr:
    case Tuple{Tuple{Tuple{ex, nx}, v}, Tuple{Tuple{lt, nl}, wm}}:
      dfoldF(M.kfl_flags(ex, base), nx, v, wm, sv, base, lt)

def done(fs: Array<T.Ex> & U32, +c: U32) -> (Array<T.Ex> & U32) & List<&2, U32>:
  (fs, Con{c, Nil{}})

def krestart(fs: Array<T.Ex> & U32, +basenx: U32) -> Array<T.Ex> & U32:
  match fs:
    case Tuple{ex, nx}:
      (M.kbump_n(ex, basenx, (nx - (basenx + M.ktbl(basenx) + 2 : U32) : U32)),
       (basenx + M.ktbl(basenx) + 2 : U32))

def fck_one_d(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
            +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +nmt: R.Tr<T.Nm>,
            +d: K.Dcl, +basenx: U32, +natn: U32, +qtt: R.Tr<U32>,
            fs: Array<T.Ex> & U32) -> (Array<T.Ex> & U32) & List<&2, U32>:
  match d fs:
    case K.DInd{nms, items} Tuple{ex, nx}:
      +its = items
      +ntb = B.add_items_nt(its, nt)
      # an inductive block: its structural parts, two bits each --
      # items + 4 ctors + 16 recursors + 64 derivation + 256 names
      # (the mutual/nested path: recursors and derivation are its verdict)
      done((ex, nx),
       (vcode(C.ind_items(its, I.is_ex(st), nt, vt, C.VAccept{}))
        + vcode(C.ctor_all(its, I.is_ex(st), C.ind_names_of(its, Nil{}),
                           C.VAccept{})) * 4
        + vcode(C.block_rec_v(its, I.is_ex(st), I.is_lnt(st), ntb, lp, C.fo_off(I.is_ex(st), I.is_lnt(st)))) * 16
        + vcode(C.derive_or_ver(its, st, mt, vt, I.is_lnt(st), ntb, lp)) * 64
        + vcode(C.block_names_v(its, nmt)) * 256 : U32))
    case K.DNone{} Tuple{ex, nx}:
      done((ex, nx), 128)
    case _ Tuple{ex, nx}:
      +pd = d
      dfold(M.fck_typed(1000000000n, (ex, nx), I.is_lnt(st),
                           I.is_nlx(st), mt, lp, vt, qtt, natn, R.TNil{},
                           nt, K.dcl_is_theorem(pd), K.dcl_type(pd),
                           K.dcl_value(pd), basenx),
               C.self_ref_v(I.is_ex(st), pd), basenx)

# a declaration's code (labelled with its name) followed by any probe dump
def push_codes(+pn: U32, cl: List<&2, U32>,
               acc: List<&2, U32>) -> List<&2, U32>:
  match cl:
    case Nil{}:
      acc
    case Con{c, d}:
      Con{(pn * 1024 + c : U32), List.append(&2, U32, d, acc)}

# argv[2] (optional): check only the declaration of that index (fmain's
# `K N` numbering), every other one is entered as trusted -- a probe on one
# declaration of a large slice without checking its prerequisites
def fck_one_sel(+go: Bool, +st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
                +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +nmt: R.Tr<T.Nm>,
                +d: K.Dcl, +basenx: U32, +natn: U32, +qtt: R.Tr<U32>,
                fs: Array<T.Ex> & U32) -> (Array<T.Ex> & U32) & List<&2, U32>:
  match go:
    case True{}:
      fck_one_d(st, mt, nt, lp, vt, nmt, d, basenx, natn, qtt, fs)
    case False{}:
      (fs, Nil{})

def fck_all_d(ds: List<&2, K.Dcl>, +st: I.IS, +mt: R.Tr<I.Meta>,
            +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
            +nmt: R.Tr<T.Nm>, +basenx: U32, +natn: U32, +qtt: R.Tr<U32>,
            +i: U32, +pn: U32, +only: U32, acc: List<&2, U32>,
            fr: (Array<T.Ex> & U32) & List<&2, U32>) -> List<&2, U32>:
  match ds fr:
    case Nil{} Tuple{fs, c}:
      push_codes(pn, c, acc)
    case Con{head, tail} Tuple{fs, c}:
      +h = head
      +i2 : U32 = i
      +o2 : U32 = only
      fck_all_d(tail, st, mt, B.add_nt(h, nt), B.add_lp(h, lp),
              B.add_vt(h, vt), nmt, basenx, natn, qtt, (i2 + 1 : U32),
              K.dcl_name(h), o2,
              # fr carries the PREVIOUS declaration's code: label it pn
              push_codes(pn, c, acc),
              fck_one_sel(U32.is_eq(o2, 4294967295) || U32.is_eq(i2, o2),
                          st, mt, nt, lp, vt, nmt, h, basenx, natn, qtt,
                          krestart(fs, basenx)))

def fjudge_d3(arr: Array<T.Ex>, +ex: R.Tr<T.Ex>, +lt: R.Tr<L.LN>,
              +recs: List<&2, D.Rec>, +ds: List<&2, K.Dcl>, +nex: Nat,
              +nlv: Nat, +rounds: Nat, +nx: U32,
              +only: U32) -> List<&2, U32>:
  +ln = M.klv_seed(nlv, 0, B.lv_resolve(rounds, nlv, B.build_lv(recs, R.TNil{}),
                                       lt))
  +dn = C.mark_names(Con{0, C.declared(ds, Nil{})}, R.TNil{})
  # Nat (key 20) and String (key 10) come from build_wk4's two passes
  +wk = K.build_wk4(recs, R.TNil{})
  +natn : U32 = R.get(U32, 64n, wk, 20, 4294967295)
  +strn : U32 = R.get(U32, 64n, wk, 10, 4294967295)
  +qtt = K.add_hts(recs, wk)
  +st : I.IS = I.IS{ex, nx, ln, nx, R.TNil{}, K.build_ht(recs, R.TNil{}),
                    natn, strn, qtt}
  +strt = C.build_str(ds, R.TNil{})
  Con{(4294966272 + vcode(C.pre_check(ds)) * 16
       + vcode(C.bad_v(C.scan_consts(nex, 0, ex, dn, False{}))) * 4
       + vcode(C.scan_projs(nex, 0, ex, strt, C.VAccept{})) : U32),
      fck_all_d(ds, st, C.build_meta2(ds, st, R.TNil{}, R.TNil{}, R.TNil{},
                                      R.TNil{},
                                      [I.is_qt(st, 16), I.is_qt(st, 17),
                                       I.is_qt(st, 18), I.is_qt(st, 19)], R.TNil{}, R.TNil{}, 0, 0, 1),
                R.TNil{},
                 R.TNil{}, R.TNil{}, K.build_nm(recs, R.TNil{}), nx,
                 natn, qtt, 0, 0, only, Nil{},
                 ((arr, (nx + M.ktbl(nx) + 2 : U32)), Con{0, Nil{}}))}

def fjudge_d2(ab: Array<T.Ex> & R.Tr<T.Ex>, +lt: R.Tr<L.LN>,
              +recs: List<&2, D.Rec>, +ds: List<&2, K.Dcl>, +nex: Nat,
              +nlv: Nat, +rounds: Nat, +nx: U32,
              +only: U32) -> List<&2, U32>:
  match ab:
    case Tuple{arr, ex}:
      fjudge_d3(arr, ex, lt, recs, ds, nex, nlv, rounds, nx, only)

def fjudge_d1(r: Array<T.Ex> & R.Tr<L.LN>, +recs: List<&2, D.Rec>,
              +ds: List<&2, K.Dcl>, +nex: Nat, +nlv: Nat, +rounds: Nat,
              +nx: U32, +only: U32) -> List<&2, U32>:
  match r:
    case Tuple{arr, lt}:
      fjudge_d2(FC.fj_abA(arr, nx), lt, recs, ds, nex, nlv, rounds, nx, only)

# the records routed as fmain routes them (FC.fj_rt: the lists interned),
# the structural checks' expression trie rebuilt from the store
def fjudge_d(+recs: List<&2, D.Rec>, +ds: List<&2, K.Dcl>, +nex: Nat,
           +nlv: Nat, +rounds: Nat, +nx: U32, +only: U32) -> List<&2, U32>:
  fjudge_d1(FC.fj_rt(recs, nx), recs, ds, nex, nlv, rounds, nx, only)

def show_all(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{head, tail}:
      U32.show(head) ++ " " ++ show_all(tail)

def d_arg_go(s: String, +acc: U32, +ok: Bool, +any: Bool) -> U32 & Bool:
  match s:
    case SNil{}:
      (acc, ok && any)
    case SCon{head, tail}:
      +c : U32 = Char.to_u32(head)
      +dg : Bool = U32.is_ge(c, 48) && U32.is_le(c, 57)
      d_arg_go(tail, (acc * 10 + (c - 48 : U32) : U32), ok && dg, True{})

def d_arg_fin(pr: U32 & Bool) -> U32:
  match pr:
    case Tuple{v, ok}:
      S.pick(ok, v, 4294967295)

def d_arg(m: Maybe<&1, String>) -> U32:
  match m:
    case None{}:
      4294967295
    case Some{value}:
      d_arg_fin(d_arg_go(value, 0, True{}, False{}))

def judge_d(+recs: List<&2, D.Rec>, +only: U32) -> String:
  +nex = U32.to_nat((K.max_ex_ix(recs, 0) + 1 : U32))
  +nlv = U32.to_nat((K.max_lvl_ix(recs, 0) + 1 : U32))
  show_all(fjudge_d(recs, K.decls_of(recs, Nil{}), nex, nlv, 32n,
          (K.max_any_ix(recs, 0) + 1 : U32), only))

def d_args(av: List<&1, String>) -> String & U32:
  match av:
    case Nil{}:
      ("", 4294967295)
    case Con{a0, r1}:
      match r1:
        case Nil{}:
          ("", 4294967295)
        case Con{a1, r2}:
          match r2:
            case Nil{}:
              (a1, 4294967295)
            case Con{a2, r3}:
              (a1, d_arg(Some{a2}))

def main_d(pa: String & U32) -> IO(Unit):
  match pa:
    case Tuple{path, only}:
      do IO<Unit>:
        oh : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
        f : File <- open_or_fail(oh)
        pr : File & Result<&1, &1, U32 & String, List<&2, U32>>
          <- File.read_bytes(f, 8388608)
        recs : List<&2, D.Rec> <- stream(1200n, 8388608, pr,
          Tuple{S.Sc.start(), Tuple{D.Acc.start(), Nil{}}})
        IO.print(judge_d(recs, only))

def main() -> IO(Unit):
  do IO<Unit>:
    av : List<&1, String> <- IO.args()
    main_d(d_args(av))
