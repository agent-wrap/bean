# The flat checker -- M3c of docs/port-plan.md.
#
# Two stores, one checker: every STRUCTURAL check (inductive blocks,
# positivity, recursor derivation, name checks, scans) runs UNCHANGED on the
# Data-trie state from check.bend -- the code that already scores 174 with
# WRONG:0. The TYPED path (ck_typed through ck_infer) runs on the kernel
# machine over the flat Array store. Both stores are built from the same
# records; fdiff proved them identical.
#
# Per-declaration isolation is preserved exactly: each declaration's machine
# run starts from the same base next-index (slots above it are recycled),
# the same level trie, and an empty reduction memo -- the old semantics,
# where terms built checking one declaration are invisible to the next.

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

# decode the machine's verdict register
def fv_of(+r: U32) -> C.V:
  match r:
    case 0:
      C.VAccept{}
    case 1:
      C.VReject{}
    case _:
      C.VDecline{}

# run one declaration's typed check on the machine and fold the verdict
def fck_fold(kr: ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>),
             +sv: C.V) -> (Array<T.Ex> & U32) & C.V:
  match kr:
    case Tuple{Tuple{fs, v}, lv}:
      (fs, C.comb(sv, fv_of(v)))

# one declaration: structural checks on the trie, the typed check on the
# machine; the machine state re-enters with the base nx (slot recycling)
def fck_one(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
            +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +nmt: R.Tr<T.Nm>,
            +d: K.Dcl, +basenx: U32, +natn: U32, +qtt: R.Tr<U32>,
            fs: Array<T.Ex> & U32) -> (Array<T.Ex> & U32) & C.V:
  match d fs:
    case K.DInd{nms, items} Tuple{ex, nx}:
      +its = items
      +ntb = B.add_items_nt(its, nt)
      ((ex, nx),
       C.comb(C.comb(C.comb(C.ind_items(its, I.is_ex(st), nt, vt,
                                        C.VAccept{}),
                            C.ctor_all(its, I.is_ex(st),
                                       C.ind_names_of(its, Nil{}),
                                       C.VAccept{})),
                     C.block_rec_v(its, I.is_ex(st), I.is_lnt(st), ntb,
                                   lp)),
              C.comb(C.block_derive_v(its, st, mt, vt, I.is_lnt(st), ntb,
                                      lp),
                     C.block_names_v(its, nmt))))
    case K.DNone{} Tuple{ex, nx}:
      ((ex, nx), C.VDecline{})
    case _ Tuple{ex, nx}:
      +pd = d
      fck_fold(M.fck_typed(1000000000n, (ex, basenx), I.is_lnt(st),
                           I.is_nlx(st), mt, lp, vt, qtt, natn, R.TNil{},
                           nt, K.dcl_is_theorem(pd), K.dcl_type(pd),
                           K.dcl_value(pd)),
               C.self_ref_v(I.is_ex(st), pd))

# each declaration is checked against the environment built from the ones
# before it, then added -- exactly check.bend's ck_all, with the flat store
# threaded through
def fck_all(ds: List<&2, K.Dcl>, +st: I.IS, +mt: R.Tr<I.Meta>,
            +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
            +nmt: R.Tr<T.Nm>, +basenx: U32, +natn: U32, +qtt: R.Tr<U32>,
            +acc: C.V, fr: (Array<T.Ex> & U32) & C.V) -> C.V:
  match ds fr:
    case Nil{} Tuple{fs, v}:
      C.comb(acc, v)
    case Con{head, tail} Tuple{fs, v}:
      +h = head
      fck_all(tail, st, mt, B.add_nt(h, nt), B.add_lp(h, lp),
              B.add_vt(h, vt), nmt, basenx, natn, qtt, C.comb(acc, v),
              fck_one(st, mt, nt, lp, vt, nmt, h, basenx, natn, qtt, fs))

def fjudge(+recs: List<&2, D.Rec>, +ds: List<&2, K.Dcl>, +nex: Nat,
           +nlv: Nat, +rounds: Nat, +nx: U32) -> C.V:
  +ex = B.build_ex(recs, R.TNil{})
  +ln = B.lv_resolve(rounds, nlv, B.build_lv(recs, R.TNil{}), R.TNil{})
  +dn = C.mark_names(Con{0, C.declared(ds, Nil{})}, R.TNil{})
  +natn = K.find_name(recs, [78, 97, 116], 4294967295)
  +qtt = K.build_wk2(recs, R.TNil{})
  +st : I.IS = I.IS{ex, nx, ln, nx, R.TNil{}, K.build_ht(recs, R.TNil{}),
                    natn,
                    K.find_name(recs,
                                [83, 116, 114, 105, 110, 103],
                                4294967295),
                    qtt}
  +strt = C.build_str(ds, R.TNil{})
  C.comb(C.comb(C.pre_check(ds),
                C.comb(C.bad_v(C.scan_consts(nex, 0, ex, dn, False{})),
                       C.scan_projs(nex, 0, ex, strt, C.VAccept{}))),
         fck_all(ds, st, C.build_meta(ds, ex, ln, R.TNil{}), R.TNil{},
                 R.TNil{}, R.TNil{}, K.build_nm(recs, R.TNil{}), nx,
                 natn, qtt, C.VAccept{},
                 ((F.fb_ex(recs,
                           Array.new(T.Ex, Nat.add(F.fdepth(nx), 4n),
                                     T.EBad{})), nx), C.VAccept{})))
