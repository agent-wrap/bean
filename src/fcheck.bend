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
def fs_ovf(+o: Bool, fs: Array<T.Ex> & U32) -> Array<T.Ex> & U32:
  match fs:
    case Tuple{ex, nx}:
      (ex, S.pick(o, 4294967295, nx))

def fck_fold(kr: ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>),
             +sv: C.V) -> (Array<T.Ex> & U32) & C.V:
  match kr:
    case Tuple{Tuple{fs, v}, Tuple{lt, wm}}:
      # fuel-exhaustion flags set by the machine (see km.bend WRb / KKpF):
      # CORRUPT (walk fuel) -> decline regardless; INCOMPLETE (whnf fuel) ->
      # a reject is not trustworthy -> decline. Accepts stay valid.
      +w2 : R.Tr<U32> = wm
      +cor : Bool = Bool.not(U32.is_eq(R.get(U32, 64n, w2, 4294967291,
                                             4294967295), 4294967295))
      +inc : Bool = Bool.not(U32.is_eq(R.get(U32, 64n, w2, 4294967292,
                                             4294967295), 4294967295))
      +v2 : U32 = v
      # OVF: the store overflowed somewhere inside (a rollback may have
      # hidden the peak) -- reported as an allocation pointer past
      # capacity, so fck_all declines this and every later declaration
      +ovf : Bool = Bool.not(U32.is_eq(R.get(U32, 64n, w2, 4294967280,
                                             4294967295), 4294967295))
      (fs_ovf(ovf, fs), C.comb(sv, fv_of(S.pick(cor || (inc && U32.is_eq(v2, 1)), 2,
                                   v2))))

# one declaration: structural checks on the trie, the typed check on the
# machine; the machine state re-enters with the base nx (slot recycling)
# an inductive block: the structural checks, and the recursors -- derived
# by the single-inductive path, or (mutual / nested) by nested.bend, whose
# verdict build_meta2 left in the metadata
def block_v(+nb: Bool, +its: List<&2, K.IItem>, +st: I.IS,
            +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>,
            +vt: R.Tr<U32>, +ntb: R.Tr<U32>, +nmt: R.Tr<T.Nm>) -> C.V:
  match nb:
    case True{}:
      C.comb(C.comb(C.ind_items(its, I.is_ex(st), nt, vt, C.VAccept{}),
                    C.ctor_all(its, I.is_ex(st), C.ind_names_of(its, Nil{}),
                               C.VAccept{})),
             C.block_ver_v(its, mt))
    case False{}:
      C.comb(C.comb(C.comb(C.ind_items(its, I.is_ex(st), nt, vt,
                                       C.VAccept{}),
                           C.ctor_all(its, I.is_ex(st),
                                      C.ind_names_of(its, Nil{}),
                                      C.VAccept{})),
                    C.block_rec_v(its, I.is_ex(st), I.is_lnt(st), ntb, lp)),
             C.comb(C.derive_or_ver(its, st, mt, vt, I.is_lnt(st), ntb, lp),
                    C.block_names_v(its, nmt)))

def fck_one(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
            +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +nmt: R.Tr<T.Nm>,
            +d: K.Dcl, +basenx: U32, +natn: U32, +qtt: R.Tr<U32>,
            fs: Array<T.Ex> & U32) -> (Array<T.Ex> & U32) & C.V:
  match d fs:
    case K.DInd{nms, items} Tuple{ex, nx}:
      +its = items
      +ntb = B.add_items_nt(its, nt)
      ((ex, nx), block_v(C.is_nm_block(its), its, st, mt, nt, lp, vt, ntb,
                         nmt))
    case K.DNone{} Tuple{ex, nx}:
      ((ex, nx), C.VDecline{})
    case _ Tuple{ex, nx}:
      +pd = d
      fck_fold(M.fck_typed(1000000000n, (ex, nx), I.is_lnt(st),
                           I.is_nlx(st), mt, lp, vt, qtt, natn, R.TNil{},
                           nt, K.dcl_is_theorem(pd), K.dcl_type(pd),
                           K.dcl_value(pd), basenx),
               C.self_ref_v(I.is_ex(st), pd))

# each declaration is checked against the environment built from the ones
# before it, then added -- exactly check.bend's ck_all, with the flat store
# threaded through
# 2^n as U32
def kpow2(n: Nat) -> U32:
  match n:
    case 0n:
      1
    case 1n+p:
      (kpow2(p) * 2 : U32)

# The store is `Array.new(T.Ex, d, ..)`: exactly 2^d slots, and an index i
# silently ALIASES slot i mod 2^d (measured, bench/arrsem.bend). Allocating
# past capacity therefore overwrites live early slots -- the export's own
# terms and the hash table -- and every later read is garbage. That silently
# turned true library declarations into rejects in perf/magma-list-deep-n21.
# Allocation restarts at the region base for every declaration (and drops
# back inside one at km's rollback regions, KRb), so an overflow is checked
# per declaration -- at its end here, and at every KRb, which marks it
# CORRUPT. Overflow aliases slots below, so every LATER declaration is
# untrustworthy too: the combined verdict declines.
def ovf_v(+nx: U32, +cap: U32, +v: C.V) -> C.V:
  C.pick_v(U32.is_ge(nx, cap), C.VDecline{}, v)

def fck_all(ds: List<&2, K.Dcl>, +st: I.IS, +mt: R.Tr<I.Meta>,
            +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
            +nmt: R.Tr<T.Nm>, +basenx: U32, +natn: U32, +qtt: R.Tr<U32>,
            +cap: U32, +poison: Bool, +acc: C.V,
            fr: (Array<T.Ex> & U32) & C.V) -> C.V:
  match ds fr:
    case Nil{} Tuple{Tuple{ex, nx}, v}:
      C.comb(acc, ovf_v(S.pick(poison, 4294967295, nx), cap, v))
    case Con{head, tail} Tuple{Tuple{ex, nx}, v}:
      +h = head
      +nx2 : U32 = nx
      # an overflow aliases slots below it: every LATER declaration runs on
      # a corrupted store, so the poison is sticky
      +p2 : Bool = poison || U32.is_ge(nx2, cap)
      fck_all(tail, st, mt, B.add_nt(h, nt), B.add_lp(h, lp),
              B.add_vt(h, vt), nmt, basenx, natn, qtt, cap, p2,
              C.comb(acc, ovf_v(S.pick(p2, 4294967295, nx2), cap, v)),
              # every declaration allocates from the region base again:
              # nothing a finished declaration allocated is referenced
              # later (its memo dies with it, the hash table's pointers
              # into the reused range become tombstones)
              fck_one(st, mt, nt, lp, vt, nmt, h, basenx, natn, qtt,
                      (ex, (basenx + 1048578 : U32))))

def fjudge(+recs: List<&2, D.Rec>, +ds: List<&2, K.Dcl>, +nex: Nat,
           +nlv: Nat, +rounds: Nat, +nx: U32) -> C.V:
  +ex = B.build_ex(recs, R.TNil{})
  +ln = B.lv_resolve(rounds, nlv, B.build_lv(recs, R.TNil{}), R.TNil{})
  +dn = C.mark_names(Con{0, C.declared(ds, Nil{})}, R.TNil{})
  # Nat (key 20) and String (key 10) come from build_wk4's two passes
  +wk = K.build_wk4(recs, R.TNil{})
  +natn : U32 = R.get(U32, 64n, wk, 20, 4294967295)
  +strn : U32 = R.get(U32, 64n, wk, 10, 4294967295)
  +qtt = K.add_hts(recs, wk)
  +st : I.IS = I.IS{ex, nx, ln, nx, R.TNil{}, K.build_ht(recs, R.TNil{}),
                    natn, strn, qtt}
  +strt = C.build_str(ds, R.TNil{})
  C.comb(C.comb(C.pre_check(ds),
                C.comb(C.bad_v(C.scan_consts(nex, 0, ex, dn, False{})),
                       C.scan_projs(nex, 0, ex, strt, C.VAccept{}))),
         fck_all(ds, st, C.build_meta2(ds, st, R.TNil{}, R.TNil{}, R.TNil{},
                                       R.TNil{},
                                       [I.is_qt(st, 16), I.is_qt(st, 17),
                                        I.is_qt(st, 18), I.is_qt(st, 19)], R.TNil{}),
                 R.TNil{},
                 R.TNil{}, R.TNil{}, K.build_nm(recs, R.TNil{}), nx,
                 natn, qtt,
                 # usable capacity; the array is twice that, its upper half
                 # holds the loose-bvar ranges (km's kput / khalf)
                 kpow2(M.sdepth(nx)), False{},
                 C.VAccept{},
                 ((M.klb_init(U32.to_nat(nx), 0, M.khalf(nx),
                   F.fb_ex(recs,
                           Array.new(T.Ex, Nat.add(M.sdepth(nx), 1n),
                                     T.EBad{}))),
                   (nx + 1048578 : U32)), C.VAccept{})))
