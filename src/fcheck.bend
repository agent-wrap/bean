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

def fck_fold2(pr: Array<T.Ex> & U32, +nx: U32, +v: U32,
              +sv: C.V) -> (Array<T.Ex> & U32) & C.V:
  match pr:
    case Tuple{ex, fl}:
      # flags set by the machine in the store (km.bend kfl_*): CORRUPT
      # (walk fuel, overflow) -> decline regardless; INCOMPLETE (whnf fuel,
      # an iota beyond us) -> a reject is not trustworthy -> decline.
      # Accepts stay valid. OVF: the store overflowed somewhere inside (a
      # rollback may have hidden the peak) -- reported as an allocation
      # pointer past capacity, so fck_all declines this and every later
      # declaration
      +f2 : U32 = fl
      +cor : Bool = Bool.not(U32.is_eq(U32.and(f2, 2), 0))
      +inc : Bool = Bool.not(U32.is_eq(U32.and(f2, 4), 0))
      +ovf : Bool = Bool.not(U32.is_eq(U32.and(f2, 1), 0))
      +v2 : U32 = v
      (fs_ovf(ovf, (ex, nx)),
       C.comb(sv, fv_of(S.pick(cor || (inc && U32.is_eq(v2, 1)), 2, v2))))

def fck_fold(kr: ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>),
             +sv: C.V, +base: U32) -> (Array<T.Ex> & U32) & C.V:
  match kr:
    case Tuple{Tuple{Tuple{ex, nx}, v}, Tuple{lt, wm}}:
      fck_fold2(M.kfl_flags(ex, base), nx, v, sv)

# A declaration may not name itself (check.bend self_ref_v), checked over
# the store after the machine (export nodes are never written): a memoised
# worklist from the type and value; 1 found, 0 not, 2 out of fuel
def sr_kids(+x: T.Ex, +nm: U32, wl: List<&2, U32>) -> List<&2, U32> & U32:
  match x:
    case T.EConst{n, us}:
      (wl, S.pick(U32.is_eq(n, nm), 1, 0))
    case T.EApp{f, a}:
      (Con{f, Con{a, wl}}, 0)
    case T.ELam{n, t, b, bi}:
      (Con{t, Con{b, wl}}, 0)
    case T.EAll{n, t, b, bi}:
      (Con{t, Con{b, wl}}, 0)
    case T.ELet{n, t, v, b}:
      (Con{t, Con{v, Con{b, wl}}}, 0)
    case T.EProj{tn, i, sx}:
      (Con{sx, wl}, 0)
    case _:
      (wl, 0)

def sr_step4(a: Array<T.Ex>, r: List<&2, U32> & U32, +vis: R.Tr<U32>,
             +f: U32) -> (Array<T.Ex> & List<&2, U32>) & (R.Tr<U32> & U32):
  match r:
    case Tuple{wl, g}:
      +g2 : U32 = g
      ((a, S.pick_l(U32.is_eq(g2, 1), Nil{}, wl)), (vis, (f + g2 : U32)))

def sr_step3(pr: Array<T.Ex> & T.Ex, t: List<&2, U32>, +vis: R.Tr<U32>,
             +f: U32, +nm: U32)
    -> (Array<T.Ex> & List<&2, U32>) & (R.Tr<U32> & U32):
  match pr:
    case Tuple{a, x}:
      sr_step4(a, sr_kids(x, nm, t), vis, f)

def sr_step2(+skip: Bool, +h: U32, a: Array<T.Ex>, t: List<&2, U32>,
             +vis: R.Tr<U32>, +f: U32, +nm: U32)
    -> (Array<T.Ex> & List<&2, U32>) & (R.Tr<U32> & U32):
  match skip:
    case True{}:
      ((a, t), (vis, f))
    case False{}:
      sr_step3(Array.get(T.Ex, a, h), t, R.set(U32, 64n, vis, h, 1, 0), f, nm)

def sr_go(fuel: Nat, +nm: U32, +lim: U32,
          st: (Array<T.Ex> & List<&2, U32>) & (R.Tr<U32> & U32))
    -> Array<T.Ex> & U32:
  match fuel st:
    case 0n Tuple{Tuple{a, wl}, Tuple{vis, f}}:
      (a, S.pick(U32.is_ge(f, 1), 1, 2))
    case 1n+p Tuple{Tuple{a, Nil{}}, Tuple{vis, f}}:
      (a, S.pick(U32.is_ge(f, 1), 1, 0))
    case 1n+p Tuple{Tuple{a, Con{h, t}}, Tuple{vis, f}}:
      +h2 : U32 = h
      +v2 : R.Tr<U32> = vis
      sr_go(p, nm, lim,
            sr_step2(U32.is_ge(h2, lim)
                     || U32.is_ne(R.get(U32, 64n, v2, h2, 0), 0),
                     h2, a, t, v2, f, nm))

def sr_v(+c: U32) -> C.V:
  match c:
    case 0:
      C.VAccept{}
    case 1:
      C.VReject{}
    case _:
      C.VDecline{}

def fsr2(pr: Array<T.Ex> & U32) -> Array<T.Ex> & C.V:
  match pr:
    case Tuple{a, c}:
      (a, sr_v(c))

def fsr3(+none: Bool, a: Array<T.Ex>, +nm: U32, +ti: U32, +vi: U32,
         +lim: U32) -> Array<T.Ex> & C.V:
  match none:
    case True{}:
      (a, C.VAccept{})
    case False{}:
      fsr2(sr_go(Nat.mul(4294967295n, 4n), nm, lim,
                 ((a, [ti, vi]), (R.TNil{}, 0))))

def fsr(a: Array<T.Ex>, +d: K.Dcl, +lim: U32) -> Array<T.Ex> & C.V:
  +d2 : K.Dcl = d
  +nm : U32 = K.dcl_name(d2)
  fsr3(U32.is_eq(nm, 0), a, nm, K.dcl_type(d2), K.dcl_value(d2), lim)

def fck_fold_s2(pr: Array<T.Ex> & C.V, +nx: U32, +v: U32,
                +base: U32) -> (Array<T.Ex> & U32) & C.V:
  match pr:
    case Tuple{ex, sv}:
      fck_fold2(M.kfl_flags(ex, base), nx, v, sv)

def fck_fold_s(kr: ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>),
               +d: K.Dcl, +base: U32) -> (Array<T.Ex> & U32) & C.V:
  match kr:
    case Tuple{Tuple{Tuple{ex, nx}, v}, Tuple{lt, wm}}:
      fck_fold_s2(fsr(ex, d, base), nx, v, base)

# one declaration: structural checks on the trie, the typed check on the
# machine; the machine state re-enters with the base nx (slot recycling)
# an inductive block: the structural checks, and the recursors -- derived
# by the single-inductive path, or (mutual / nested) by nested.bend, whose
# verdict build_meta2 left in the metadata
def block_v2(+nb: Bool, +its: List<&2, K.IItem>, +st: I.IS,
             +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>,
             +vt: R.Tr<U32>, +ntb: R.Tr<U32>, +nmt: R.Tr<T.Nm>) -> C.V:
  match nb:
    case True{}:
      C.comb(C.comb(C.comb(C.ind_items(its, I.is_ex(st), nt, vt, C.VAccept{}),
                           C.ctor_all(its, I.is_ex(st),
                                      C.ind_names_of(its, Nil{}),
                                      C.VAccept{})),
                    C.comb(C.block_lps_v(its, I.is_ex(st), I.is_lnt(st)),
                           C.rules_nf_v(its, its))),
             C.block_ver_v(its, mt))
    case False{}:
      C.comb(C.comb(C.comb(C.ind_items(its, I.is_ex(st), nt, vt,
                                       C.VAccept{}),
                           C.ctor_all(its, I.is_ex(st),
                                      C.ind_names_of(its, Nil{}),
                                      C.VAccept{})),
                    C.block_rec_v(its, I.is_ex(st), I.is_lnt(st), ntb, lp, C.fo_on(st, mt, vt))),
             C.comb(C.comb(C.derive_or_ver(its, st, mt, vt, I.is_lnt(st), ntb, lp),
                           C.block_names_v(its, nmt)),
                    C.comb(C.block_lps_v(its, I.is_ex(st), I.is_lnt(st)),
                           C.rules_nf_v(its, its))))

def block_v(+nb: Bool, +its0: List<&2, K.IItem>, +st0: I.IS,
            +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>,
            +vt: R.Tr<U32>, +ntb: R.Tr<U32>, +nmt: R.Tr<T.Nm>) -> C.V:
  # each inductive's type with its telescope exposed by whnf (Lean peels an
  # inductive type through whnf: Mathlib's `CompClosure ... : HomRel C`)
  +ei = C.exp_items(its0, st0, mt, lp, vt, Nil{})
  block_v2(nb, C.ei_its(ei), C.ei_st(ei), mt, nt, lp, vt, ntb, nmt)

# A declined block gets the machine's positivity pass over every
# constructor (M.fck_posit): a definite invalid occurrence (a stuck K-like
# recursor whose indices are NOT the constructor's, mentioning the block)
# is Lean's rejection -- bugs/rec-missing-ih. Anything else stays declined.
def posit_v(kr: ((Array<T.Ex> & U32) & U32) & ((R.Tr<L.LN> & U32) & R.Tr<U32>)) -> (Array<T.Ex> & U32) & Bool:
  match kr:
    case Tuple{Tuple{fs, v}, rest}:
      (fs, U32.is_eq(v, 2))

def posit_one(+item: K.IItem, +nms: List<&2, U32>, +st: I.IS,
              +mt: R.Tr<I.Meta>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
              +basenx: U32, +natn: U32, +qtt: R.Tr<U32>, +nt: R.Tr<U32>,
              fs: Array<T.Ex> & U32) -> (Array<T.Ex> & U32) & Bool:
  match item:
    case K.ICtor{nm, lps, ty, ind, np, nf, ci}:
      posit_v(M.fck_posit(100000000n, fs, I.is_lnt(st), I.is_nlx(st), mt, lp,
                          vt, qtt, natn, R.TNil{}, nt, ty, np, nms, basenx))
    case _:
      (fs, False{})

def posit_ctors(items: List<&2, K.IItem>, +nms: List<&2, U32>, +st: I.IS,
                +mt: R.Tr<I.Meta>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
                +basenx: U32, +natn: U32, +qtt: R.Tr<U32>, +nt: R.Tr<U32>,
                r: (Array<T.Ex> & U32) & Bool) -> (Array<T.Ex> & U32) & Bool:
  match items r:
    case Nil{} Tuple{fs, b}:
      (fs, b)
    case Con{head, tail} Tuple{fs, True{}}:
      (fs, True{})
    case Con{head, tail} Tuple{fs, False{}}:
      posit_ctors(tail, nms, st, mt, lp, vt, basenx, natn, qtt, nt,
                  posit_one(head, nms, st, mt, lp, vt, basenx, natn, qtt, nt, fs))

def posit_fin(r: (Array<T.Ex> & U32) & Bool) -> (Array<T.Ex> & U32) & C.V:
  match r:
    case Tuple{fs, True{}}:
      (fs, C.VReject{})
    case Tuple{fs, False{}}:
      (fs, C.VDecline{})

def posit_if(+v: C.V, +items: List<&2, K.IItem>, +nms: List<&2, U32>,
             +st: I.IS, +mt: R.Tr<I.Meta>, +lp: R.Tr<List<&2, U32>>,
             +vt: R.Tr<U32>, +basenx: U32, +natn: U32, +qtt: R.Tr<U32>,
             +nt: R.Tr<U32>, fs: Array<T.Ex> & U32) -> (Array<T.Ex> & U32) & C.V:
  match v:
    case C.VDecline{}:
      posit_fin(posit_ctors(items, nms, st, mt, lp, vt, basenx, natn, qtt, nt,
                            (fs, False{})))
    case _:
      (fs, v)

# fuel per pass mode: the cheap-projection pass (1) first on 2^30 steps,
# the capped full pass (2) on 2^32, the full pass (absent) on 2^32 * 64
def fck_fuel2(+cheap: Bool) -> Nat:
  match cheap:
    case True{}:
      Nat.mul(4294967295n, 64n)
    case False{}:
      4294967295n

def fck_fuel3(+full: Bool, +cheap: Bool) -> Nat:
  match full:
    case True{}:
      Nat.mul(4294967295n, 64n)
    case False{}:
      fck_fuel2(cheap)

def fck_fuel(+mode: U32) -> Nat:
  fck_fuel3(U32.is_eq(mode, 0), U32.is_eq(mode, 1))

def fck_one(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
            +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +nmt: R.Tr<T.Nm>,
            +d: K.Dcl, +basenx: U32, +natn: U32, +qtt: R.Tr<U32>,
            fs: Array<T.Ex> & U32) -> (Array<T.Ex> & U32) & C.V:
  match d fs:
    case K.DInd{nms, items} Tuple{ex, nx}:
      +its = items
      +ntb = B.add_items_nt(its, nt)
      +ntb2 : R.Tr<U32> = ntb
      posit_if(block_v(C.is_nm_block(its), its, st, mt, nt, lp, vt, ntb2,
                       nmt),
               its, nms, st, mt, lp, vt, basenx, natn, qtt, ntb2, (ex, nx))
    case K.DNone{} Tuple{ex, nx}:
      ((ex, nx), C.VDecline{})
    case _ Tuple{ex, nx}:
      +pd = d
      # the machine's step fuel: 2^32 * 64 (a Nat literal stops at 2^32-1).
      # 1e9 steps (~33 s) ran out on Lean.Grind.Ring.OfSemiring.mul_helper
      # and WellFounded.partialExtrinsicFix₃_eq: the machine then answered
      # with a stale register, read as a decline with no flag or UNK
      # anywhere (found with a diagnostic fold mapping registers outside
      # 0..2 to a reject)
      # fck_sel's first two passes run on 2^32 steps (~2 min); a
      # declaration they cannot settle declines into the next pass
      fck_fold_s(M.fck_typed(fck_fuel(R.get(U32, 64n, qtt, 48, 0)),
                             (ex, nx), I.is_lnt(st),
                             I.is_nlx(st), mt, lp, vt, qtt, natn, R.TNil{},
                             nt, K.dcl_is_theorem(pd), K.dcl_type(pd),
                             K.dcl_value(pd), basenx),
                 pd, basenx)

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

# The declarations checked: [krange_lo, krange_hi) by index. Everything in
# the checker; tools/frange.sh rewrites these two in a copy to check one
# slice of a large export (the rest trusted, still entering the tables), so
# a long corpus runs as parallel slices.
def krange_lo() -> U32:
  0

def krange_hi() -> U32:
  4294967295

# Three passes per declaration, each from a fresh region, the first
# decisive verdict standing (every pass is sound; they differ only in what
# they settle and how fast):
#   1. the full machine on a 2^32-step fuel (qtt key 48 = 2) -- what
#      std, init and cedar were tuned on; nearly every declaration ends here
#   2. Lean's cheap projections in the defeq core (key = 1, same fuel):
#      whnf_core leaves a projection's structure un-delta'd and the full
#      projection is the tail's, as Lean's is_def_eq_core does. Navier's
#      instance-heavy theorems need it (sourceCoordinateSolver: the full
#      machine unfolds AEEqFun.cast where Lean compares it as a head;
#      > 2,400 s -> ~70 s); std's bit-blasting proofs stall in it
#   3. the full machine on its full fuel (key absent), as before
def fck_retry2(+dec: Bool, +st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
               +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +nmt: R.Tr<T.Nm>,
               +d: K.Dcl, +basenx: U32, +natn: U32, +q2: R.Tr<U32>,
               r: (Array<T.Ex> & U32) & C.V) -> (Array<T.Ex> & U32) & C.V:
  match dec r:
    case True{} Tuple{Tuple{ex, nx}, v}:
      +n2 : U32 = nx
      +b2 : U32 = (basenx + M.ktbl(basenx) + 2 : U32)
      fck_one(st, mt, nt, lp, vt, nmt, d, basenx, natn, q2,
              (M.kbump_n(ex, basenx, (n2 - b2 : U32)), b2))
    case False{} Tuple{fs, v}:
      (fs, v)

def fck_isdec(+v: C.V) -> Bool:
  match v:
    case C.VDecline{}:
      True{}
    case _:
      False{}

def fck_isacc(+v: C.V) -> Bool:
  match v:
    case C.VAccept{}:
      True{}
    case _:
      False{}

# the cheap and capped passes are not complete: a NO there (a cheap
# projection left a pair apart that the full pass equates) is not final.
# Any non-accept retries in the next pass; only the full pass rejects.
# (navier's nat_square_le_two_pow and Finset.sum_schlomilch_le were
# rejected by the cheap pass, accepted by the full one)
def fck_retry_na(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
                 +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +nmt: R.Tr<T.Nm>,
                 +d: K.Dcl, +basenx: U32, +natn: U32, +q2: R.Tr<U32>,
                 r: (Array<T.Ex> & U32) & C.V) -> (Array<T.Ex> & U32) & C.V:
  match r:
    case Tuple{fs, v}:
      +v2 : C.V = v
      fck_retry2(Bool.not(fck_isacc(v2)), st, mt, nt, lp, vt, nmt, d, basenx,
                 natn, q2, (fs, v2))

def fck_retry(+st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
              +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +nmt: R.Tr<T.Nm>,
              +d: K.Dcl, +basenx: U32, +natn: U32, +q2: R.Tr<U32>,
              r: (Array<T.Ex> & U32) & C.V) -> (Array<T.Ex> & U32) & C.V:
  match r:
    case Tuple{fs, v}:
      +v2 : C.V = v
      fck_retry2(fck_isdec(v2), st, mt, nt, lp, vt, nmt, d, basenx, natn,
                 q2, (fs, v2))

def fck_sel(+go: Bool, +st: I.IS, +mt: R.Tr<I.Meta>, +nt: R.Tr<U32>,
            +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>, +nmt: R.Tr<T.Nm>,
            +d: K.Dcl, +basenx: U32, +natn: U32, +qtt: R.Tr<U32>,
            fs: Array<T.Ex> & U32) -> (Array<T.Ex> & U32) & C.V:
  match go:
    case True{}:
      fck_retry_na(st, mt, nt, lp, vt, nmt, d, basenx, natn, qtt,
        fck_retry_na(st, mt, nt, lp, vt, nmt, d, basenx, natn,
                  R.set(U32, 64n, qtt, 48, 2, 4294967295),
          fck_one(st, mt, nt, lp, vt, nmt, d, basenx, natn,
                  R.set(U32, 64n, qtt, 48, 1, 4294967295), fs)))
    case False{}:
      (fs, C.VAccept{})

def fck_all(ds: List<&2, K.Dcl>, +st: I.IS, +mt: R.Tr<I.Meta>,
            +nt: R.Tr<U32>, +lp: R.Tr<List<&2, U32>>, +vt: R.Tr<U32>,
            +nmt: R.Tr<T.Nm>, +basenx: U32, +natn: U32, +qtt: R.Tr<U32>,
            +cap: U32, +poison: Bool, +acc: C.V, +ix: U32, +wk: U32, +wn: U32,
            fr: (Array<T.Ex> & U32) & C.V) -> C.V:
  match ds fr:
    case Nil{} Tuple{Tuple{ex, nx}, v}:
      C.comb(acc, ovf_v(S.pick(poison, 4294967295, nx), cap, v))
    case Con{head, tail} Tuple{Tuple{ex, nx}, v}:
      +h = head
      +nx2 : U32 = nx
      # an overflow declines its own declaration; km's kput drops writes
      # past capacity, so nothing it allocated aliases the export's slots
      # and later declarations run on an intact store
      +p2 : Bool = U32.is_ge(nx2, cap)
      fck_all(tail, st, mt, B.add_nt(h, nt), B.add_lp(h, lp),
              B.add_vt(h, vt), nmt, basenx, natn, qtt, cap, p2,
              C.comb(acc, ovf_v(S.pick(p2, 4294967295, nx2), cap, v)),
              (ix + 1 : U32), wk, wn,
              # every declaration allocates from the region base again:
              # nothing a finished declaration allocated is referenced
              # later (its memo dies with it; kbump moves the hash table to
              # a new epoch, which retires every pointer it left)
              fck_sel(U32.is_ge(ix, krange_lo()) && U32.is_lt(ix, krange_hi())
                      && U32.is_eq(U32.mod(ix, wn), wk),
                      st, mt, nt, lp, vt, nmt, h, basenx, natn, qtt,
                      (M.kbump_n(ex, basenx, (nx2 - (basenx + M.ktbl(basenx) + 2 : U32) : U32)),
                       (basenx + M.ktbl(basenx) + 2 : U32))))

# ---- dynamic sharing --------------------------------------------------
# With a claim directory (fmain's fourth argument) every worker walks all
# declarations -- entering each in the tables, as a trusted one -- and
# checks a chunk only if it claimed it first (fmain: a claim file per
# chunk). A chunk is skipped only when another worker claimed it, and that
# worker's verdict (or crash) counts in the wrapper's join; a race leaves a
# chunk checked twice, never unchecked. A worker stuck on one heavy
# declaration falls behind and the others take the chunks after it (cslib:
# one worker drew tensorTensorTensorComm_eq, 1093 s, on top of its ~1000 s
# share). FL is fck_all's state between chunks.
type FL is Type:
  FL{ds: List<&2, K.Dcl>, st: I.IS, mt: R.Tr<I.Meta>, nt: R.Tr<U32>,
     lp: R.Tr<List<&2, U32>>, vt: R.Tr<U32>, nmt: R.Tr<T.Nm>, basenx: U32,
     natn: U32, qtt: R.Tr<U32>, cap: U32, poison: Bool, acc: C.V, ix: U32,
     fr: (Array<T.Ex> & U32) & C.V}

# an inductive block's derivation (recursors, nested translation) runs only
# in its OWNER, worker ix mod wn (C.build_meta2), and its verdict surfaces
# when the declaration is checked: so the owner checks it whoever claimed
# the chunk (bugs/rec-missing-ih was accepted when another worker took it)
def fck_isind(+d: K.Dcl) -> Bool:
  match d:
    case K.DInd{nms, items}:
      True{}
    case _:
      False{}

def fck_dsel(+isind: Bool, +go: Bool, +ix: U32, +wk: U32, +wn: U32) -> Bool:
  match isind:
    case True{}:
      U32.is_eq(U32.mod(ix, wn), wk)
    case False{}:
      go

# the next n declarations, checked when go (and in krange), else trusted
def fck_chunk(n: Nat, +go: Bool, +wk: U32, +wn: U32, s: FL) -> FL:
  match n s:
    case 0n FL{ds, st, mt, nt, lp, vt, nmt, basenx, natn, qtt, cap, poison,
               acc, ix, fr}:
      FL{ds, st, mt, nt, lp, vt, nmt, basenx, natn, qtt, cap, poison, acc,
         ix, fr}
    case 1n+p FL{Nil{}, st, mt, nt, lp, vt, nmt, basenx, natn, qtt, cap,
                 poison, acc, ix, fr}:
      FL{Nil{}, st, mt, nt, lp, vt, nmt, basenx, natn, qtt, cap, poison, acc,
         ix, fr}
    case 1n+p FL{Con{head, tail}, st, mt, nt, lp, vt, nmt, basenx, natn, qtt,
                 cap, poison, acc, ix, Tuple{Tuple{ex, nx}, v}}:
      +h = head
      +nx2 : U32 = nx
      +cp : U32 = cap
      +p2 : Bool = U32.is_ge(nx2, cp)
      +ix2 : U32 = ix
      +g2 : Bool = go
      +st2 : I.IS = st
      +mt2 : R.Tr<I.Meta> = mt
      +nt2 : R.Tr<U32> = nt
      +lp2 : R.Tr<List<&2, U32>> = lp
      +vt2 : R.Tr<U32> = vt
      +nm2 : R.Tr<T.Nm> = nmt
      +bn : U32 = basenx
      +na : U32 = natn
      +q2 : R.Tr<U32> = qtt
      fck_chunk(p, g2, wk, wn,
        FL{tail, st2, mt2, B.add_nt(h, nt2), B.add_lp(h, lp2), B.add_vt(h, vt2),
           nm2, bn, na, q2, cp, p2,
           C.comb(acc, ovf_v(S.pick(p2, 4294967295, nx2), cp, v)),
           (ix2 + 1 : U32),
           fck_sel(fck_dsel(fck_isind(h), g2, ix2, wk, wn)
                   && U32.is_ge(ix2, krange_lo())
                   && U32.is_lt(ix2, krange_hi()),
                   st2, mt2, nt2, lp2, vt2, nm2, h, bn, na, q2,
                   (M.kbump_n(ex, bn,
                              (nx2 - (bn + M.ktbl(bn) + 2 : U32) : U32)),
                    (bn + M.ktbl(bn) + 2 : U32)))})

def fl_more(s: FL) -> FL & Bool:
  match s:
    case FL{Nil{}, st, mt, nt, lp, vt, nmt, basenx, natn, qtt, cap, poison,
            acc, ix, fr}:
      (FL{Nil{}, st, mt, nt, lp, vt, nmt, basenx, natn, qtt, cap, poison, acc,
          ix, fr}, False{})
    case FL{Con{head, tail}, st, mt, nt, lp, vt, nmt, basenx, natn, qtt, cap,
            poison, acc, ix, fr}:
      (FL{Con{head, tail}, st, mt, nt, lp, vt, nmt, basenx, natn, qtt, cap,
          poison, acc, ix, fr}, True{})

def fl_fin(s: FL) -> C.V:
  match s:
    case FL{ds, st, mt, nt, lp, vt, nmt, basenx, natn, qtt, cap, poison, acc,
            ix, Tuple{Tuple{ex, nx}, v}}:
      C.comb(acc, ovf_v(S.pick(poison, 4294967295, nx), cap, v))

# ---- load: the independent tables in parallel ---------------------------
# Every table below reads the record list and nothing else, so they are
# built as a balanced tree of parallel calls (Bend's `a b = f(x) g(y)`):
# the load's wall time is its slowest branch, not the sum (navier-stokes:
# ~165 s of sequential table building after the read).
def fj_wq(+recs: List<&2, D.Rec>) -> R.Tr<U32> & R.Tr<U32>:
  +wk = K.build_wk4(recs, R.TNil{})
  (wk, K.add_hts(recs, wk))

def fj_ht(+recs: List<&2, D.Rec>) -> R.Tr<U32>:
  K.build_ht(recs, R.TNil{})

# lt: the expressions' lists (F.fb_route), at keys no level index reaches
def fj_ln(+recs: List<&2, D.Rec>, +nlv: Nat, +rounds: Nat,
          +lt: R.Tr<L.LN>) -> R.Tr<L.LN>:
  M.klv_seed(nlv, 0, B.lv_resolve(rounds, nlv, B.build_lv(recs, R.TNil{}),
                                  lt))

def fj_nm(+recs: List<&2, D.Rec>) -> R.Tr<T.Nm>:
  K.build_nm(recs, R.TNil{})

def fj_dn(+ds: List<&2, K.Dcl>) -> R.Tr<Bool> & (R.Tr<U32> & C.V):
  (C.mark_names(Con{0, C.declared(ds, Nil{})}, R.TNil{}),
   (C.build_str(ds, R.TNil{}), C.pre_check(ds)))

# branch C: the well-known constants and the hash tables
def fj_c(+recs: List<&2, D.Rec>) -> (R.Tr<U32> & R.Tr<U32>) & R.Tr<U32>:
  w h = fj_wq(recs) fj_ht(recs)
  (w, h)

# branch D: levels, names, declared names, string table, pre-check
def fj_d(+recs: List<&2, D.Rec>, +ds: List<&2, K.Dcl>, +nlv: Nat,
         +rounds: Nat, +lt: R.Tr<L.LN>) -> (R.Tr<L.LN> & R.Tr<T.Nm>) & (R.Tr<Bool> & (R.Tr<U32> & C.V)):
  ln n = fj_ln(recs, nlv, rounds, lt) fj_nm(recs)
  ((ln, n), fj_dn(ds))

def fj_cd(+recs: List<&2, D.Rec>, +ds: List<&2, K.Dcl>, +nlv: Nat,
          +rounds: Nat, +lt: R.Tr<L.LN>) -> ((R.Tr<U32> & R.Tr<U32>) & R.Tr<U32>) & ((R.Tr<L.LN> & R.Tr<T.Nm>) & (R.Tr<Bool> & (R.Tr<U32> & C.V))):
  c d = fj_c(recs) fj_d(recs, ds, nlv, rounds, lt)
  (c, d)

# the two whole-export scans, each over [lo, lo+cnt) split in halves to
# depth d: 2^d parallel lanes
def fj_scr(d: Nat, +lo: U32, +cnt: U32, +ex: R.Tr<T.Ex>,
           +dn: R.Tr<Bool>) -> Bool:
  match d:
    case 0n:
      C.scan_consts(U32.to_nat(cnt), lo, ex, dn, False{})
    case 1n+p:
      +h : U32 = (cnt / 2 : U32)
      +q = p
      a b = fj_scr(q, lo, h, ex, dn) fj_scr(q, (lo + h : U32), (cnt - h : U32), ex, dn)
      a || b

def fj_spr(d: Nat, +lo: U32, +cnt: U32, +ex: R.Tr<T.Ex>,
           +strt: R.Tr<U32>) -> C.V:
  match d:
    case 0n:
      C.scan_projs(U32.to_nat(cnt), lo, ex, strt, C.VAccept{})
    case 1n+p:
      +h : U32 = (cnt / 2 : U32)
      +q = p
      a b = fj_spr(q, lo, h, ex, strt) fj_spr(q, (lo + h : U32), (cnt - h : U32), ex, strt)
      C.comb(a, b)

def fj_sc(+nexu: U32, +ex: R.Tr<T.Ex>, +dn: R.Tr<Bool>) -> C.V:
  C.bad_v(fj_scr(4n, 0, nexu, ex, dn))

def fj_sp(+nexu: U32, +ex: R.Tr<T.Ex>, +strt: R.Tr<U32>) -> C.V:
  fj_spr(4n, 0, nexu, ex, strt)

def fj_meta(+ds: List<&2, K.Dcl>, +st: I.IS, +wid: U32,
            +wcnt: U32) -> R.Tr<I.Meta>:
  C.build_meta2(ds, st, R.TNil{}, R.TNil{}, R.TNil{}, R.TNil{},
                [I.is_qt(st, 16), I.is_qt(st, 17), I.is_qt(st, 18),
                 I.is_qt(st, 19)], R.TNil{}, R.TNil{}, 0, wid, wcnt)

def fj_scans(+nex: U32, +ex: R.Tr<T.Ex>, +dn: R.Tr<Bool>,
             +strt: R.Tr<U32>) -> C.V:
  a b = fj_sc(nex, ex, dn) fj_sp(nex, ex, strt)
  C.comb(a, b)

def fj_post(+ds: List<&2, K.Dcl>, +st: I.IS, +nex: U32, +ex: R.Tr<T.Ex>,
            +dn: R.Tr<Bool>, +strt: R.Tr<U32>, +wid: U32,
            +wcnt: U32) -> R.Tr<I.Meta> & C.V:
  (fj_meta(ds, st, wid, wcnt), C.VAccept{})

def fj_fin(mv: R.Tr<I.Meta> & C.V, +pre: C.V, +ds: List<&2, K.Dcl>,
           +st: I.IS, +nmt: R.Tr<T.Nm>, +nx: U32, +natn: U32,
           +qtt: R.Tr<U32>, arr: Array<T.Ex>, +wid: U32,
           +wcnt: U32) -> C.V:
  match mv:
    case Tuple{mt, sv}:
      C.comb(C.comb(pre, sv),
             fck_all(ds, st, mt, R.TNil{}, R.TNil{}, R.TNil{}, nmt, nx, natn,
                     qtt, kpow2(M.sdepth(nx)), False{}, C.VAccept{}, 0, wid,
                     wcnt, ((arr, (nx + M.ktbl(nx) + 2 : U32)), C.VAccept{})))

# the literal operations' names (keys 5-7, 11-15, 26-31) marked 1 at
# 2 name + 65, beside their heights at 2 name + 64 (store add_hts): km's
# lazy loop asks "is this head a literal operation" at every step for both
# sides, and Bend evaluated all fourteen lookups of the chained comparison
# strictly
def lit_mark_if(+go: Bool, +q: R.Tr<U32>, +n: U32) -> R.Tr<U32>:
  match go:
    case True{}:
      R.set(U32, 64n, q, ((n * 2 : U32) + 65 : U32), 1, 4294967295)
    case False{}:
      q

def lit_mark1(+q: R.Tr<U32>, +k: U32) -> R.Tr<U32>:
  +q2 : R.Tr<U32> = q
  +n : U32 = R.get(U32, 64n, q2, k, 4294967295)
  lit_mark_if(U32.is_lt(n, 1073741824), q2, n)


def lit_marks(+q: R.Tr<U32>) -> R.Tr<U32>:
  lit_mark1(lit_mark1(lit_mark1(lit_mark1(lit_mark1(lit_mark1(lit_mark1(
  lit_mark1(lit_mark1(lit_mark1(lit_mark1(lit_mark1(lit_mark1(lit_mark1(q,
    5), 6), 7), 11), 12), 13), 14), 15), 26), 27), 28), 29), 30), 31)

# --- the streamed store (fmain's nx path) ---------------------------------
# The expressions are already in the flat store (F.fb_route); the
# expression trie the structural checks read is rebuilt from it.
def exa_bad(+x: T.Ex) -> Bool:
  match x:
    case T.EBad{}:
      True{}
    case _:
      False{}

def ex_from_arr(n: Nat, +i: U32, pr: (Array<T.Ex> & T.Ex) & R.Tr<T.Ex>)
    -> Array<T.Ex> & R.Tr<T.Ex>:
  match n pr:
    case 0n Tuple{Tuple{a, x}, t}:
      (a, t)
    case 1n+p Tuple{Tuple{a, x}, t}:
      +x2 : T.Ex = x
      +i2 : U32 = i
      ex_from_arr(p, (i2 + 1 : U32),
                  (Array.get(T.Ex, a, (i2 + 1 : U32)),
                   R.set_if(T.Ex, Bool.not(exa_bad(x2)), t, i2, x2, T.EBad{})))

def fj_abA2(pr: Array<T.Ex> & R.Tr<T.Ex>, +nx: U32) -> Array<T.Ex> & R.Tr<T.Ex>:
  match pr:
    case Tuple{a, t}:
      +n2 : U32 = nx
      (M.klb_init(U32.to_nat(n2), 0, M.khalf(n2), a), t)

# --- the structural checks' trie: what they can reach, not the export ----
# The structural checks (inductive blocks, recursors, quotients) read
# expressions from a trie; km reads the flat store. Every node they read
# is a subterm of an inductive block's types, constructor and recursor types
# or rule right-hand sides, or of a quotient's type -- or of the declared type
# or value of a constant one of those mentions (I.infer / I.sl through nt,
# I.whd's delta through vt), transitively. That closure is 8-9% of std's and
# cslib's expressions (tools/closure.py); the whole-export trie was ~200 B
# a record of a worker's peak (the arena's runner has 16 GB). A node outside
# it reads as EBad, which some walkers take as "absent" -- so the closure
# must be exact: every constant reached contributes its type AND value. The
# whole-export scans and the self-reference check walk the store instead
# (fj_scan_a, fsr_v).
# cl_tab: key 2n the type of constant n, 2n + 1 its value
def cl_tab_items(items: List<&2, K.IItem>, +t: R.Tr<U32>) -> R.Tr<U32>:
  match items:
    case Nil{}:
      t
    case Con{head, tail}:
      +h = head
      +nm : U32 = B.item_name(h)
      cl_tab_items(tail, R.set_if(U32, U32.is_gt(nm, 0), t, (nm * 2 : U32),
                                  B.item_type(h), 4294967295))

def cl_tab1(+d: K.Dcl, +t: R.Tr<U32>) -> R.Tr<U32>:
  match d:
    case K.DInd{nms, items}:
      cl_tab_items(items, t)
    case _:
      +pd : K.Dcl = d
      +nm : U32 = K.dcl_name(pd)
      +ok : Bool = U32.is_gt(nm, 0)
      R.set_if(U32, ok,
               R.set_if(U32, ok, t, (nm * 2 : U32), K.dcl_type(pd), 4294967295),
               ((nm * 2 : U32) + 1 : U32), K.dcl_value(pd), 4294967295)

def cl_tab(ds: List<&2, K.Dcl>, +t: R.Tr<U32>) -> R.Tr<U32>:
  match ds:
    case Nil{}:
      t
    case Con{head, tail}:
      cl_tab(tail, cl_tab1(head, t))

def cl_item_root(+it: K.IItem, acc: List<&2, U32>) -> List<&2, U32>:
  match it:
    case K.IRule{ct, nf, rhs}:
      Con{rhs, acc}
    case K.IOther{}:
      acc
    case _:
      Con{B.item_type(it), acc}

def cl_roots_items(items: List<&2, K.IItem>,
                   acc: List<&2, U32>) -> List<&2, U32>:
  match items:
    case Nil{}:
      acc
    case Con{head, tail}:
      cl_roots_items(tail, cl_item_root(head, acc))

def cl_roots(ds: List<&2, K.Dcl>, acc: List<&2, U32>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      acc
    case Con{head, tail}:
      match head:
        case K.DInd{nms, items}:
          cl_roots(tail, cl_roots_items(items, acc))
        case K.DQuot{n, lps, t}:
          cl_roots(tail, Con{t, acc})
        case _:
          cl_roots(tail, acc)

# a node's children; a constant seen for the first time adds its type and
# value (cs: the constants seen)
def cl_kc(+seen: Bool, +n: U32, +tab: R.Tr<U32>, +cs: R.Tr<U32>,
          wl: List<&2, U32>) -> List<&2, U32> & R.Tr<U32>:
  match seen:
    case True{}:
      (wl, cs)
    case False{}:
      +t2 : R.Tr<U32> = tab
      (Con{R.get(U32, 64n, t2, (n * 2 : U32), 4294967295),
           Con{R.get(U32, 64n, t2, ((n * 2 : U32) + 1 : U32), 4294967295),
               wl}},
       R.set(U32, 64n, cs, n, 1, 0))

def cl_kids(+x: T.Ex, +tab: R.Tr<U32>, +cs: R.Tr<U32>,
            wl: List<&2, U32>) -> List<&2, U32> & R.Tr<U32>:
  match x:
    case T.EApp{f, a}:
      (Con{f, Con{a, wl}}, cs)
    case T.ELam{n, t, b, bi}:
      (Con{t, Con{b, wl}}, cs)
    case T.EAll{n, t, b, bi}:
      (Con{t, Con{b, wl}}, cs)
    case T.ELet{n, t, v, b}:
      (Con{t, Con{v, Con{b, wl}}}, cs)
    case T.EProj{tn, i, sx}:
      (Con{sx, wl}, cs)
    case T.EConst{n, us}:
      +n2 : U32 = n
      +c2 : R.Tr<U32> = cs
      cl_kc(U32.is_ne(R.get(U32, 64n, c2, n2, 0), 0), n2, tab, c2, wl)
    case _:
      (wl, cs)


# state: ((store, worklist), (trie, constants seen)); one step pops an index
def cl_step4(a: Array<T.Ex>, r: List<&2, U32> & R.Tr<U32>,
             +tr: R.Tr<T.Ex>)
    -> (Array<T.Ex> & List<&2, U32>) & (R.Tr<T.Ex> & R.Tr<U32>):
  match r:
    case Tuple{wl, cs}:
      ((a, wl), (tr, cs))

def cl_step3(pr: Array<T.Ex> & T.Ex, +h: U32, t: List<&2, U32>,
             +tab: R.Tr<U32>, +tr: R.Tr<T.Ex>, +cs: R.Tr<U32>)
    -> (Array<T.Ex> & List<&2, U32>) & (R.Tr<T.Ex> & R.Tr<U32>):
  match pr:
    case Tuple{a, x}:
      +x2 : T.Ex = x
      cl_step4(a, cl_kids(x2, tab, cs, t),
               R.set_if(T.Ex, Bool.not(exa_bad(x2)), tr, h, x2, T.EBad{}))


def cl_step2(+skip: Bool, +h: U32, a: Array<T.Ex>, t: List<&2, U32>,
             +tab: R.Tr<U32>, +tr: R.Tr<T.Ex>, +cs: R.Tr<U32>)
    -> (Array<T.Ex> & List<&2, U32>) & (R.Tr<T.Ex> & R.Tr<U32>):
  match skip:
    case True{}:
      ((a, t), (tr, cs))
    case False{}:
      cl_step3(Array.get(T.Ex, a, h), h, t, tab, tr, cs)

def cl_go(fuel: Nat, +nx: U32, +tab: R.Tr<U32>,
          st: (Array<T.Ex> & List<&2, U32>) & (R.Tr<T.Ex> & R.Tr<U32>))
    -> (Array<T.Ex> & R.Tr<T.Ex>) & Bool:
  match fuel st:
    case 0n Tuple{Tuple{a, wl}, Tuple{tr, cs}}:
      ((a, tr), False{})
    case 1n+p Tuple{Tuple{a, Nil{}}, Tuple{tr, cs}}:
      ((a, tr), True{})
    case 1n+p Tuple{Tuple{a, Con{h, t}}, Tuple{tr, cs}}:
      +h2 : U32 = h
      +tr2 : R.Tr<T.Ex> = tr
      cl_go(p, nx, tab,
            cl_step2(U32.is_ge(h2, nx)
                     || Bool.not(exa_bad(R.get(T.Ex, 64n, tr2, h2, T.EBad{}))),
                     h2, a, t, tab, tr2, cs))

# (store, trie, complete): an incomplete walk (fuel) declines the export
def fj_cl(arr: Array<T.Ex>, +nx: U32,
          +ds: List<&2, K.Dcl>) -> (Array<T.Ex> & R.Tr<T.Ex>) & Bool:
  +d2 : List<&2, K.Dcl> = ds
  cl_go(Nat.mul(4294967295n, 64n), nx, cl_tab(d2, R.TNil{}),
        ((arr, cl_roots(d2, Nil{})), (R.TNil{}, R.TNil{})))

def fj_abA3(r: (Array<T.Ex> & R.Tr<T.Ex>) & Bool,
            +nx: U32) -> (Array<T.Ex> & R.Tr<T.Ex>) & Bool:
  match r:
    case Tuple{pr, ok}:
      (fj_abA2(pr, nx), ok)

# the whole-export trie (fdbg: its scans and self-reference check read it)
def fj_abF(arr: Array<T.Ex>, +nx: U32) -> (Array<T.Ex> & R.Tr<T.Ex>) & Bool:
  +n2 : U32 = nx
  (fj_abA2(ex_from_arr(U32.to_nat(n2), 0, (Array.get(T.Ex, arr, 0), R.TNil{})),
           n2), True{})

def fj_abA(arr: Array<T.Ex>, +nx: U32,
           +ds: List<&2, K.Dcl>) -> (Array<T.Ex> & R.Tr<T.Ex>) & Bool:
  +n2 : U32 = nx
  fj_abA3(fj_cl(arr, n2, ds), n2)

def new_store(+nx: U32) -> Array<T.Ex>:
  Array.new(T.Ex, Nat.add(M.sdepth(nx), 1n), T.EBad{})

# the whole-export scans over the store: an undeclared constant, a
# projection out of a non-structure (check.bend scan_consts / scan_projs)
def sca_go(n: Nat, +i: U32, +dn: R.Tr<Bool>, +strt: R.Tr<U32>, +bad: Bool,
           +v: C.V, pr: Array<T.Ex> & T.Ex) -> Array<T.Ex> & C.V:
  match n pr:
    case 0n Tuple{a, x}:
      (a, C.comb(C.bad_v(bad), v))
    case 1n+p Tuple{a, x}:
      +x2 : T.Ex = x
      +i2 : U32 = i
      sca_go(p, (i2 + 1 : U32), dn, strt, bad || C.bad_const_x(x2, dn),
             C.comb(v, C.proj_x(x2, strt)),
             Array.get(T.Ex, a, (i2 + 1 : U32)))

def fj_scan_a(arr: Array<T.Ex>, +nex: U32, +dn: R.Tr<Bool>,
              +strt: R.Tr<U32>) -> Array<T.Ex> & C.V:
  sca_go(U32.to_nat(nex), 0, dn, strt, False{}, C.VAccept{},
         Array.get(T.Ex, arr, 0))

def fj_fin_s(sp: Array<T.Ex> & C.V, mv: R.Tr<I.Meta> & C.V, +pre: C.V,
             +ds: List<&2, K.Dcl>, +st: I.IS, +nmt: R.Tr<T.Nm>, +nx: U32,
             +natn: U32, +qtt: R.Tr<U32>, +wid: U32, +wcnt: U32) -> C.V:
  match sp:
    case Tuple{arr, sv}:
      fj_fin(mv, C.comb(pre, sv), ds, st, nmt, nx, natn, qtt, arr, wid, wcnt)

def fj_go(+ds: List<&2, K.Dcl>, +nex: U32, +nx: U32,
          ab: (Array<T.Ex> & R.Tr<T.Ex>) & Bool,
          cd: ((R.Tr<U32> & R.Tr<U32>) & R.Tr<U32>) & ((R.Tr<L.LN> & R.Tr<T.Nm>) & (R.Tr<Bool> & (R.Tr<U32> & C.V))),
          +wid: U32, +wcnt: U32) -> C.V:
  match ab cd:
    case Tuple{Tuple{arr, ex}, clok} Tuple{Tuple{Tuple{wk, qtt}, ht}, Tuple{Tuple{ln, nmt}, Tuple{dn, Tuple{strt, pre}}}}:
      +wk2 : R.Tr<U32> = wk
      +ex2 : R.Tr<T.Ex> = ex
      +q2 : R.Tr<U32> = lit_marks(qtt)
      +natn : U32 = R.get(U32, 64n, wk2, 20, 4294967295)
      +strn : U32 = R.get(U32, 64n, wk2, 10, 4294967295)
      +st : I.IS = I.IS{ex2, nx, ln, nx, R.TNil{}, ht, natn, strn, q2}
      +pre2 : C.V = C.comb(pre, C.quot_clash_v(ds, R.get(U32, 64n, wk2, 0, 4294967295),
                                                R.get(U32, 64n, wk2, 1, 4294967295),
                                                R.get(U32, 64n, wk2, 2, 4294967295)))
      +dn2 : R.Tr<Bool> = dn
      +sr2 : R.Tr<U32> = strt
      fj_fin_s(fj_scan_a(arr, nex, dn2, sr2),
               fj_post(ds, st, nex, ex2, dn2, sr2, wid, wcnt),
               C.comb(pre2, C.pick_v(clok, C.VAccept{}, C.VDecline{})), ds, st,
               nmt, nx, natn, q2, wid, wcnt)

# the whole-list path routes the records into the store as the streamed
# one does (F.fb_route), so both intern the lists in record order
def fj_rt2(r: (Array<T.Ex> & (U32 & R.Tr<L.LN>)) & List<&2, D.Rec>)
    -> Array<T.Ex> & R.Tr<L.LN>:
  match r:
    case Tuple{Tuple{a, Tuple{bad, lt}}, kept}:
      (a, lt)

def fj_rt(+recs: List<&2, D.Rec>, +nx: U32) -> Array<T.Ex> & R.Tr<L.LN>:
  fj_rt2(F.fb_route(recs, ((new_store(nx), (0, R.TNil{})), Nil{}), nx))

def fjudge_r(r: Array<T.Ex> & R.Tr<L.LN>, +recs: List<&2, D.Rec>,
             +ds: List<&2, K.Dcl>, +nex: U32, +nlv: Nat, +rounds: Nat,
             +nx: U32, +wid: U32, +wcnt: U32) -> C.V:
  match r:
    case Tuple{arr, lt}:
      ab cd = fj_abA(arr, nx, ds) fj_cd(recs, ds, nlv, rounds, lt)
      fj_go(ds, nex, nx, ab, cd, wid, wcnt)

def fjudge(+recs: List<&2, D.Rec>, +ds: List<&2, K.Dcl>, +nex: U32,
           +nlv: Nat, +rounds: Nat, +nx: U32, +wid: U32, +wcnt: U32) -> C.V:
  fjudge_r(fj_rt(recs, nx), recs, ds, nex, nlv, rounds, nx, wid, wcnt)

# the dynamic-sharing variants: the load as above, the loop state returned
def fj_fin2(mv: R.Tr<I.Meta> & C.V, +pre: C.V, +ds: List<&2, K.Dcl>,
            +st: I.IS, +nmt: R.Tr<T.Nm>, +nx: U32, +natn: U32,
            +qtt: R.Tr<U32>, arr: Array<T.Ex>) -> FL:
  match mv:
    case Tuple{mt, sv}:
      FL{ds, st, mt, R.TNil{}, R.TNil{}, R.TNil{}, nmt, nx, natn, qtt,
         kpow2(M.sdepth(nx)), False{}, C.comb(pre, sv), 0,
         ((arr, (nx + M.ktbl(nx) + 2 : U32)), C.VAccept{})}

def fj_fin2_s(sp: Array<T.Ex> & C.V, mv: R.Tr<I.Meta> & C.V, +pre: C.V,
              +ds: List<&2, K.Dcl>, +st: I.IS, +nmt: R.Tr<T.Nm>, +nx: U32,
              +natn: U32, +qtt: R.Tr<U32>) -> FL:
  match sp:
    case Tuple{arr, sv}:
      fj_fin2(mv, C.comb(pre, sv), ds, st, nmt, nx, natn, qtt, arr)

def fj_go2(+ds: List<&2, K.Dcl>, +nex: U32, +nx: U32,
           ab: (Array<T.Ex> & R.Tr<T.Ex>) & Bool,
           cd: ((R.Tr<U32> & R.Tr<U32>) & R.Tr<U32>) & ((R.Tr<L.LN> & R.Tr<T.Nm>) & (R.Tr<Bool> & (R.Tr<U32> & C.V))),
           +wid: U32, +wcnt: U32) -> FL:
  match ab cd:
    case Tuple{Tuple{arr, ex}, clok} Tuple{Tuple{Tuple{wk, qtt}, ht}, Tuple{Tuple{ln, nmt}, Tuple{dn, Tuple{strt, pre}}}}:
      +wk2 : R.Tr<U32> = wk
      +ex2 : R.Tr<T.Ex> = ex
      +q2 : R.Tr<U32> = lit_marks(qtt)
      +natn : U32 = R.get(U32, 64n, wk2, 20, 4294967295)
      +strn : U32 = R.get(U32, 64n, wk2, 10, 4294967295)
      +st : I.IS = I.IS{ex2, nx, ln, nx, R.TNil{}, ht, natn, strn, q2}
      +pre2 : C.V = C.comb(pre, C.quot_clash_v(ds, R.get(U32, 64n, wk2, 0, 4294967295),
                                                R.get(U32, 64n, wk2, 1, 4294967295),
                                                R.get(U32, 64n, wk2, 2, 4294967295)))
      +dn2 : R.Tr<Bool> = dn
      +sr2 : R.Tr<U32> = strt
      fj_fin2_s(fj_scan_a(arr, nex, dn2, sr2),
                fj_post(ds, st, nex, ex2, dn2, sr2, wid, wcnt),
                C.comb(pre2, C.pick_v(clok, C.VAccept{}, C.VDecline{})), ds,
                st, nmt, nx, natn, q2)

def fjudge2_r(r: Array<T.Ex> & R.Tr<L.LN>, +recs: List<&2, D.Rec>,
              +ds: List<&2, K.Dcl>, +nex: U32, +nlv: Nat, +rounds: Nat,
              +nx: U32, +wid: U32, +wcnt: U32) -> FL:
  match r:
    case Tuple{arr, lt}:
      ab cd = fj_abA(arr, nx, ds) fj_cd(recs, ds, nlv, rounds, lt)
      fj_go2(ds, nex, nx, ab, cd, wid, wcnt)

def fjudge2(+recs: List<&2, D.Rec>, +ds: List<&2, K.Dcl>, +nex: U32,
            +nlv: Nat, +rounds: Nat, +nx: U32, +wid: U32, +wcnt: U32) -> FL:
  fjudge2_r(fj_rt(recs, nx), recs, ds, nex, nlv, rounds, nx, wid, wcnt)

def fjudgeA(+recs: List<&2, D.Rec>, arr: Array<T.Ex>, +lt: R.Tr<L.LN>,
            +ds: List<&2, K.Dcl>, +nlv: Nat, +rounds: Nat, +nx: U32,
            +wid: U32, +wcnt: U32) -> C.V:
  +n2 : U32 = nx
  ab cd = fj_abA(arr, n2, ds) fj_cd(recs, ds, nlv, rounds, lt)
  fj_go(ds, n2, n2, ab, cd, wid, wcnt)

def fjudge2A(+recs: List<&2, D.Rec>, arr: Array<T.Ex>, +lt: R.Tr<L.LN>,
             +ds: List<&2, K.Dcl>, +nlv: Nat, +rounds: Nat, +nx: U32,
             +wid: U32, +wcnt: U32) -> FL:
  +n2 : U32 = nx
  ab cd = fj_abA(arr, n2, ds) fj_cd(recs, ds, nlv, rounds, lt)
  fj_go2(ds, n2, n2, ab, cd, wid, wcnt)

# fork mode (fmain run_fk): fjudge2A in two halves. fsetupA builds the
# tables every worker reads (the structural closure, the declaration
# tables) once, before the workers are forked, so they share them; fgo2A is
# a worker's rest
def fsetupA(+recs: List<&2, D.Rec>, arr: Array<T.Ex>, +lt: R.Tr<L.LN>,
            +ds: List<&2, K.Dcl>, +nlv: Nat, +rounds: Nat, +nx: U32) -> ((Array<T.Ex> & R.Tr<T.Ex>) & Bool) & (((R.Tr<U32> & R.Tr<U32>) & R.Tr<U32>) & ((R.Tr<L.LN> & R.Tr<T.Nm>) & (R.Tr<Bool> & (R.Tr<U32> & C.V)))):
  +n2 : U32 = nx
  ab cd = fj_abA(arr, n2, ds) fj_cd(recs, ds, nlv, rounds, lt)
  (ab, cd)

def fgo2A(+ds: List<&2, K.Dcl>, +nx: U32, su: ((Array<T.Ex> & R.Tr<T.Ex>) & Bool) & (((R.Tr<U32> & R.Tr<U32>) & R.Tr<U32>) & ((R.Tr<L.LN> & R.Tr<T.Nm>) & (R.Tr<Bool> & (R.Tr<U32> & C.V)))),
          +wid: U32, +wcnt: U32) -> FL:
  match su:
    case Tuple{ab, cd}:
      fj_go2(ds, nx, nx, ab, cd, wid, wcnt)
