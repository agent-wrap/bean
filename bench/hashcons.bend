# Hash-consing primitive for the flat store, in the shape that actually
# compiles in Bend -- the remaining core for the port (docs/port-plan.md).
#
# Earlier attempts hit Bend's no-mutual-recursion wall: open addressing with
# early stop is a return-or-recurse branch that needs a callback. The fix is
# a BOUNDED, fixed-K scan that ALWAYS iterates K slots (one Array read per
# iteration), accumulating first-match and first-empty branchlessly -- no
# early return, so one self-recursive def suffices. Insert always fills the
# first empty within K, so a present node sits in the occupied prefix before
# the first empty; `stopped` gates matches seen after an empty.
#
# The hash table is a REGION of the node Array itself ([base, base+size)),
# so there is no second array and no store-widening: the integration keeps
# the machine's fs = (ex & nx) and only changes kalloc.
#
# Test: 1,000,000 allocations of 10 distinct structures must end with 10
# occupied hash slots (every repeat shares). An append-only store would use
# 1,000,000.

import Base

def pick_u(+z: Bool, +x: U32, +y: U32) -> U32:
  match z:
    case True{}:
      x
    case False{}:
      y

type Nd is Data:
  NBad{}
  NLeaf{v: U32}
  NApp{f: U32, a: U32}

def is_bad(+x: Nd) -> Bool:
  match x:
    case NBad{}:
      True{}
    case _:
      False{}

def nd_eq(+x: Nd, +y: Nd) -> Bool:
  match x y:
    case NLeaf{v} NLeaf{w}:
      U32.is_eq(v, w)
    case NApp{f, a} NApp{g, b}:
      U32.is_eq(f, g) && U32.is_eq(a, b)
    case _ _:
      False{}

def mix(+h: U32, +x: U32) -> U32:
  (U32.xor(h, x) * 16777619 : U32)

def fp(+node: Nd) -> U32:
  match node:
    case NBad{}:
      0
    case NLeaf{v}:
      mix(mix(2166136261, 1), v)
    case NApp{f, a}:
      mix(mix(mix(2166136261, 2), f), a)

def nxt(+base: U32, +mask: U32, +slot: U32) -> U32:
  (base + U32.and((slot + 1 - base : U32), mask) : U32)

# fixed-K scan: always K iterations, one ex read each, branchless accumulate
def kscan(k: Nat, +base: U32, +mask: U32, +node: Nd, +slot: U32,
          +found: U32, +fempty: U32, +stopped: Bool,
          pr: Array<Nd> & Nd) -> Array<Nd> & U32 & U32:
  match k pr:
    case 0n Tuple{ex, cand}:
      (ex, (found, fempty))
    case 1n+p Tuple{ex, cand}:
      +cd : Nd = cand
      +eb : Bool = is_bad(cd)
      +hit : Bool = Bool.not(stopped) && nd_eq(cd, node)
                    && U32.is_eq(found, 4294967295)
      +found2 : U32 = pick_u(hit, slot, found)
      +fe2 : U32 = pick_u(eb && U32.is_eq(fempty, 4294967295), slot, fempty)
      +slot2 : U32 = nxt(base, mask, slot)
      kscan(p, base, mask, node, slot2, found2, fe2,
            Bool.or(stopped, eb), Array.get(Nd, ex, slot2))

# share / insert-at-first-empty / overflow-append (non-recursive)
def kfinish2_b(+miss: Bool, +fempty: U32, ex: Array<Nd>, +node: Nd,
               +nx: U32) -> Array<Nd> & U32:
  match miss:
    case False{}:
      (Array.set(Nd, ex, fempty, node), fempty)
    case True{}:
      +n : U32 = nx
      (Array.set(Nd, ex, n, node), n)

def kfinish2(+fempty: U32, ex: Array<Nd>, +node: Nd,
             +nx: U32) -> Array<Nd> & U32:
  kfinish2_b(U32.is_eq(fempty, 4294967295), fempty, ex, node, nx)

def kfinish_b(+miss: Bool, +found: U32, +fempty: U32, ex: Array<Nd>,
              +node: Nd, +nx: U32) -> Array<Nd> & U32:
  match miss:
    case False{}:
      (ex, found)
    case True{}:
      kfinish2(fempty, ex, node, nx)

def kfinish(+found: U32, +fempty: U32, ex: Array<Nd>, +node: Nd,
            +nx: U32) -> Array<Nd> & U32:
  kfinish_b(U32.is_eq(found, 4294967295), found, fempty, ex, node, nx)

def kfin(r: Array<Nd> & U32 & U32, +node: Nd,
         +nx: U32) -> Array<Nd> & U32:
  match r:
    case Tuple{ex, Tuple{found, fempty}}:
      kfinish(found, fempty, ex, node, nx)

def kalloc_hc(+base: U32, +mask: U32, +node: Nd, +nx: U32,
              ex: Array<Nd>) -> Array<Nd> & U32:
  +s0 : U32 = (base + U32.and(fp(node), mask) : U32)
  kfin(kscan(16n, base, mask, node, s0, 4294967295, 4294967295,
             False{}, Array.get(Nd, ex, s0)),
       node, nx)

# allocate NApp{i%10, i%10}; the previous kalloc result threads in as pr and
# is matched at entry, so this stays single self-recursive (no build_go
# callback). nx is the overflow counter.
def build(n: Nat, +base: U32, +mask: U32, +i: U32, +nx: U32,
          pr: Array<Nd> & U32) -> U32:
  match n pr:
    case 0n Tuple{ex, idx}:
      nx
    case 1n+p Tuple{ex, idx}:
      +id : U32 = idx
      +nx2 : U32 = pick_u(U32.is_ge(id, nx), (id + 1 : U32), nx)
      build(p, base, mask, (i + 1 : U32), nx2,
            kalloc_hc(base, mask, NApp{(i % 10 : U32), (i % 10 : U32)},
                      nx2, ex))

def idx_of(r: Array<Nd> & U32) -> Array<Nd> & U32:
  r

def three4(+a: U32, +b: U32, rc: Array<Nd> & U32) -> U32:
  match rc:
    case Tuple{ex3, c}:
      (a * 1000000 + b * 1000 + c : U32)

def three3(+a: U32, rb: Array<Nd> & U32) -> U32:
  match rb:
    case Tuple{ex2, b}:
      three4(a, b, kalloc_hc(16, 1023, NApp{0, 0}, 1040, ex2))

def three2(ra: Array<Nd> & U32) -> U32:
  match ra:
    case Tuple{ex1, a}:
      three3(a, kalloc_hc(16, 1023, NApp{1, 1}, 1040, ex1))

def three_enc(e0: Array<Nd> & U32) -> U32:
  match e0:
    case Tuple{ex0, _}:
      three2(kalloc_hc(16, 1023, NApp{0, 0}, 1040, ex0))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("A,B,C packed a*1000000+b*1000+c (want a==c, a!=b): "
             ++ U32.show(three_enc((Array.new(Nd, 12n, NBad{}), 0))))
    IO.print("big-run overflow (want 0): "
             ++ U32.show((build(1000000n, 16, 1023, 0, 1040, (Array.new(Nd, 12n, NBad{}), 1039)) - 1040
                          : U32)))
