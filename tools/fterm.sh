#!/usr/bin/env bash
# Term dump at a defeq entry, for a run that declines or never ends:
#     tools/fterm.sh X Y OUT       (then: OUT SLICE K N 2>&1 >/dev/null | grep ^PT > TOKS;
#                                   python3 tools/fterm_dec.py SLICE TOKS DEPTH)
# Builds the checker from a copy of src whose DSub arm, the first time the
# pair (X, Y) of store indices is entered, walks both terms (preorder, 4000
# nodes each) through kprb_w; the generated C's token additions are patched
# into prb_tok, which prints `PT token` (200k at most). fprobe's dump goes
# through the memo trie and is lost when the declaration declines; this
# prints as it happens. X, Y come from tools/fkey.sh (FRAMES=CID_KM_DSUB:2:3)
# on the same source -- the store indices are deterministic.
set -euo pipefail
X="$1"; Y="$2"; OUT="$3"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TMP="$(mktemp -d)"; mkdir -p "$TMP/src"; /bin/cp -f "$ROOT"/src/*.bend "$TMP/src/"
python3 - "$TMP/src/km.bend" "$X" "$Y" <<'PY'
import sys
p, x, y = sys.argv[1:]; s = open(p).read()
W = r'''def kprb_tok(n: Nat, +t: U32, +acc: U32) -> U32:
  match n:
    case 0n:
      acc
    case 1n+p:
      kprb_tok(p, t, (acc + t : U32))

def kprb_pk(a: Array<T.Ex>, work: List<&2, U32>) -> (Array<T.Ex> & T.Ex) & List<&2, U32>:
  match work:
    case Nil{}:
      ((a, T.EBad{}), Nil{})
    case Con{h, t}:
      (Array.get(T.Ex, a, h), t)

def kprb_w(fuel: Nat, st: (Array<T.Ex> & T.Ex) & List<&2, U32>,
           +acc: U32) -> Array<T.Ex> & U32:
  match fuel st:
    case 0n Tuple{Tuple{a, nd}, work}:
      (a, kprb_tok(1n, 4294966003, acc))
    case 1n+p Tuple{Tuple{a, nd}, work}:
      match nd:
        case T.EApp{f, g}:
          kprb_w(p, kprb_pk(a, Con{f, Con{g, work}}), kprb_tok(1n, 1, acc))
        case T.ELam{n, t, b, bi}:
          kprb_w(p, kprb_pk(a, Con{t, Con{b, work}}), kprb_tok(1n, 2, acc))
        case T.EAll{n, t, b, bi}:
          kprb_w(p, kprb_pk(a, Con{t, Con{b, work}}), kprb_tok(1n, 3, acc))
        case T.ELet{n, t, v, b}:
          kprb_w(p, kprb_pk(a, Con{t, Con{v, Con{b, work}}}), kprb_tok(1n, 4, acc))
        case T.EProj{tn, i, sx}:
          kprb_w(p, kprb_pk(a, Con{sx, work}),
                 kprb_tok(1n, i, kprb_tok(1n, tn, kprb_tok(1n, 5, acc))))
        case T.EConst{n, us}:
          kprb_w(p, kprb_pk(a, work), kprb_tok(1n, n, kprb_tok(1n, 6, acc)))
        case T.EBVar{i}:
          kprb_w(p, kprb_pk(a, work), kprb_tok(1n, i, kprb_tok(1n, 7, acc)))
        case T.ESort{l}:
          kprb_w(p, kprb_pk(a, work), kprb_tok(1n, 12, acc))
        case T.ENat{d}:
          kprb_w(p, kprb_pk(a, work), kprb_tok(1n, 9, acc))
        case T.EBad{}:
          (a, acc)
        case _:
          kprb_w(p, kprb_pk(a, work), kprb_tok(1n, 11, acc))

def kprb_y(pr: Array<T.Ex> & U32, +y: U32) -> Array<T.Ex> & U32:
  match pr:
    case Tuple{a, acc}:
      kprb_w(4000n, (Array.get(T.Ex, a, y), Nil{}), kprb_tok(1n, 4294966000, acc))

def kprb_fin(pr: Array<T.Ex> & U32, +nx: U32) -> Array<T.Ex> & U32:
  match pr:
    case Tuple{a, acc}:
      (a, nx)

def kprb_go(+c: Bool, fs: Array<T.Ex> & U32, +x: U32, +y: U32) -> Array<T.Ex> & U32:
  match c fs:
    case True{} Tuple{a, nx}:
      kprb_fin(kprb_y(kprb_w(4000n, (Array.get(T.Ex, a, x), Nil{}),
                             kprb_tok(1n, 4294966002, 0)), y), nx)
    case False{} Tuple{a, nx}:
      (a, nx)

'''
s = s.replace("\ndef krigid(", "\n" + W + "def krigid(", 1)
arm = """    case 1n+p KCon{DSub{False{}, False{}, xi, yi, ctx, fu}, k}
         Tuple{Tuple{fs, msg}, ri}:
      +x2 : U32 = xi
      +y2 : U32 = yi
"""
i = s.index(arm) + len(arm)
s = s[:i] + "      fsd = kprb_go(U32.is_eq(x2, %s) && U32.is_eq(y2, %s), fs, x2, y2)\n" % (x, y) + s[i:]
j = s.index("knoop(fs, ri))", i); s = s[:j] + "knoop(fsd, ri))" + s[j + len("knoop(fs, ri))"):]
open(p, "w").write(s)
PY
"$ROOT/tools/bend.sh" "$TMP/src/fmain.bend" -o "$TMP/gen.c"
python3 - "$TMP/gen.c" <<'PY'
import sys, re
p = sys.argv[1]; L = open(p).read().split("\n")
i = [k for k, l in enumerate(L) if "4294966003ull" in l][0]
s = i
while s > 0 and not re.match(r"^(FAR|INLINE|static|OUTLINE)\b", L[s]): s -= 1
e = i
while e < len(L) - 1 and not re.match(r"^(FAR|INLINE|static|OUTLINE)\b", L[e + 1]): e += 1
sub = lambda l: re.sub(r"U32_BIN\((\w+), \+, (\w+)\)", r"prb_tok(\1, \2)", l)
for k in range(s, e + 1): L[k] = sub(L[k])
for k in range(len(L)):
    if "4294966002ull" in L[k] or "4294966000ull" in L[k]: L[k] = sub(L[k])
src = "\n".join(L)
hdr = 'static unsigned long prb_n = 0;\nstatic unsigned prb_tok(unsigned a, unsigned t){ if (prb_n < 200000) { fprintf(stderr, "PT %u\\n", t); prb_n++; } return a + t; }\n'
j = src.index("static void err_fail"); src = src[:j] + hdr + src[j:]
open(p, "w").write(src)
PY
/nix/store/fy71z4s85kl6114vz7ksp3m5z4fz275k-clang-wrapper-21.1.8/bin/clang -O2 -o "$OUT" "$TMP/gen.c" -lpthread
codesign -s - -f "$OUT"
