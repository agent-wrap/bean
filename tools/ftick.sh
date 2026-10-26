#!/usr/bin/env bash
# Build a per-declaration TIMING variant of the flat checker:
#     tools/ftick.sh OUT
# Patches the generated C so that entering fcheck's fck_sel (one per
# declaration, in export order) and block_v (inductive blocks) logs to stderr:
#     SLOW decl=<index> blk=<0|1> dt=<seconds> at=<since first decl>
# for every declaration over 0.3 s, PROG every 5000 declarations, and
#     VERD decl=<index> v=<1 reject | 2 decline> fl=<OVF|CORRUPT<<1|INCOMPLETE<<2> mv=<raw machine register>
# for every declaration that does not accept. The
# index counts declaration records (axiom/def/thm/opaque/quot/inductive) in
# file order from 0 (fck_all's own counter). SRC=DIR builds a copy. Verdicts are unchanged. Found the init hang
# (String.Pos.Raw.IsValid) after prefix bisection proved timing-dependent.
set -euo pipefail
OUT="$1"
DIR="$(cd "$(dirname "$0")" && pwd)"
TMP="$(mktemp -d)"
"$DIR/bend.sh" "${SRC:-$DIR/../src}/fmain.bend" -o "$TMP/gen.c"
python3 - "$TMP/gen.c" <<'PY'
import sys
p = sys.argv[1]; s = open(p).read()
tick = r'''
#include <time.h>
static double dbg_now(void){struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+t.tv_nsec*1e-9;}
static long dbg_decl=-1, dbg_cur=0; static double dbg_t0=0, dbg_last=0; static int dbg_isblk=0;
static unsigned dbg_fl=0, dbg_mv=0; /* the last typed check's flag bits (OVF|CORRUPT<<1|INCOMPLETE<<2) and raw verdict register */
static void dbg_tick(int kind){
  double n=dbg_now(); if(dbg_t0==0){dbg_t0=n;dbg_last=n;}
  if(kind==0){ double dt=n-dbg_last; if(dt>0.3 && dbg_decl>=0) fprintf(stderr,"SLOW decl=%ld blk=%d dt=%.2f at=%.1f\n",dbg_decl,dbg_isblk,dt,n-dbg_t0);
    dbg_decl=dbg_cur; dbg_last=n; dbg_isblk=0; if(dbg_decl%5000==0) fprintf(stderr,"PROG decl=%ld at=%.1f\n",dbg_decl,n-dbg_t0);}
  else { dbg_isblk=1; }
}
'''
i = s.index('static void err_fail'); s = s[:i] + tick + s[i:]
# fck_all's last argument is the PREVIOUS declaration's ((store, nx), verdict),
# unboxed: the verdict is the enum index in register _fr_2 (0 accept,
# 1 reject, 2 decline) -- log every non-accept against that declaration
import re
m = re.search(r"    u32 _ix_0 = r(\d+);\n(?:    u32 _w[a-z]+_0 = r\d+;\n)*    Term _fr_0 = r\d+;\n    u32 _fr_1 = r\d+;\n    u32 _fr_2 = r\d+;\n", s)
assert m, 'fck_all registers moved'
# the index fck_all carries is the NEXT declaration's; the verdict it
# receives is the previous one's
s = s[:m.end()] + '    dbg_cur = (long)_ix_0; if (_fr_2 != 0) { fprintf(stderr, "VERD decl=%ld v=%u fl=%u mv=%u\\n", (long)_ix_0 - 1, _fr_2, dbg_fl, dbg_mv); } dbg_fl = 0; dbg_mv = 0;\n' + s[m.end():]
# fck_fold (inlined into a spin helper): the flag bits come back from the
# kfl_flags helper into _v_N, the machine's verdict register is _kr_2
m2 = re.search(r"  u32 _sv_0 = r6;\n  u32 _base_0 = r7;\n  WL_SPIN\n(?:.*\n){0,12}?    (_v_\d+) = \(u32\)_o_\d+\[1\];\n", s)
assert m2, 'fck_fold registers moved'
s = s[:m2.end()] + f'    dbg_fl = {m2.group(1)}; dbg_mv = _kr_2;\n' + s[m2.end():]
for fid, k in (('FID_FCHECK_FCK_SEL', 0), ('FID_FCHECK_BLOCK_V', 1)):
    a = f"  WL_CASE({fid})\n  {{\n"
    assert s.count(a) == 1, fid
    s = s.replace(a, a + f"    dbg_tick({k});\n")
open(p, 'w').write(s)
PY
NIXCLANG=/nix/store/fy71z4s85kl6114vz7ksp3m5z4fz275k-clang-wrapper-21.1.8/bin/clang
exec "$NIXCLANG" -O2 -o "$OUT" "$TMP/gen.c" -lpthread
