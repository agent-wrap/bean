#!/usr/bin/env bash
# Build a FRAME PROFILER variant of the flat checker:
#     tools/fprof.sh OUT
# km is one continuation machine: every step dispatches on the frame at the
# top of its stack. This patches km's entry in the generated C to count the
# top frame's constructor at each step and, at exit (or SIGTERM), prints the
# 40 most frequent frames to stderr:  PROF <count> <frame>
# The C-level sampler only ever shows `km`; this shows which part of the
# machine (whnf phases, defeq stages, the lazy probe, inference) the steps go to.
# ALLOC=1: count store GROWTH (nodes allocated) per frame instead of steps.
set -euo pipefail
OUT="$1"
DIR="$(cd "$(dirname "$0")" && pwd)"
TMP="$(mktemp -d)"
"$DIR/bend.sh" "$DIR/../src/fmain.bend" -o "$TMP/gen.c"
python3 - "$TMP/gen.c" <<'PY'
import re, sys
p = sys.argv[1]; s = open(p).read()
cids = re.findall(r"#define (CID_[A-Z0-9_]+) (\d+)", s)
mx = max(int(v) for _, v in cids) + 1
names = ["?"] * mx
for n, v in cids: names[int(v)] = n[4:]
hdr = r'''
#include <signal.h>
#include <stdlib.h>
static unsigned long long prof_cnt[%d];
static const char* prof_nm[%d] = {%s};
static int prof_cmp(const void* a, const void* b){ unsigned long long x=prof_cnt[*(int*)a], y=prof_cnt[*(int*)b]; return x<y?1:(x>y?-1:0); }
static void prof_dump(void){ int ix[%d]; for(int i=0;i<%d;i++) ix[i]=i; qsort(ix,%d,sizeof(int),prof_cmp);
  for(int j=0;j<40&&j<%d;j++){ if(!prof_cnt[ix[j]]) break; fprintf(stderr,"PROF %%12llu %%s\n",prof_cnt[ix[j]],prof_nm[ix[j]]); } }
static void prof_sig(int sg){ prof_dump(); _exit(3); }
static int prof_init=0;
static const unsigned char prof_sub[%d] = {%s};
''' % (mx, mx, ",".join('"%s"' % n for n in names), mx, mx, mx, mx, mx,
       ",".join('1' if (n.startswith('KM_K') and n not in ('KM_KCON','KM_KNIL')) else '0' for n in names))
i = s.index('static void err_fail'); s = s[:i] + hdr + s[i:]
s = s.replace("static void err_fail(const char* msg) {\n  fflush(stdout);", "static void err_fail(const char* msg) {\n  prof_dump(); fflush(stdout);", 1)
a = "  WL_CASE(FID_KM_KM)\n  {\n"
assert s.count(a) == 1
import os
if os.environ.get('ALLOC'):
    # attribute store growth (nx, register r13) to the frame of the PREVIOUS step
    hit = '''    if(!prof_init){prof_init=1; atexit(prof_dump); signal(SIGTERM, prof_sig);}
    { static u32 _plast_nx = 0; static u64 _plast_c = 0; u32 _pnx = (u32)r13;
      if (_plast_c < %d && _pnx > _plast_nx && _pnx - _plast_nx < 1000000) prof_cnt[_plast_c] += _pnx - _plast_nx;
      _plast_nx = _pnx; _plast_c = %d;
      Term _ps = r1; int _pd = 0;
      while (term_aux(_ps) == CID_KM_KCON && _pd < 64) { u64 _pl = term_peek(e.mem, _ps); Term _pf = e.mem[_pl]; u64 _pc = term_aux(_pf);
        if (_pc < %d && !prof_sub[_pc]) { _plast_c = _pc; break; } _ps = e.mem[_pl + 1]; _pd++; } }
''' % (mx, mx, mx)
else:
    hit = '''    if(!prof_init){prof_init=1; atexit(prof_dump); signal(SIGTERM, prof_sig);}
    { Term _ps = r1; if (term_aux(_ps) == CID_KM_KCON) { u64 _pl = term_peek(e.mem, _ps); Term _pf = e.mem[_pl]; u64 _pc = term_aux(_pf); if (_pc < %d) prof_cnt[_pc]++; } }
''' % mx
s = s.replace(a, a + hit)
open(p, 'w').write(s)
PY
NIXCLANG=/nix/store/fy71z4s85kl6114vz7ksp3m5z4fz275k-clang-wrapper-21.1.8/bin/clang
exec "$NIXCLANG" -O2 -o "$OUT" "$TMP/gen.c" -lpthread
