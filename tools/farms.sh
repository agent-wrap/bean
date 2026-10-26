#!/usr/bin/env bash
# Per-arm step histogram of the flat machine: builds fmain with a counter at
# km's dispatch (the frame constructor) and dumps the top 40 arms on SIGTERM
# or at exit, so a run capped with `timeout` still reports.
#
#     tools/farms.sh OUT            # then: timeout 120 OUT EXPORT [K N] 2>arms.txt
#
# ARM lines: `ARM CID_KM_<frame> <steps>`; ARMS total first. On std's
# blastDivSubtractShift_denote_mem_prefix this found 3.78G steps in 120 s
# with 1.35G in KEvM (the unmemoised instantiate-several walk) where the
# counting probes (tools/fprobe.sh) showed 597 betas and 191 unfolds.
# SRC=DIR builds a copy.
set -euo pipefail
OUT="$1"
DIR="$(cd "$(dirname "$0")" && pwd)"
TMP="$(mktemp -d)"
"$DIR/bend.sh" "${SRC:-$DIR/../src}/fmain.bend" -o "$TMP/gen.c"
python3 - "$TMP/gen.c" <<'PY'
import sys, re
p = sys.argv[1]; s = open(p).read()
names = re.findall(r'#define (CID_[A-Z0-9_]+) (\d+)', s)
maxid = max(int(n) for _, n in names)
tbl = ['"?"'] * (maxid + 1)
for n, v in names: tbl[int(v)] = '"%s"' % n
hist = '''
#include <signal.h>
static unsigned long dbg_arm[%d];
static const char* dbg_arm_names[%d] = {%s};
static void dbg_dump_arms(void){
  unsigned long tot = 0; for (int i = 0; i < %d; i++) tot += dbg_arm[i];
  fprintf(stderr, "ARMS total %%lu\\n", tot);
  for (int r = 0; r < 40; r++) { int bi = -1; unsigned long bv = 0;
    for (int i = 0; i < %d; i++) if (dbg_arm[i] > bv) { bv = dbg_arm[i]; bi = i; }
    if (bi < 0 || bv == 0) break; fprintf(stderr, "ARM %%s %%lu\\n", dbg_arm_names[bi], bv); dbg_arm[bi] = 0; }
  fflush(stderr);
}
static void dbg_dump_sig(int sig){ dbg_dump_arms(); _exit(0); }
''' % (maxid + 1, maxid + 1, ','.join(tbl), maxid + 1, maxid + 1)
i = s.index('static void err_fail'); s = s[:i] + hist + s[i:]
m = re.search(r'\nint main\([^)]*\)\s*\{\n', s); assert m, 'main'
s = s[:m.end()] + '  signal(SIGTERM, dbg_dump_sig); signal(SIGINT, dbg_dump_sig); atexit(dbg_dump_arms);\n' + s[m.end():]
L = s.index('  WL_CASE(FID_KM_KM)\n')
line = '        Term _f_0 = e.mem[_sp_0 + 0];\n'
j = s.index(line, L)
s = s[:j] + line + '        dbg_arm[term_aux(_f_0) < %d ? term_aux(_f_0) : 0]++;\n' % (maxid + 1) + s[j+len(line):]
open(p, 'w').write(s)
PY
NIXCLANG=/nix/store/fy71z4s85kl6114vz7ksp3m5z4fz275k-clang-wrapper-21.1.8/bin/clang
exec "$NIXCLANG" -O2 -o "$OUT" "$TMP/gen.c" -lpthread
