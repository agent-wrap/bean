#!/usr/bin/env bash
# Frame-key COUNTING variant of the flat checker:
#     FRAMES="CID_KM_KEVI:2:1,CID_KM_WDELGO:2" tools/fkey.sh OUT   (SRC=DIR builds a copy)
# For each km frame constructor CID:F[:G], every dispatch on that frame counts
# the value of its field F (and G, packed as F*2^32+G) in a hash table; at
# exit stderr gets `FKEY cid total distinct` and the top 30 `FKT cid key count`.
# Says whether a walk/cache re-enters the same keys (a memo that misses) or
# genuinely distinct ones. SIGTERM (timeout) dumps too.
set -euo pipefail
OUT="$1"
DIR="$(cd "$(dirname "$0")" && pwd)"
TMP="$(mktemp -d)"
"$DIR/bend.sh" "${SRC:-$DIR/../src}/fmain.bend" -o "$TMP/gen.c"
python3 - "$TMP/gen.c" "$FRAMES" <<'PY'
import sys, re
p, frames = sys.argv[1], sys.argv[2]; s = open(p).read()
specs = []
for f in frames.split(','):
    parts = f.split(':'); specs.append((parts[0], int(parts[1]), int(parts[2]) if len(parts) > 2 else None))
n = len(specs)
hdr = r'''
#define FK_N (1u<<24)
typedef struct { unsigned long long k; unsigned long long c; } fk_e;
static fk_e* fk_t[%d]; static unsigned long long fk_tot[%d], fk_dist[%d];
static const char* fk_nm[%d] = {%s};
static void fk_rec(int t, unsigned long long k){ if(!fk_t[t]) fk_t[t]=calloc(FK_N,sizeof(fk_e)); fk_tot[t]++;
  unsigned h=(unsigned)((k*11400714819323198485ull)>>40)&(FK_N-1); fk_e* T=fk_t[t];
  while(T[h].c && T[h].k!=k) h=(h+1)&(FK_N-1); if(!T[h].c){ T[h].k=k; fk_dist[t]++; } T[h].c++; }
static int fk_cmp(const void*a,const void*b){ unsigned long long x=((const fk_e*)a)->c, y=((const fk_e*)b)->c; return x<y?1:x>y?-1:0; }
static void fk_dump(void){ for(int t=0;t<%d;t++){ fprintf(stderr,"FKEY %%s total=%%llu distinct=%%llu\n",fk_nm[t],fk_tot[t],fk_dist[t]); if(!fk_t[t]) continue;
  qsort(fk_t[t],FK_N,sizeof(fk_e),fk_cmp); for(int i=0;i<30&&fk_t[t][i].c;i++) fprintf(stderr,"FKT %%s %%llu:%%llu %%llu\n",fk_nm[t],fk_t[t][i].k>>32,fk_t[t][i].k&0xffffffffull,fk_t[t][i].c); } }
''' % (n, n, n, n, ",".join('"%s"' % c for c, _, _ in specs), n)
i = s.index("static void err_fail"); s = s[:i] + hdr + s[i:]
for t, (cid, F, G) in enumerate(specs):
    pat = re.compile(r"(\} else if \(term_aux\(_f_0\) == %s\) \{\n\s*u64 (_sp_\d+) = term_loc\(_f_0\);\n)((?:\s*(?:u32|Term) _f_\d+ = e\.mem\[_sp_\d+ \+ \d+\];\n)+)" % cid)
    cnt = [0]
    def rep(m):
        cnt[0] += 1
        fl = re.findall(r"(?:u32|Term) (_f_\d+) = e\.mem\[_sp_\d+ \+ (\d+)\]", m.group(3))
        d = dict((int(b), a) for a, b in fl)
        key = "((unsigned long long)(unsigned)%s<<32)" % d[F] + ("|(unsigned)%s" % d[G] if G is not None else "")
        return m.group(1) + m.group(3) + "          fk_rec(%d, %s);\n" % (t, key)
    s = pat.sub(rep, s)
    assert cnt[0] >= 1, cid
s = s.replace("static void err_fail", "#include <signal.h>\nstatic void fk_term(int sg){ fk_dump(); _exit(143); }\nstatic void err_fail", 1)
s = s.replace("int main(int argc, char** argv) {\n", "int main(int argc, char** argv) {\n  atexit(fk_dump); signal(SIGTERM, fk_term);\n", 1)
open(p, 'w').write(s)
PY
NIXCLANG=/nix/store/fy71z4s85kl6114vz7ksp3m5z4fz275k-clang-wrapper-21.1.8/bin/clang
"$NIXCLANG" -O2 -o "$OUT" "$TMP/gen.c" -lpthread
codesign -s - -f "$OUT" 2>/dev/null || true
