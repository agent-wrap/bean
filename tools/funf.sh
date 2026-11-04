#!/usr/bin/env bash
# Delta-unfold COUNTING variant of the flat checker:
#     tools/funf.sh OUT        (SRC=DIR builds a copy)
# Patches the generated C so that km's WDelGo arm (an unfold attempt, can=1)
# and WDelH miss arm (a real unfold: the body is instantiated) count per value
# node vi; at exit every nonzero one goes to stderr as `UNFC vi att real`.
# tools/unfname.py SLICE ERR names them; join with tools/kdiag's DIAG lines
# (Lean's Kernel.Diagnostics unfold counter) for a differential profile.
# SIGTERM (timeout) dumps too. Run one declaration with argv `K N` (K < N, N = declaration count).
set -euo pipefail
OUT="$1"
DIR="$(cd "$(dirname "$0")" && pwd)"
TMP="$(mktemp -d)"
"$DIR/bend.sh" "${SRC:-$DIR/../src}/fmain.bend" -o "$TMP/gen.c"
python3 - "$TMP/gen.c" <<'PY'
import sys, re
p = sys.argv[1]; s = open(p).read()
hdr = r'''
#define UNF_N (1u<<22)
static unsigned unf_key[UNF_N], unf_att[UNF_N], unf_real[UNF_N];
static unsigned unf_slot(unsigned k){ unsigned h=(k*2654435761u)&(UNF_N-1); while(unf_key[h]!=k+1){ if(unf_key[h]==0){unf_key[h]=k+1; break;} h=(h+1)&(UNF_N-1);} return h; }
static void unf_rec(unsigned vi,int real){ unsigned h=unf_slot(vi); if(real) __atomic_fetch_add(&unf_real[h],1,__ATOMIC_RELAXED); else __atomic_fetch_add(&unf_att[h],1,__ATOMIC_RELAXED); }
static void unf_dump(void){ for(unsigned h=0;h<UNF_N;h++) if(unf_key[h]) fprintf(stderr,"UNFC %u %u %u\n",unf_key[h]-1,unf_att[h],unf_real[h]); }
'''
i = s.index("static void err_fail"); s = s[:i] + hdr + s[i:]
def hook(cid, flagidx, viidx, flagval, real):
    global s
    pat = re.compile(r"(\} else if \(term_aux\(_f_0\) == %s\) \{\n\s*u64 (_sp_\d+) = term_loc\(_f_0\);\n)((?:\s*(?:u32|Term) _f_\d+ = e\.mem\[_sp_\d+ \+ \d+\];\n)+)" % cid)
    n = 0
    def rep(m):
        nonlocal n; n += 1
        fl = re.findall(r"(?:u32|Term) (_f_\d+) = e\.mem\[_sp_\d+ \+ (\d+)\]", m.group(3))
        d = dict((int(b), a) for a, b in fl)
        return m.group(1) + m.group(3) + "          if (%s == %d) unf_rec((unsigned)%s, %d);\n" % (d[flagidx], flagval, d[viidx], real)
    s = pat.sub(rep, s)
    assert n >= 1, cid
hook("CID_KM_WDELGO", 0, 2, 1, 0)
hook("CID_KM_WDELH", 0, 3, 0, 1)
s = s.replace("static void err_fail", "#include <signal.h>\nstatic void unf_term(int sg){ unf_dump(); _exit(143); }\nstatic void err_fail", 1)
s = s.replace("int main(int argc, char** argv) {\n", "int main(int argc, char** argv) {\n  atexit(unf_dump); signal(SIGTERM, unf_term);\n", 1)
open(p, 'w').write(s)
PY
NIXCLANG=/nix/store/fy71z4s85kl6114vz7ksp3m5z4fz275k-clang-wrapper-21.1.8/bin/clang
"$NIXCLANG" -O2 -o "$OUT" "$TMP/gen.c" -lpthread
codesign -s - -f "$OUT" 2>/dev/null || true
