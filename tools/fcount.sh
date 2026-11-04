#!/usr/bin/env bash
# Function-entry COUNTING variant of the flat checker:
#     tools/fcount.sh OUT        (SRC=DIR builds a copy)
# Patches the generated C so that every worklist function entry (WL_CASE)
# and every iteration of a compiled tail loop (spin_N) bumps a counter; at
# exit the nonzero ones go to stderr as `CNT name count`, spin loops named
# after the functions that call them. Counts, unlike samples, say whether a
# change removed work or only moved it.
set -euo pipefail
OUT="$1"
DIR="$(cd "$(dirname "$0")" && pwd)"
TMP="$(mktemp -d)"
"$DIR/bend.sh" "${SRC:-$DIR/../src}/fmain.bend" -o "$TMP/gen.c"
python3 - "$TMP/gen.c" <<'PY'
import sys, re
p = sys.argv[1]; s = open(p).read()
fids = re.findall(r"#define (FID_[A-Z0-9_]+) (\d+)", s)
nf = max(int(v) for _, v in fids) + 1
spins = sorted(set(int(x) for x in re.findall(r"Term spin_(\d+)\(Env e", s)))
ns = (max(spins) + 1) if spins else 1
lines = s.split('\n'); cur = None; owner = {}
for l in lines:
    m = re.match(r'\s*(?:WL_CASE\((FID_[A-Z0-9_]+)\)|(?:static|INLINE|FAR)[^(]*\b(spin_\d+)\()', l)
    if m: cur = m.group(1) or m.group(2)
    for sp in re.findall(r'\bspin_(\d+)\(e,', l):
        if cur and cur != 'spin_' + sp: owner.setdefault(int(sp), []).append(cur)
fn = ["?"] * nf
for n_, v in fids: fn[int(v)] = n_[4:]
sn = []
for i in range(ns):
    o = sorted(set(owner.get(i, [])))
    sn.append(("spin_%d<" % i) + ",".join(x.replace("FID_", "") for x in o[:3]) + (".." if len(o) > 3 else ""))
hdr = "static unsigned long long fc_f[%d], fc_s[%d];\n" % (nf, ns)
hdr += "static const char* fc_fn[%d] = {%s};\n" % (nf, ",".join('"%s"' % x for x in fn))
hdr += "static const char* fc_sn[%d] = {%s};\n" % (ns, ",".join('"%s"' % x for x in sn))
hdr += r'''static void fc_dump(void){ for(int i=0;i<%d;i++) if(fc_f[i]) fprintf(stderr,"CNT %%s %%llu\n",fc_fn[i],fc_f[i]);
  for(int i=0;i<%d;i++) if(fc_s[i]) fprintf(stderr,"CNT %%s %%llu\n",fc_sn[i],fc_s[i]); }
''' % (nf, ns)
i = s.index("static void err_fail"); s = s[:i] + hdr + s[i:]
s = re.sub(r"(  WL_CASE\((FID_[A-Z0-9_]+)\)\n  \{\n)", lambda m: m.group(1) + "    __atomic_fetch_add(&fc_f[%s], 1, __ATOMIC_RELAXED);\n" % m.group(2), s)
def spin_body(m):
    return m.group(0)
out = []; cur = None
for l in s.split('\n'):
    m = re.match(r'(?:INLINE|FAR|static)[^(]*\bspin_(\d+)\(Env e', l)
    if m: cur = int(m.group(1))
    elif re.match(r'(?:INLINE|FAR|static|WL_FN)\b', l) or l.startswith('  WL_CASE('): cur = None
    out.append(l)
    if cur is not None and l.strip() == 'WL_SPIN':
        out.append("    __atomic_fetch_add(&fc_s[%d], 1, __ATOMIC_RELAXED);" % cur)
s = '\n'.join(out)
s = s.replace("int main(int argc, char** argv) {\n", "int main(int argc, char** argv) {\n  atexit(fc_dump);\n", 1)
open(p, 'w').write(s)
PY
NIXCLANG=/nix/store/fy71z4s85kl6114vz7ksp3m5z4fz275k-clang-wrapper-21.1.8/bin/clang
"$NIXCLANG" -O2 -o "$OUT" "$TMP/gen.c" -lpthread
codesign -s - -f "$OUT" 2>/dev/null || true
