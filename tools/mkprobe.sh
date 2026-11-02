#!/usr/bin/env bash
# tools/mkprobe.sh DIR IDX: a probe-ready source copy for tools/fprobe.sh (SRC=DIR):
# the DQx frame after each defeq, IAp7 rebinds, and fdbg checking only slice
# declaration IDX (tools/fdbg_one.patch). BASE=SRCDIR copies another tree.
# MODE=1|2 runs that pass of fck_sel (1 cheap projections, 2 capped full)
# instead of fdbg's single full pass.
set -euo pipefail
TD="$(cd "$(dirname "$0")" && pwd)"
D="$1"; I="$2"
/bin/rm -rf "${D:?}"; /bin/cp -Rf "${BASE:-$TD/../src}" "$D"
sed "s/22918/$I/g" "$TD/fdbg_one.patch" | patch -s "$D/fdbg.bend"
if [[ -n "${MODE:-}" ]]; then
  python3 - "$D/fdbg.bend" "$MODE" <<'PY'
import sys
p, m = sys.argv[1:3]; s = open(p).read()
old = """    case True{}:
      fck_one_d(st, mt, nt, lp, vt, nmt, d, basenx, natn, qtt, fs)"""
assert s.count(old) == 1
s = s.replace(old, old.replace("natn, qtt, fs", "natn, R.set(U32, 64n, qtt, 4000000000, %s, 4294967295), fs" % m))
open(p, 'w').write(s)
PY
fi
python3 - "$D/km.bend" <<'PY'
import sys
p=sys.argv[1]; s=open(p).read()
s=s.replace("type KF is Data:\n","type KF is Data:\n  DQx{x: U32, y: U32, fu: U32}\n",1)
old="""      km(p, KCon{DSc0{x2, y2, ctx, fu}, k}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, kclmax(fs, x2, y2, hcb))
    case 1n+p KCon{DSc0{xi, yi, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:"""
assert s.count(old)==1
s=s.replace(old,"""      +fq0 : U32 = fu
      km(p, KCon{DSc0{x2, y2, ctx, fq0}, KCon{DQx{x2, y2, fq0}, k}}, lnt, nlx, mt, lp, vt, qtt, natn,
         wm, nt, hcb, kclmax(fs, x2, y2, hcb))
    case 1n+p KCon{DQx{x, y, fu}, k} Tuple{Tuple{fs, MTri{t}}, ri}:
      +tq : L.Tri = t
      +xq : U32 = x
      +yq : U32 = y
      +fq : U32 = fu
      km(p, k, lnt, nlx, mt, lp, vt, qtt, natn, wm, nt, hcb, kmtri_r((fs, ri), tq))
    case 1n+p KCon{DSc0{xi, yi, ctx, fu}, k} Tuple{Tuple{fs, msg}, ri}:""")
old="""    case 1n+p KCon{IAp7{a, node, ra, raok, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +r2 : U32 = ra
      km(p, KCon{IAp8{t, a, node, r2, raok, rf, rfok, ctx, fu}, k}, lnt,"""
assert s.count(old)==1
s=s.replace(old,"""    case 1n+p KCon{IAp7{a, node, ra, raok, rf, rfok, ctx, fu}, k}
         Tuple{Tuple{fs, MTri{t}}, ri}:
      +t7 : L.Tri = t
      +nd7 : T.Ex = node
      +a7 : U32 = a
      +rf7 : U32 = rf
      +cx7 : List<&2, U32> = ctx
      +r2 : U32 = ra
      km(p, KCon{IAp8{t7, a7, nd7, r2, raok, rf7, rfok, cx7, fu}, k}, lnt,""")
open(p,'w').write(s)
PY
