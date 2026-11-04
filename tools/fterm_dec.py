#!/usr/bin/env python3
"""Decode tools/fterm.sh tokens: python3 tools/fterm_dec.py SLICE TOKS DEPTH -> the two terms X, Y
(App/Lam/Pi/Let/Proj/Const/BVar), names from the slice, cut at DEPTH."""
import sys, json
sys.setrecursionlimit(100000)
toks=[int(l.split()[1]) for l in open(sys.argv[2])]
names={0:""}
for ln in open(sys.argv[1]):
    if ln.startswith('{"in"'):
        r=json.loads(ln); k="str" if "str" in r else "num"; d=r[k]
        s=d["str"] if k=="str" else str(d["i"]); p=names[d["pre"]]
        names[r["in"]]=(p+"."+s) if p else s
    elif not ln.startswith('{"meta"') and not ln.startswith('{"il"') and not ln.startswith('{"ie"'): pass
# segment
st=toks.index(4294966002); ys=toks.index(4294966000, st); en=toks.index(4294966002, ys) if 4294966002 in toks[ys:] else len(toks)
def parse(t,i):
    if i>=len(t) or t[i] in (4294966000,4294966002): return ("…",),i
    k=t[i]
    if k==1: f,i=parse(t,i+1); a,i=parse(t,i); return ("app",f,a),i
    if k in (2,3): ty,i=parse(t,i+1); b,i=parse(t,i); return ("lam" if k==2 else "pi",ty,b),i
    if k==4: ty,i=parse(t,i+1); v,i=parse(t,i); b,i=parse(t,i); return ("let",ty,v,b),i
    if k==5: tn,ix=t[i+1],t[i+2]; s,i=parse(t,i+3); return ("proj",names.get(tn,tn),ix,s),i
    if k==6: return ("c",names.get(t[i+1],t[i+1])),i+2
    if k==7: return ("bv",t[i+1]),i+2
    if k==12: return ("sort",),i+1
    if k==9: return ("nat",),i+1
    if k==4294966003: return ("…",),i+1
    return ("?%d"%k,),i+1
def show(e,d=0,lim=[0]):
    if d>int(sys.argv[3]): return "…"
    tag=e[0]
    if tag=="app":
        fn=e; args=[]
        while fn[0]=="app": args.append(fn[2]); fn=fn[1]
        args.reverse()
        return "("+show(fn,d+1)+" "+" ".join(show(a,d+1) for a in args)+")"
    if tag in("lam","pi"): return ("λ" if tag=="lam" else "Π")+"["+show(e[1],d+1)+"]."+show(e[2],d+1)
    if tag=="let": return "let["+show(e[1],d+1)+":="+show(e[2],d+1)+"]."+show(e[3],d+1)
    if tag=="proj": return show(e[3],d+1)+"."+str(e[1]).split('.')[-1]+"#"+str(e[2])
    if tag=="c": return str(e[1])
    if tag=="bv": return "#%d"%e[1]
    return tag
x,_=parse(toks,st+1); y,_=parse(toks,ys+1)
print("X =", show(x)); print(); print("Y =", show(y))
