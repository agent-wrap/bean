#!/usr/bin/env python3
"""Decode an fdbg probe dump (see tools/fprobe.sh): the recorded (x, y) pair
of store indices and the two terms they name, with names resolved from the
export.  usage: fdump.py EXPORT.ndjson DUMP.dbg ""
"""
import sys,json
recs=[json.loads(l) for l in open(sys.argv[1])]
N={r["in"]:r for r in recs if "in" in r}
def nm(i):
    r=N.get(i)
    if not r: return "_%d"%i
    for k in ("str","num"):
        if k in r and isinstance(r[k],dict):
            p=nm(r[k].get("pre",0)) if r[k].get("pre",0) else ""; s=r[k].get("str",r[k].get("i"))
            return (p+"." if p else "")+str(s)
    return "?"
ws=[int(x) for x in open(sys.argv[2]).read().split()][1:]
# find dump: tokens between a code and the 4294966000 marker (printed list is acc order)
if 4294966000 not in ws: print("no dump"); sys.exit()
end=ws.index(4294966000)
seg=list(reversed(ws[1:end+1]))
print('raw x,y =', seg[1], seg[2])
toks=seg[3:]
def parse(t,i,depth=0):
    if i>=len(t): return "…",i
    k=t[i]
    if k==1:
        f,i=parse(t,i+1,depth+1); a,i=parse(t,i,depth+1); return "(%s %s)"%(f,a),i
    if k in (2,3):
        ty,i=parse(t,i+1,depth+1); b,i=parse(t,i,depth+1); return "(%s %s. %s)"%("λ" if k==2 else "Π",ty,b),i
    if k==4:
        ty,i=parse(t,i+1); v,i=parse(t,i); b,i=parse(t,i); return "(let %s := %s; %s)"%(ty,v,b),i
    if k==5:
        tn,ix=t[i+1],t[i+2]; s,i=parse(t,i+3); return "%s.%d"%(s,ix),i
    if k==6:
        name=nm(t[i+1]); i+=2; ls=[]
        while i<len(t) and t[i]==15: ls.append("L%d"%t[i+1]); i+=2
        if i<len(t) and t[i]==16: i+=1
        return (name + ("{%s}"%",".join(ls) if ls else "")), i
    if k==7: return "#%d"%t[i+1],i+2
    if k==8: return "Sort",i+1
    if k==12: return "Sort@%d"%t[i+1],i+2
    if k==9: return "%d"%t[i+1],i+2
    if k==10: return "\"str\"",i+1
    if k==11: return "BAD",i+1
    if k==4294966001: return "‖",i+1
    return "?%d"%k,i+1
x,i=parse(toks,0)
if i<len(toks) and toks[i]==4294966001: i+=1
y,i=parse(toks,i)
def lnparse(t,i):
    k=t[i]
    if k==30: return "?un",i+1
    if k==31: return "?sym",i+1
    if k==35: return "…",i+1
    if k in (32,34):
        n=t[i+1]; i+=2; ats=[]
        for _ in range(n):
            b,o=t[i],t[i+1]; i+=2
            ats.append(("%d"%o) if b==0 else ("u%d%s"%(b-1, "+%d"%o if o else "")))
        if k==32: return ("max(%s)"%",".join(ats) if len(ats)!=1 else ats[0]),i
        yv,i=lnparse(t,i); r,i=lnparse(t,i); return "mx(%s; %s; %s)"%(",".join(ats),yv,r),i
    if k==33:
        off=t[i+1]; a,i=lnparse(t,i+2); b,i=lnparse(t,i); return "imax(%s,%s)%s"%(a,b,"+%d"%off if off else ""),i
    return "?%d"%k,i+1
if i<len(toks) and toks[i]==4294966003:
    i+=1
    while i<len(toks) and toks[i]==13:
        lid=toks[i+1]; lv,i=lnparse(toks,i+2); print("LV %d = %s"%(lid,lv))
import os; L=int(os.environ.get("FDUMP_MAX","3000")); print("X =",x[:L]); print("Y =",y[:L])
