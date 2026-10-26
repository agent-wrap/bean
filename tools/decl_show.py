#!/usr/bin/env python3
"""Print a declaration of an export: its type and value as readable terms.
usage: decl_show.py EXPORT.ndjson NAME|EXPR_ID [DEPTH]  (a numeric NAME prints that expression)"""
import json,sys
sys.setrecursionlimit(100000)
src,name=sys.argv[1],sys.argv[2]; depth=int(sys.argv[3]) if len(sys.argv)>3 else 12
N={};E={};L={};decls=[]
for l in open(src):
    r=json.loads(l)
    if "in" in r: N[r["in"]]=r
    elif "ie" in r: E[r["ie"]]=r
    elif "il" in r: L[r["il"]]=r
    elif "meta" in r: pass
    else: decls.append(r)
def nm(i):
    r=N.get(i)
    if not r: return ""
    for k in ("str","num"):
        if k in r and isinstance(r[k],dict):
            p=nm(r[k].get("pre",0)); s=r[k].get("str",r[k].get("i")); return (p+"." if p else "")+str(s)
    return ""
def lv(i):
    r=L.get(i)
    if r is None: return "?"
    k=[k for k in r if k!="il"][0]; v=r[k]
    if k=="succ": return "s("+lv(v)+")"
    if k=="param": return nm(v)
    if k in ("max","imax"): return k+"("+",".join(lv(x) for x in (v if isinstance(v,list) else [v.get("lhs"),v.get("rhs")]))+")"
    return k+str(v)
def show(i,d=0,lim=depth):
    r=E.get(i)
    if r is None: return "?%d"%i
    k=[k for k in r if k!="ie"][0]; v=r[k]
    if k=="const": return nm(v["name"])+("{"+",".join(lv(u) for u in v["us"])+"}" if v["us"] else "")
    if k=="bvar": return "#%s"%(v if not isinstance(v,dict) else v.get("idx",v))
    if k=="sort": return "Sort("+lv(v)+")"
    if k=="lit": return "lit"+str(v)[:30]
    if d>=lim: return "…"
    if k=="app":
        args=[]; f=i
        while True:
            rr=E[f]; kk=[x for x in rr if x!="ie"][0]
            if kk!="app": break
            args.append(rr[kk]["arg"]); f=rr[kk]["fn"]
        return "("+show(f,d+1,lim)+" "+" ".join(show(a,d+1,lim) for a in args[::-1])+")"
    if k in("lam","forallE"): return ("λ" if k=="lam" else "Π")+"["+show(v.get("type",v.get("binderType")),d+1,lim)+"]. "+show(v["body"],d+1,lim)
    if k=="proj": return "proj."+nm(v["typeName"])+"."+str(v["idx"])+"("+show(v["struct"],d+1,lim)+")"
    if k=="letE": return "let["+show(v.get("type"),d+1,lim)+" := "+show(v.get("value"),d+1,lim)+"]. "+show(v["body"],d+1,lim)
    return k+str(v)[:60]
if name.lstrip("-").isdigit():   # a raw export expression id (store node id below the export size)
    print("expr", name, ":", show(int(name))); sys.exit(0)
for r in decls:
    k=list(r.keys())[0]; d=r[k]; n=d.get("name")
    if isinstance(n,int) and nm(n)==name:
        print("==",k,name,"hints",d.get("hints"),"lps",[nm(x) for x in d.get("levelParams",[])])
        print("type:",show(d["type"]))
        if "value" in d: print("value:",show(d["value"]))
