#!/usr/bin/env python3
"""Structural diff of a probe dump's X and Y terms (tools/fdump.py output):
the spine of each side and the path to the first difference.
usage: pairdiff.py PAIR.txt"""
import sys, re
s=open(sys.argv[1]).read()
X=s[s.index("X = ")+4:s.index("\nY = ")]; Y=s[s.index("Y = ")+4:].strip()
def tokens(t):
    i=0; out=[]
    while i<len(t):
        c=t[i]
        if c in '()': out.append(c); i+=1
        elif c==' ': i+=1
        elif t.startswith('λ ',i) or t.startswith('Π ',i): out.append(t[i]); i+=2
        elif c=='.' and (i+1==len(t) or t[i+1]==' '): out.append('.'); i+=1
        else:
            j=i
            while j<len(t) and t[j] not in '()' and not (t[j]==' ') and not (t[j]=='.' and (j+1==len(t) or t[j+1]==' ')): j+=1
            out.append(t[i:j]); i=j
    return out
def parse(toks):
    pos=0
    def p():
        nonlocal pos
        tk=toks[pos]
        if tk=='(':
            pos+=1
            if toks[pos] in ('λ','Π'):
                k=toks[pos]; pos+=1; ty=p(); assert toks[pos]=='.'; pos+=1; b=p(); assert toks[pos]==')'; pos+=1
                return (k,ty,b)
            f=p(); a=p(); assert toks[pos]==')', toks[pos:pos+5]; pos+=1
            return ('app',f,a)
        pos+=1; return tk
    r=p(); return r
def spine(n):
    args=[]
    while isinstance(n,tuple) and n[0]=='app': args.append(n[2]); n=n[1]
    return n, args[::-1]
def show(n,lim=3):
    if isinstance(n,str): return n
    if lim==0: return "…"
    if n[0]=='app':
        h,args=spine(n); return "("+show(h,lim-1)+" "+" ".join(show(a,lim-1) for a in args)+")"
    return n[0]+"["+show(n[1],lim-1)+"]. "+show(n[2],lim-1)
def diff(a,b,path):
    if isinstance(a,str) or isinstance(b,str):
        if a!=b: return path,a,b
        return None
    if a[0]!=b[0]: return path,a,b
    if a[0]=='app':
        ha,aa=spine(a); hb,ab=spine(b)
        if len(aa)!=len(ab) or ha!=hb:
            if isinstance(ha,str) and isinstance(hb,str) and ha!=hb or len(aa)!=len(ab):
                return path,a,b
        r=diff(ha,hb,path+["head"]); 
        if r: return r
        for k,(x,y) in enumerate(zip(aa,ab)):
            r=diff(x,y,path+["arg%d"%k])
            if r: return r
        return None
    for k,(x,y) in enumerate(zip(a[1:],b[1:])):
        r=diff(x,y,path+[a[0]+("ty" if k==0 else "body")])
        if r: return r
    return None
tx,ty=parse(tokens(X)),parse(tokens(Y))
for nm,t in (("X",tx),("Y",ty)):
    h,args=spine(t); print(nm,"head",h,"nargs",len(args))
    for k,a in enumerate(args): print("  arg%d:"%k, show(a,3)[:300])
r=diff(tx,ty,[])
if r:
    path,a,b=r; print("FIRST DIFF at", "/".join(path)); print("  X:", show(a,4)[:1200]); print("  Y:", show(b,4)[:1200])
else: print("identical")
