#!/usr/bin/env python3
"""For every scb_decomp (t, s, flatBP p, b) of t in T_B nonempty, is len(s) >=
length(pre) where pre is the canonical prefix-before-trailing-principal of the
flat of t (single: pre=[]; multi: pre = LP # flatBP head @ midpre @ [CM])?
i.e. does the marked principal always start at or after the LAST top-level
component boundary?  (This is the 'length s >= length pre' branch.)
"""
import itertools
LP, CM, RP, Zsym = 'LP','CM','RP','Zsym'
def Dsym(u): return ('Dsym',u)
def Trm(ps): return ('Trm',tuple(ps))
def DB(v,a): return ('D',v,a)
def flatBP(p):
    _,u,a=p; return [Dsym(u)]+flatBT(a)
def flatBT(t):
    _,ps=t
    if len(ps)==0: return [Zsym]
    if len(ps)==1: return flatBP(ps[0])
    head=ps[0]; rest=ps[1:]; mid=[]
    for r in rest: mid+=[CM]+flatBP(r)
    return [LP]+(flatBP(head)+mid)+[RP]
def pre_of(t):
    _,ps=t
    if len(ps)<=1: return []
    head=ps[0]; mids=ps[1:-1]
    midpre=[]
    for r in mids: midpre+=[CM]+flatBP(r)
    return [LP]+flatBP(head)+midpre+[CM]
def dfree_BT(t): return all(dfree_BP(p) for p in t[1])
def dfree_BP(p):
    _,v,a=p; return v!='INF' and dfree_BT(a)
def in_TB(t): return dfree_BT(t)
def enum_terms(d,idxs,mp):
    if d==0: return [Trm([])]
    sub=enum_terms(d-1,idxs,mp); princ=[DB(v,a) for v in idxs for a in sub]
    terms=[Trm([])]
    for k in range(1,mp+1):
        for combo in itertools.product(princ,repeat=k): terms.append(Trm(list(combo)))
    return terms
IDXS=[0,1,2]; DEPTH=2; MAXP=2
ALL=enum_terms(DEPTH,IDXS,MAXP); ALL_PRINC=[]
for t in ALL:
    for p in t[1]:
        if p not in ALL_PRINC: ALL_PRINC.append(p)
for t in enum_terms(DEPTH+1,IDXS,1):
    for p in t[1]:
        if p not in ALL_PRINC: ALL_PRINC.append(p)
PSET=set(tuple(flatBP(p)) for p in ALL_PRINC if dfree_BP(p))
def isPTB(c): return tuple(c) in PSET
def scb(t,s,c,b):
    if flatBT(t)!=s+c+b: return False
    if t!=Trm([]) and not isPTB(c): return False
    return all(x==RP for x in b)
def decomps(t):
    ft=flatBT(t); n=len(ft); out=[]
    for i in range(n+1):
        for k in range(n-i+1):
            s=ft[:i]; c=ft[i:i+k]; b=ft[i+k:]
            if scb(t,s,c,b): out.append((s,c,b))
    return out
TB=[t for t in ALL if in_TB(t) and t!=Trm([])]
fail=0; tot=0
for t in TB:
    pl=len(pre_of(t))
    for (s,c,b) in decomps(t):
        tot+=1
        if len(s)<pl:
            fail+=1
            if fail<=12: print("CUT-IN-PRE t=",t," len(s)=",len(s)," len(pre)=",pl," c=",c)
print(f"len(s) < len(pre): {fail}/{tot} decomps (these would be the residual branch)")
