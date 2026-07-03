#!/usr/bin/env python3
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
    h=ps[0]; r=ps[1:]; mid=[]
    for x in r: mid+=[CM]+flatBP(x)
    return [LP]+(flatBP(h)+mid)+[RP]
def dfree_BT(t):
    _,ps=t; return all(dfree_BP(p) for p in ps)
def dfree_BP(p):
    _,v,a=p; return v!='INF' and dfree_BT(a)
def in_TB(t): return dfree_BT(t)
def addBT(t,c):
    _,a=t; _,b=c; return Trm(list(a)+list(b))
def enum_terms(d,idxs,mp):
    if d==0: return [Trm([])]
    sub=enum_terms(d-1,idxs,mp)
    pr=[DB(v,a) for v in idxs for a in sub]
    ts=[Trm([])]
    for k in range(1,mp+1):
        for combo in itertools.product(pr,repeat=k): ts.append(Trm(list(combo)))
    return ts
IDXS=[0,1]
ALL=enum_terms(3,IDXS,2)   # deeper: depth 3
PR=[]
for t in ALL:
    for p in t[1]:
        if p not in PR: PR.append(p)
def isPTB(cstr): return len(cstr)>0 and isinstance(cstr[0],tuple) and cstr[0][0]=='Dsym'
def scb(t,s,c,b):
    if flatBT(t)!=s+c+b: return False
    if t!=Trm([]) and not isPTB(c): return False
    return all(x==RP for x in b)
TB=[t for t in ALL if in_TB(t)]
PRT=[Trm([p]) for p in PR if in_TB(Trm([p]))]
fail=0; tot=0
for t in TB:
    if len(t[1])>2: continue   # keep t small to bound
    for c in PRT:
        tc=addBT(t,c); ftc=flatBT(tc); fc=flatBT(c); m=len(fc)
        decs=[]
        for i in range(len(ftc)-m+1):
            s=ftc[:i]; b=ftc[i+m:]
            if ftc[i:i+m]==fc and scb(tc,s,fc,b): decs.append((s,b))
        for c2 in PRT:
            tc2=addBT(t,c2); fc2=flatBT(c2)
            for (s,b) in decs:
                tot+=1
                if not scb(tc2,s,fc2,b):
                    fail+=1
                    if fail<=5: print("FAIL2 t=",t,"c=",c,"c'=",c2,"s=",s,"b=",b)
print(f"Conjunct(2) DEEP(depth3): {fail}/{tot} failures")
