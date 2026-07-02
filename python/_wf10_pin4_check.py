#!/usr/bin/env python3
"""Within a fixed kind, is len(RightNodes c) constant for a given t?
kind0: len(RN c)=2 by definition - trivially constant.
kind1: len(RN c) = j1+1 with constraints. Check it's constant per t per kind1.
Mechanism: kind1 condition on r=RN(c) [= suffix of RN(t) of length L]:
  L>=2, r[0]<r[L-1], all r[1..L-2]>=r[L-1].
Since r is the length-L suffix of rnt, and rnt is FIXED, the kind1 condition
selects a UNIQUE L (we test). Then len(s) is pinned by L.
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
def RightNodes_T(t):
    _,ps=t
    if len(ps)==0: return []
    _,u,a=ps[-1]; return [u]+RightNodes_T(a)
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
PMAP={}
for p in ALL_PRINC:
    if dfree_BP(p): PMAP.setdefault(tuple(flatBP(p)),p)
def isPTB(c): return tuple(c) in PMAP
def getp(c): return PMAP.get(tuple(c))
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
def RNc(c):
    p=getp(c); return RightNodes_T(Trm([p])) if p is not None else None
def is_kind0(r):
    return r is not None and len(r)==2 and r[1]==0
def is_kind1(r):
    if r is None: return False
    L=len(r); j1=L-1
    if j1<1: return False
    if not (r[0]<r[j1]): return False
    return all(r[j]>=r[j1] for j in range(1,j1))

TB=[t for t in ALL if in_TB(t) and t!=Trm([])]
# Within kind1, is L=len(RN c) constant per t?  And the suffix-of-rnt selection unique?
for kindname,pred in [("kind0",is_kind0),("kind1",is_kind1)]:
    fail_Lconst=0; tot=0
    fail_suffix_unique=0
    for t in TB:
        ds=[(s,c,b) for (s,c,b) in decomps(t) if pred(RNc(c))]
        if not ds: continue
        tot+=1
        Ls=set(len(RNc(c)) for (s,c,b) in ds)
        if len(Ls)>1:
            fail_Lconst+=1
            if fail_Lconst<=8: print(f"{kindname} L-not-const t={t} Ls={Ls}")
        # independent check: among ALL suffix-lengths L of rnt (1..len rnt),
        # how many give a kind-pred-satisfying suffix? must be exactly the L's seen.
        rnt=RightNodes_T(t)
        good_L=[L for L in range(1,len(rnt)+1) if pred(rnt[len(rnt)-L:])]
        if len(set(good_L))>1:
            fail_suffix_unique+=1
            if fail_suffix_unique<=8:
                print(f"{kindname} multiple suffix-L satisfy pred: t={t} rnt={rnt} good_L={good_L}")
    print(f"{kindname}: L-const-per-t {fail_Lconst}/{tot} fail; suffix-L-unique {fail_suffix_unique} fail")
