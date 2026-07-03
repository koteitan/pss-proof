#!/usr/bin/env python3
"""Directly test rnsub_RightNodes_suffix:
For t in T_B, IF flatBT t = s @ flatBP p @ b with b all-RP and Trm[p] in T_B,
THEN RightNodes(Trm[p]) is a suffix of RightNodes t.
Enumerate t, all (s,p,b) splits where flatBP p is a principal flat.
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
# map principal flat -> principal (for all dfree principals)
PMAP={}
for p in ALL_PRINC:
    if dfree_BP(p): PMAP.setdefault(tuple(flatBP(p)),p)
def getp(flat): return PMAP.get(tuple(flat))
def is_suffix(small, big): return big[len(big)-len(small):]==small if len(small)<=len(big) else False
TB=[t for t in ALL if in_TB(t) and t!=Trm([])]
fail=0; tot=0; cut_lt_handled=0
for t in TB:
    ft=flatBT(t); n=len(ft); rnt=RightNodes_T(t)
    for i in range(n+1):
        for j in range(i, n+1):
            s=ft[:i]; c=ft[i:j]; b=ft[j:]
            if not all(x==RP for x in b): continue
            p=getp(c)
            if p is None: continue  # c not a principal flat / Trm[p] not dfree
            tot+=1
            rnc=RightNodes_T(Trm([p]))
            if not is_suffix(rnc, rnt):
                fail+=1
                if fail<=12:
                    print("FAIL t=",t," s_len=",i," c=",c," rnc=",rnc," rnt=",rnt)
print(f"rnsub_RightNodes_suffix: {fail}/{tot} fail")
