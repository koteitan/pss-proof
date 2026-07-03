#!/usr/bin/env python3
# Lean Adm0 probe (case2 bounds). Key questions:
#   transJm1(N')==0 ; transV eq ; transT2 eq ; full transC2 eq ; bpHeadT(transC2) eq ; conds match
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import (Lng, entry, monoT, reduced, seg, adm, diagSeq,
                       parent, Adm, Pred, TrMax, Br, FirstNodes, Joints, fmt, Red)
from trans_model import (Trans, Mark, bpHeadT, bpHeadV, Dpt, PB, SigmaB, ZB, addBT,
                         condI, condIII, condV, condVI)
def transJ0(M): return parent(M,0,Lng(M)-1)
def transJm1(M): return Adm(M, transJ0(M))
def transC1(M): return Mark(Pred(M), transJm1(M))
def transV(M): return bpHeadV(transC1(M))
def transT2(M): return bpHeadT(transC1(M))
def transC2(M):
    j1=Lng(M)-1; jp=transJ0(M); v=transV(M); t2=transT2(M)
    Pt2=PB(t2); J1=len(Pt2)-1; pj=Pt2[J1] if Pt2 else None
    leftDj0 = (pj is not None and bpHeadV(('T',[pj]))==entry(M,1,jp))
    if leftDj0:
        t3=SigmaB([('T',[p]) for p in Pt2[:J1]]); t4=bpHeadT(('T',[pj]))
    else:
        t3=t2; t4=t2
    e1=entry(M,1,j1)
    if condI(M) or condIII(M) or condV(M):
        return Dpt(v, addBT(t2, Dpt(e1, ZB)))
    if condVI(M):
        return Dpt(v, Dpt(e1, ZB))
    if t2==ZB:
        return Dpt(v, Dpt(entry(M,1,jp), Dpt(e1, ZB)))
    return Dpt(v, addBT(t3, Dpt(entry(M,1,jp), addBT(t4, Dpt(e1, ZB)))))
def descending(L):
    vals=[entry(b,1,0) for b in L]
    return all(vals[i]>=vals[i+1] for i in range(len(vals)-1))
def valid_m(N,m):
    b=Br(N); Lb=Lng(b)
    if Lb==0: return False
    fn=FirstNodes(N); jn=Joints(N); jlast=jn[Lb-1]
    if m<jlast: return True
    if m==jlast:
        fnl=fn[Lb-1]
        return (entry(N,0,fnl)==entry(N,1,fnl)) and descending(b)
    return False
tot=0
c={'tjm1s0':0,'vEq':0,'t2Eq':0,'c2Eq':0,'bpEq':0,'e1':0,'e0':0,'condMatch':0,'c1Eq':0}
for u in range(0,3):
  for b in range(u+1,u+6):
    for wp in range(u+1,b+1):
      for w in range(0,wp+1):
        N=diagSeq(u,b)+[(wp,w)]
        if not reduced(N) or not monoT(N): continue
        if Lng(Br(N))==0: continue
        if Lng(N)!=TrMax(N)+2: continue
        if transJm1(N)!=0: continue
        L=Lng(N)
        for m in range(1,L):
            if not valid_m(N,m): continue
            tot+=1
            S=Red(seg(N,m,L-1))
            if transJm1(S)==0: c['tjm1s0']+=1
            if transV(N)==transV(S): c['vEq']+=1
            if transT2(N)==transT2(S): c['t2Eq']+=1
            if transC2(N)==transC2(S): c['c2Eq']+=1
            if bpHeadT(transC2(N))==bpHeadT(transC2(S)): c['bpEq']+=1
            if entry(N,1,L-1)==entry(S,1,Lng(S)-1): c['e1']+=1
            if entry(N,1,transJ0(N))==entry(S,1,transJ0(S)): c['e0']+=1
            if (condI(N)==condI(S) and condIII(N)==condIII(S) and condV(N)==condV(S) and condVI(N)==condVI(S)): c['condMatch']+=1
            if transC1(N)==transC1(S): c['c1Eq']+=1
print("Adm0 base hosts (m>0):", tot)
for k in c: print("  %-10s %d/%d"%(k,c[k],tot))
