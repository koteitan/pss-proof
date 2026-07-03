#!/usr/bin/env python3
# Enumerate case2 base hosts (m > transJm1 N) DIRECTLY via diagApp with w'<=b.
# Record: condition, w vs w', transJm1(N), transJm1(slice), Trans==transC2 (both),
# and bpHeadT(transC2 N)==bpHeadT(transC2 slice).
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
def cond_name(M):
    if condI(M): return 'I'
    if condIII(M): return 'III'
    if condV(M): return 'V'
    if condVI(M): return 'VI'
    return 'ELSE'
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

rows=[]; total=0; ve_ok=0
conds={}
for u in range(0,3):
  for b in range(u+1,u+6):
    for wp in range(u+1,b+1):   # w' <= b (case2 regime: jp interior)
      for w in range(0,wp+1):
        N=diagSeq(u,b)+[(wp,w)]
        if not reduced(N) or not monoT(N): continue
        if Lng(Br(N))==0: continue
        if Lng(N)!=TrMax(N)+2: continue
        tjm1=transJm1(N)
        L=Lng(N)
        for m in range(1,L):
            if not valid_m(N,m): continue
            if not (m>tjm1): continue   # case2 only
            total+=1
            sl=seg(N,m,L-1); Rsl=Red(sl)
            tjm1s=transJm1(Rsl)
            cn=cond_name(N); cns=cond_name(Rsl)
            TN=Trans(N); TS=Trans(Rsl)
            eqN = (TN==transC2(N)); eqS=(TS==transC2(Rsl))
            bpeq = (bpHeadT(transC2(N))==bpHeadT(transC2(Rsl)))
            ve = (bpHeadT(TS)==bpHeadT(TN))
            if ve: ve_ok+=1
            conds[(cn,cns)]=conds.get((cn,cns),0)+1
            if len(rows)<25:
                rows.append((fmt(N),'m=%d'%m,'w=%d wp=%d'%(w,wp),'tjm1N=%d tjm1S=%d'%(tjm1,tjm1s),
                             'cond=%s/%s'%(cn,cns),'TN=c2:%s TS=c2:%s'%(eqN,eqS),'bpC2eq=%s'%bpeq,'VE=%s'%ve))
print("case2 checks:", total, " VE ok:", ve_ok)
print("cond (N/slice) histogram:", sorted(conds.items()))
for r in rows: print(r)
