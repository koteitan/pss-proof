import sys, time
from collections import deque, Counter
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import Lng, oper, diagSeq, monoT, zeroT, P, seg
from trans_model import Trans
import buchholz as bu
def multiT(M): return (not zeroT(M)) and (not monoT(M))
def bucOf(t): return [('D',p[1],bucOf(p[2])) for p in t[1]]
def Pcut(M):
    comps=P(M); return Lng(M)-Lng(comps[-1])
seen=set()
q=deque(diagSeq(u,u+d) for u in range(0,8) for d in range(1,8))
multi=[]; t0=time.time()
while q and time.time()-t0<80:
    M=q.popleft(); k=tuple(M)
    if k in seen: continue
    seen.add(k)
    if multiT(M): multi.append(list(M))
    if Lng(M)<=60:
        for nn in range(1,7):
            try: M2=oper(M,nn)
            except Exception: continue
            if M2!=M and tuple(M2) not in seen: q.append(M2)
tot=md_ok=cp_ok=headeq=eqcomp=0; fails=[]; deep=deep_ok=0
for M in multi:
    c=Pcut(M); pre=seg(M,0,c-1); bJ=seg(M,c,Lng(M)-1)
    if bJ==[(0,0)]: continue
    comps=P(M)
    if len(comps)<2: continue
    bJm1=comps[-2]
    try:
        TA=Trans(pre); TB=Trans(bJ); TBm1=Trans(bJm1)
    except Exception: continue
    asl=bucOf(TA); bsl=bucOf(TB)
    if not asl or not bsl: continue
    tot+=1
    md=bu.le_term([bsl[0]],[asl[-1]]); cp=bu.le_term(bucOf(TB),bucOf(TBm1))
    if md: md_ok+=1
    else: fails.append(('md',M,seg(M,c,Lng(M)-1),bJm1))
    if cp: cp_ok+=1
    else: fails.append(('cp',M,bucOf(TB),bucOf(TBm1)))
    if bsl[0][1]==asl[-1][1]: headeq+=1
    if bJ==bJm1: eqcomp+=1
    if Lng(M)>=12:
        deep+=1
        if md and cp: deep_ok+=1
print("multiT total=%d  nontriv-junction checked=%d"%(len(multi),tot))
print("  multiD leBT[hd bs]<=[last as]: %d/%d"%(md_ok,tot))
print("  comple Trans(last)<=Trans(2nd-last): %d/%d"%(cp_ok,tot))
print("  headeq=%d/%d  eqcomp(last==2nd-last)=%d/%d"%(headeq,tot,eqcomp,tot))
print("  deep(Lng>=12): %d/%d both-pass"%(deep_ok,deep))
for f in fails[:10]: print("  FAIL",f)
