import sys, time
from collections import deque
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import Lng, oper, diagSeq, monoT, zeroT, P, seg
from trans_model import Trans
import buchholz as bu
def multiT(M): return (not zeroT(M)) and (not monoT(M))
def bucOf(t): return [('D',p[1],bucOf(p[2])) for p in t[1]]
def Pcut(M):
    comps=P(M); return Lng(M)-Lng(comps[-1])
# DFS-ish with priority to grow long, from many seeds, hunting non-equal comps
import random
rng=random.Random(1)
seen=set(); noneq=[]; multi_nontriv=0; eqcnt=0; comple_fail=0; md_fail=0
seeds=[diagSeq(u,u+d) for u in range(0,8) for d in range(1,8)]
frontier=deque(seeds)
t0=time.time()
while frontier and time.time()-t0<120:
    M=frontier.popleft() if rng.random()<0.5 else frontier.pop()
    k=tuple(M)
    if k in seen: continue
    seen.add(k)
    if multiT(M):
        comps=P(M)
        c=Pcut(M); bJ=seg(M,c,Lng(M)-1)
        if len(comps)>=2 and bJ!=[(0,0)]:
            bJm1=comps[-2]
            multi_nontriv+=1
            if bJ==bJm1: eqcnt+=1
            else:
                # NON-equal consecutive components!
                try:
                    TB=Trans(bJ); TBm1=Trans(bJm1)
                    cp=bu.le_term(bucOf(TB),bucOf(TBm1))
                except Exception:
                    cp=None
                noneq.append((list(M),bJ,bJm1,cp))
                if cp is False: comple_fail+=1
    if Lng(M)<=45:
        for nn in range(1,7):
            try: M2=oper(M,nn)
            except Exception: continue
            if M2!=M and tuple(M2) not in seen: frontier.append(M2)
print("seen=%d  multi_nontriv_junction=%d  eq-consec=%d  noneq-consec=%d"%(len(seen),multi_nontriv,eqcnt,len(noneq)))
print("comple_fail among noneq=%d"%comple_fail)
for M,bJ,bJm1,cp in noneq[:15]:
    print("  NONEQ cp=%s last=%s 2nd=%s  Lng=%d M=%s"%(cp,bJ,bJm1,len(M),M))
