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
seen=set()
# phase 1: BFS from diagSeq, collect multiT hosts
q=deque(diagSeq(u,u+d) for u in range(0,7) for d in range(1,7))
multi_seeds=[]; t0=time.time()
while q and time.time()-t0<50:
    M=q.popleft(); k=tuple(M)
    if k in seen: continue
    seen.add(k)
    if multiT(M): multi_seeds.append(list(M))
    if Lng(M)<=45:
        for nn in range(1,6):
            try: M2=oper(M,nn)
            except Exception: continue
            if M2!=M and tuple(M2) not in seen: q.append(M2)
print("phase1: multi_seeds=%d"%len(multi_seeds))
# phase 2: oper the multiT seeds to diversify component structure
noneq=[]; tot=cp_ok=eqc=0; fails=[]; t1=time.time()
seen2=set()
q2=deque(multi_seeds)
while q2 and time.time()-t1<70:
    M=q2.popleft(); k=tuple(M)
    if k in seen2: continue
    seen2.add(k)
    if multiT(M):
        comps=P(M); c=Pcut(M); bJ=seg(M,c,Lng(M)-1)
        if len(comps)>=2 and bJ!=[(0,0)]:
            bJm1=comps[-2]; tot+=1
            if bJ==bJm1: eqc+=1
            else:
                try:
                    cp=bu.le_term(bucOf(Trans(bJ)),bucOf(Trans(bJm1)))
                except Exception: cp=None
                noneq.append((list(M),bJ,bJm1,cp))
                if cp: cp_ok+=1
                elif cp is False: fails.append((list(M),bJ,bJm1))
    if Lng(M)<=48:
        for nn in range(1,6):
            try: M2=oper(M,nn)
            except Exception: continue
            if M2!=M and tuple(M2) not in seen2: q2.append(M2)
print("phase2: nontriv-junction=%d eqcomp=%d noneq=%d  comple(noneq)ok=%d fail=%d"
      %(tot,eqc,len(noneq),cp_ok,len(fails)))
for M,bJ,bJm1,cp in noneq[:12]:
    print("  NONEQ cp=%s Lng=%d last=%s 2nd=%s"%(cp,len(M),bJ,bJm1))
for M,bJ,bJm1 in fails[:6]:
    print("  COMPLE-FAIL Lng=%d last=%s 2nd=%s M=%s"%(len(M),bJ,bJm1,M))
