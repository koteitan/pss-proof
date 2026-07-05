import sys, time, random
from collections import deque
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import Lng, oper, diagSeq, monoT, zeroT, P, seg
def multiT(M): return (not zeroT(M)) and (not monoT(M))
def Pcut(M):
    comps=P(M); return Lng(M)-Lng(comps[-1])
seen=set()
q=deque(diagSeq(u,u+d) for u in range(0,7) for d in range(1,7))
multi=[]; t0=time.time(); nseen=0
while q and time.time()-t0<90:
    M=q.popleft(); k=tuple(M)
    if k in seen: continue
    seen.add(k); nseen+=1
    if multiT(M): multi.append(list(M))
    if Lng(M)<=55:
        for nn in range(1,6):
            try: M2=oper(M,nn)
            except Exception: continue
            if M2!=M and tuple(M2) not in seen: q.append(M2)
# classify multiT by last component
from collections import Counter
lastc=Counter()
nontriv=[]
for M in multi:
    last=tuple(seg(M,Pcut(M),Lng(M)-1))
    if last==((0,0),): lastc['(0,0)']+=1
    else:
        lastc['nontriv']+=1; nontriv.append(M)
print("seen=%d multiT=%d  last-comp: %s"%(nseen,len(multi),dict(lastc)))
for M in multi[:10]:
    print("  multiT Lng=%d last=%s M=%s"%(Lng(M),seg(M,Pcut(M),Lng(M)-1),M))
print("--- nontrivial last comp (first 10) ---")
for M in nontriv[:10]:
    print("  Lng=%d last=%s M=%s"%(Lng(M),seg(M,Pcut(M),Lng(M)-1),M))
