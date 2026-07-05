import sys, time
from collections import deque
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import Lng, oper, diagSeq, monoT, zeroT, P, seg
def multiT(M): return (not zeroT(M)) and (not monoT(M))
def Pcut(M):
    comps=P(M); return Lng(M)-Lng(comps[-1])
def is_prefix(a,b): return len(a)<=len(b) and b[:len(a)]==a
# phase1 collect multi seeds
seen=set(); q=deque(diagSeq(u,u+d) for u in range(0,7) for d in range(1,7))
t0=time.time(); ms=[]
while q and time.time()-t0<40:
    M=q.popleft(); k=tuple(M)
    if k in seen: continue
    seen.add(k)
    if multiT(M): ms.append(list(M))
    if Lng(M)<=45:
        for nn in range(1,6):
            try: M2=oper(M,nn)
            except Exception: continue
            if M2!=M and tuple(M2) not in seen: q.append(M2)
# phase2 multi-seeded
seen2=set(); q2=deque(ms); t1=time.time()
Qtot=Qok=Ptot=Pok=Pdeep=Pdok=0; Qfail=[]
while q2 and time.time()-t1<70:
    M=q2.popleft(); k=tuple(M)
    if k in seen2: continue
    seen2.add(k); comps=P(M)
    if multiT(M) and len(comps)>=2 and seg(M,Pcut(M),Lng(M)-1)!=[(0,0)]:
        Ptot+=1
        p=is_prefix(comps[-1],comps[-2])
        if p: Pok+=1
        if Lng(M)>=12:
            Pdeep+=1
            if p: Pdok+=1
        Qtot+=1
        if all(is_prefix(comps[j+1],comps[j]) for j in range(len(comps)-1)): Qok+=1
        else: Qfail.append((M,[len(c) for c in comps]))
    if Lng(M)<=48:
        for nn in range(1,6):
            try: M2=oper(M,nn)
            except Exception: continue
            if M2!=M and tuple(M2) not in seen2: q2.append(M2)
print("multi_nontriv=%d"%Ptot)
print("pcompPrefix(last pair) = %d/%d  deep(>=12) %d/%d"%(Pok,Ptot,Pdok,Pdeep))
print("Q*(ALL consecutive nested) = %d/%d"%(Qok,Qtot))
for M,ls in Qfail[:10]: print("  QFAIL comp-lens=%s M=%s"%(ls,M[:20]))
