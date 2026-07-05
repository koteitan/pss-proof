import sys, time
from collections import deque
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import Lng, oper, diagSeq, monoT, zeroT, P, seg, entry
import red_model as rm
def multiT(M): return (not zeroT(M)) and (not monoT(M))
def is_prefix(a,b): return len(a)<=len(b) and b[:len(a)]==a
# For each multiT ST_PS X = M'[n] we reconstruct via oper generation: track (M', n)
# Simpler: enumerate multiT hosts X, find its P, and check the tail block P(?c[n]) structure
# by identifying ?c = last(P(M')) where X = M'[n]. But we don't store M'. Instead directly:
# check the JUNCTION prefix: last(P X) prefix of secondlast, and whether last(P X) equals
# an oper-expanded (longer than a "base") -- i.e. is the junction ever a PROPER (non-Pred) growth?
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
# For multiT X, classify the last two components relation
seen2=set(); q2=deque(ms); t1=time.time()
eqlast=predlast=deeper=other=0; examples=[]
def Pcut(M):
    comps=P(M); return Lng(M)-Lng(comps[-1])
while q2 and time.time()-t1<70:
    X=q2.popleft(); k=tuple(X)
    if k in seen2: continue
    seen2.add(k); comps=P(X)
    if multiT(X) and len(comps)>=2 and seg(X,Pcut(X),Lng(X)-1)!=[(0,0)]:
        last=comps[-1]; snd=comps[-2]
        if last==snd: eqlast+=1
        elif is_prefix(last,snd):
            # proper prefix: how much shorter?
            gap=len(snd)-len(last)
            if gap>=1: predlast+=1
            if len(examples)<8: examples.append((gap,last,snd))
        else: other+=1
    if Lng(X)<=48:
        for nn in range(1,6):
            try: X2=oper(X,nn)
            except Exception: continue
            if X2!=X and tuple(X2) not in seen2: q2.append(X2)
print("eq-last-two=%d  proper-prefix=%d  non-prefix=%d"%(eqlast,predlast,other))
print("proper-prefix examples (gap,last,snd):")
for g,l,s in examples: print("  gap=%d last=%s snd=%s"%(g,l,s))
