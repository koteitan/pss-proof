import sys, time, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import Lng, oper, diagSeq, monoT, zeroT, P
import red_model as rm
def multiT(M): return (not zeroT(M)) and (not monoT(M))
rng=random.Random(7); seen=set(); mono=0; multi=0; deep=0; maxL=0
starts=[diagSeq(u,u+d) for u in range(0,6) for d in range(1,6)]
t0=time.time()
for M0 in starts:
    M=M0
    for _ in range(60):
        k=tuple(M)
        if k not in seen and Lng(M)>1:
            seen.add(k)
            if multiT(M): multi+=1
            elif monoT(M): mono+=1
            maxL=max(maxL,Lng(M))
            if Lng(M)>=12: deep+=1
        nn=rng.randrange(1,5)
        try: M2=oper(M,nn)
        except Exception: break
        if M2==M or Lng(M2)>50: break
        M=M2
    if time.time()-t0>40: break
print("mono=%d multi=%d deep(>=12)=%d maxLng=%d total=%d"%(mono,multi,deep,maxL,len(seen)))
# sample a few multiT
cnt=0
for M in seen:
    Ml=list(M)
    if multiT(Ml) and Lng(Ml)>=6:
        print("multiT Lng=%d P-comps=%d M=%s"%(Lng(Ml),len(P(Ml)),Ml)); cnt+=1
        if cnt>=6: break
