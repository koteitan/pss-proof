import sys, time
from collections import deque
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import Lng, oper, diagSeq, monoT, zeroT, P, seg
def multiT(M): return (not zeroT(M)) and (not monoT(M))
def Pcut(M):
    comps=P(M); return Lng(M)-Lng(comps[-1])
def is_prefix(a,b): return len(a)<=len(b) and b[:len(a)]==a
seen=set()
q=deque(diagSeq(u,u+d) for u in range(0,7) for d in range(1,7))
multi_seeds=[]; t0=time.time()
while q and time.time()-t0<45:
    M=q.popleft(); k=tuple(M)
    if k in seen: continue
    seen.add(k)
    if multiT(M): multi_seeds.append(list(M))
    if Lng(M)<=45:
        for nn in range(1,6):
            try: M2=oper(M,nn)
            except Exception: continue
            if M2!=M and tuple(M2) not in seen: q.append(M2)
# phase 2
tot=pref=eqc=deep=deep_pref=0; noPref=[]; seen2=set()
q2=deque(multi_seeds); t1=time.time()
while q2 and time.time()-t1<90:
    M=q2.popleft(); k=tuple(M)
    if k in seen2: continue
    seen2.add(k)
    if multiT(M):
        comps=P(M); c=Pcut(M); bJ=seg(M,c,Lng(M)-1)
        if len(comps)>=2 and bJ!=[(0,0)]:
            bJm1=comps[-2]; tot+=1
            p=is_prefix(bJ,bJm1)
            if p: pref+=1
            else: noPref.append((list(M),bJ,bJm1))
            if bJ==bJm1: eqc+=1
            if Lng(M)>=12:
                deep+=1
                if p: deep_pref+=1
    if Lng(M)<=48:
        for nn in range(1,6):
            try: M2=oper(M,nn)
            except Exception: continue
            if M2!=M and tuple(M2) not in seen2: q2.append(M2)
print("nontriv-junction=%d  bJ-prefix-of-bJm1=%d  (eq=%d)  deep>=12: %d/%d"
      %(tot,pref,eqc,deep_pref,deep))
print("NO-PREFIX cases: %d"%len(noPref))
for M,bJ,bJm1 in noPref[:12]:
    print("  last=%s 2nd=%s Lng=%d M=%s"%(bJ,bJm1,len(M),M[:20]))
