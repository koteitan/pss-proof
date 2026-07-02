import sys, time, signal, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,multiT,parent,oper,reduced,hasParent,nextrel0,idx1,Adm,Pcut)
from trans_model import condV
# quick check: is the base-level row-0 edge nextrel0(M, j0M, j1M) true on genuine blocks
# (j0M = parent M (idx1) (j1M))?  i1=0: should be automatic; i1=1: the extra parR0M hyp.
class TO(Exception): pass
def h(s,f): raise TO()
signal.signal(signal.SIGALRM,h)
def sred(M):
    signal.alarm(1)
    try: r=reduced(M); signal.alarm(0); return r
    except Exception: signal.alarm(0); return None
def gen(rng,maxlen=6,maxv=3,u_vals=(0,1,2,3,4)):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]; npair=len(pairs)
    combos=[(u,L) for u in u_vals for L in range(2,maxlen+1)]
    while True:
        rng.shuffle(combos)
        for (u,L) in combos:
            idx=rng.randrange(npair**(L-1)); s=[]; t=idx
            for _ in range(L-1): s.append(pairs[t%npair]); t//=npair
            yield [(u,u)]+s
ok=[0,0]; tot=[0,0]; fails=[]
for sd in (555,321,7,99,2024,13,42):
    rng=random.Random(sd); t0=time.time(); seen=set()
    for M in gen(rng):
        if time.time()-t0>25: break
        k=tuple(M)
        if k in seen: continue
        seen.add(k)
        if sred(M) is not True: continue
        j1M=Lng(M)-1
        if j1M<=0: continue
        if entry(M,0,j1M)==0 and entry(M,1,j1M)==0: continue
        i1M=idx1(M,j1M)
        if not hasParent(M,i1M,j1M): continue
        j0M=parent(M,i1M,j1M)
        for q in (1,2,3,4,5):
            try:
                Mq=oper(M,q); j1=Lng(Mq)-1
                if j1<=0 or Lng(Mq)>16: continue
                if not condV(Mq): continue
                if not hasParent(Mq,1,j1): continue
                p1=parent(Mq,1,j1)
                if not (nextrel0(Mq,p1,j1) and p1==parent(Mq,0,j1)): continue
                jm1=Adm(Mq,parent(Mq,0,j1))
                if not jm1>0: continue
                Msq=oper(M,q+1)
                if Msq[:len(Mq)]!=Mq: continue
                B=Msq[len(Mq):]
                if len(B)<1 or B[0][0]==0: continue
                if sred(Mq) is not True or not multiT(Mq): continue
                tot[i1M]+=1
                if nextrel0(M,j0M,j1M): ok[i1M]+=1
                elif len(fails)<5: fails.append((tuple(M),q,i1M))
            except Exception: continue
print(f"parR0M base edge: i1=0: {ok[0]}/{tot[0]}   i1=1: {ok[1]}/{tot[1]}")
for f in fails: print("FAIL:",f)
