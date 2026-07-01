import sys, time, signal, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut,idx1)
import trans_model as tm
from trans_model import condV

"""ROUND 13: is the deepen block Mq->M_{q+1} governed by Mq's OWN structure?
Tests for genuine trunk-stuck non-reset blocks:
  (A) oper(oper(M,q),1) == oper(M,q+1)  [1-step composability]
  (B) idx1(Mq, Lng Mq -1): 0 or 1?  (which oper branch)
  (C) does the explicit e1-block form (from Mq) match B? i.e. is
      B == map(lambda j:(entry Mq 0 j + 1*d0Mq, entry Mq 1 j))[j0Mq..<j1Mq]?
Also re-measures C0 (entry X 0 0 < fst(B!m)) for MORE coverage."""

class TimeoutErr(Exception): pass
def handler(s,f): raise TimeoutErr()
signal.signal(signal.SIGALRM, handler)

def safe_reduced(M, budget=1):
    signal.alarm(budget)
    try:
        r=reduced(M); signal.alarm(0); return r
    except Exception:
        signal.alarm(0); return None

def gen_shuffled(rng, maxlen=6, maxv=2, u_vals=(0,1,2,3,4)):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]
    npairs=len(pairs)
    combos=[(u,L) for u in u_vals for L in range(2,maxlen+1)]
    while True:
        rng.shuffle(combos)
        for (u,L) in combos:
            idx=rng.randrange(npairs**(L-1)); s=[]; t=idx
            for _ in range(L-1):
                s.append(pairs[t%npairs]); t//=npairs
            yield [(u,u)]+s

def main_sweep(tl, qs, seed):
    rng=random.Random(seed); t0=time.time(); cnt=0
    rowsA=[]; rowsC0=[]; idx1c={0:0,1:0}; matchB=[]; opstep=[]
    for M in gen_shuffled(rng):
        if time.time()-t0>tl: break
        if safe_reduced(M,1) is not True: continue
        cnt+=1
        for q in qs:
            try:
                Mq=oper(M,q); j1=Lng(Mq)-1
                if j1<=0 or Lng(Mq)>16: continue
                if not condV(Mq): continue
                if not hasParent(Mq,1,j1): continue
                p1=parent(Mq,1,j1); parR=nextrel0(Mq,p1,j1); p0=parent(Mq,0,j1)
                if not (parR and p1==p0): continue
                jm1=Adm(Mq,p0)
                if not (jm1>0): continue
                Msq=oper(M,q+1)
                if Msq[:len(Mq)]!=Mq: continue
                B=Msq[len(Mq):]; wB=len(B)
                if wB<1: continue
                if safe_reduced(Mq,1) is not True: continue
                if not multiT(Mq): continue
                fcol0=B[0][0]
                if fcol0==0: continue
                # only keep blocks with a trunk-stuck non-reset column
                host=list(Mq); stuckcols=[]
                for m in range(wB):
                    Nprev=list(host); col=B[m]; host=host+[col]; Ncur=list(host)
                    if safe_reduced(Ncur,1) is not True: continue
                    if safe_reduced(Nprev,1) is not True: continue
                    if not multiT(Nprev): continue
                    if not (jm1<Pcut(Nprev)): continue
                    if col[0]==0: continue
                    stuckcols.append((m,Nprev,col,Ncur))
                if not stuckcols: continue
                # (A) 1-step composability
                Mq1=oper(Mq,1)
                opstep.append(Mq1==Msq)
                # (B) idx1 branch at Mq level
                i1=idx1(Mq,j1); idx1c[i1]=idx1c.get(i1,0)+1
                # (C) explicit e1-block from Mq matches B?
                if i1==1 and hasParent(Mq,1,j1):
                    j0=parent(Mq,1,j1); d0=entry(Mq,0,j1)-entry(Mq,0,j0)
                    Bexp=[(entry(Mq,0,j)+1*d0, entry(Mq,1,j)) for j in range(j0,j1)]
                    matchB.append(Bexp==B)
                rowsA.append(1)
                for (m,Nprev,col,Ncur) in stuckcols:
                    last=Lng(Ncur)-1; elast=entry(Ncur,0,last)
                    rowsC0.append(entry(Ncur,0,0)<elast)
            except Exception:
                continue
    return cnt, rowsA, rowsC0, idx1c, matchB, opstep

if __name__=='__main__':
    tl=int(sys.argv[1]) if len(sys.argv)>1 else 200
    seed=int(sys.argv[2]) if len(sys.argv)>2 else 555
    cnt,rowsA,rowsC0,idx1c,matchB,opstep=main_sweep(tl,(1,2,3,4),seed)
    print(f"seed={seed} reduced scanned={cnt} genuine non-reset trunk-stuck blocks={len(rowsA)}")
    print(f"(A) oper(Mq,1)==oper(M,q+1):  {sum(opstep)}/{len(opstep)}")
    print(f"(B) idx1(Mq,last) branch counts: {idx1c}")
    print(f"(C) e1-explicit block (from Mq) == B (when idx1=1): {sum(matchB)}/{len(matchB)}")
    print(f"C0 entry X 0 0 < fst(col) [stuck non-reset cols]: {sum(rowsC0)}/{len(rowsC0)}")
