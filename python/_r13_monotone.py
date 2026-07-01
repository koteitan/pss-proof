import sys, time, signal, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,multiT,parent,oper,reduced,hasParent,
                        nextrel0,Pcut,Adm)
from trans_model import condV

"""ROUND 13 handoff check: candidate proof route for the base-cut inequality
entry Mq 0 (Pcut Mq) < fst(B!m).  Tests, per genuine non-reset trunk-stuck block:
  (A) fst(B!m) non-decreasing in m  (row-0 monotone across the block)?
  (B) is column m=0 trunk-stuck (jm1 < Pcut(Mq))?  (m=0 witness = base-cut@0)
  (C) base-cut@0: entry Mq 0 (Pcut Mq) < fst(B!0)?"""

class TE(Exception): pass
def h(s,f): raise TE()
signal.signal(signal.SIGALRM,h)
def sr(M,b=1):
    signal.alarm(b)
    try: r=reduced(M); signal.alarm(0); return r
    except Exception: signal.alarm(0); return None
def gen(rng,maxlen=6,maxv=2,uv=(0,1,2,3,4)):
    P=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]; n=len(P)
    C=[(u,L) for u in uv for L in range(2,maxlen+1)]
    while True:
        rng.shuffle(C)
        for (u,L) in C:
            idx=rng.randrange(n**(L-1)); s=[]; t=idx
            for _ in range(L-1): s.append(P[t%n]); t//=n
            yield [(u,u)]+s

def sweep(tl,qs,seed):
    rng=random.Random(seed); t0=time.time()
    monoOK=0; blocks=0; stuck0=0; bc0=0; stuck0_tot=0
    for M in gen(rng):
        if time.time()-t0>tl: break
        if sr(M,1) is not True: continue
        for q in qs:
            try:
                Mq=oper(M,q); j1=Lng(Mq)-1
                if j1<=0 or Lng(Mq)>16: continue
                if not condV(Mq): continue
                if not hasParent(Mq,1,j1): continue
                p1=parent(Mq,1,j1)
                if not (nextrel0(Mq,p1,j1) and p1==parent(Mq,0,j1)): continue
                jm1=Adm(Mq,parent(Mq,0,j1))
                if not (jm1>0): continue
                Msq=oper(M,q+1)
                if Msq[:len(Mq)]!=Mq: continue
                B=Msq[len(Mq):]; wB=len(B)
                if wB<1 or B[0][0]==0: continue
                if sr(Mq,1) is not True or not multiT(Mq): continue
                # keep only blocks that HAVE a trunk-stuck non-reset column
                host=list(Mq); has_stuck=False
                for m in range(wB):
                    Nprev=list(host); host=host+[B[m]]
                    if sr(host,1) is not True: break
                    if sr(Nprev,1) is not True: continue
                    if not multiT(Nprev): continue
                    if jm1<Pcut(Nprev) and B[m][0]!=0: has_stuck=True
                if not has_stuck: continue
                blocks+=1
                row0=[B[m][0] for m in range(wB)]
                mono = all(row0[m]<=row0[m+1] for m in range(wB-1))
                if mono: monoOK+=1
                # column m=0 trunk-stuck?
                pc0=Pcut(Mq); s0 = jm1<pc0
                stuck0_tot+=1
                if s0:
                    stuck0+=1
                    if entry(Mq,0,pc0)<B[0][0]: bc0+=1
            except Exception: continue
    return blocks,monoOK,stuck0,bc0,stuck0_tot

if __name__=='__main__':
    tl=int(sys.argv[1]) if len(sys.argv)>1 else 60
    seeds=[int(x) for x in sys.argv[2:]] or [555,321,7,99,13]
    B=Mo=S0=BC=S0t=0
    for sd in seeds:
        b,m,s,bc,st=sweep(tl,(1,2,3,4),sd)
        B+=b; Mo+=m; S0+=s; BC+=bc; S0t+=st
        print(f"seed={sd}: blocks={b} monoOK={m}/{b} col0stuck={s}/{st} bc@0={bc}/{s}")
    print(f"\nTOTAL blocks={B}")
    print(f"(A) row0 non-decreasing across block: {Mo}/{B}")
    print(f"(B) column 0 trunk-stuck:             {S0}/{S0t}")
    print(f"(C) base-cut@0 (given col0 stuck):    {BC}/{S0}")
