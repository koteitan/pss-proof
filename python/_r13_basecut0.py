import sys, time, signal, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import Lng,entry,multiT,parent,oper,reduced,hasParent,nextrel0,Pcut,Adm
from trans_model import condV
class TE(Exception): pass
def h(s,f): raise TE()
signal.signal(signal.SIGALRM,h)
def sr(M,b=1):
    signal.alarm(b)
    try: r=reduced(M); signal.alarm(0); return r
    except Exception: signal.alarm(0); return None
def gen(rng,ml=6,mv=2,uv=(0,1,2,3,4)):
    P=[(a,b) for a in range(mv+1) for b in range(mv+1)]; n=len(P)
    C=[(u,L) for u in uv for L in range(2,ml+1)]
    while True:
        rng.shuffle(C)
        for (u,L) in C:
            idx=rng.randrange(n**(L-1)); s=[]; t=idx
            for _ in range(L-1): s.append(P[t%n]); t//=n
            yield [(u,u)]+s
def sweep(tl,qs,seed):
    rng=random.Random(seed); t0=time.time(); blk=0; bc0=0
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
                host=list(Mq); has=False
                for m in range(wB):
                    Nprev=list(host); host=host+[B[m]]
                    if sr(host,1) is not True: break
                    if sr(Nprev,1) is not True: continue
                    if not multiT(Nprev): continue
                    if jm1<Pcut(Nprev) and B[m][0]!=0: has=True
                if not has: continue
                blk+=1; pc=Pcut(Mq)
                if entry(Mq,0,pc)<B[0][0]: bc0+=1
            except Exception: continue
    return blk,bc0
tl=int(sys.argv[1]); seeds=[int(x) for x in sys.argv[2:]]
B=BC=0
for sd in seeds:
    b,c=sweep(tl,(1,2,3,4),sd); B+=b; BC+=c
    print(f"seed={sd}: blocks={b} basecut@0={c}/{b}")
print(f"TOTAL: entry Mq 0 (Pcut Mq) < fst(B!0): {BC}/{B}")
