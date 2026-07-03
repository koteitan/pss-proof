#!/usr/bin/env python3
# r27: dissect RightAnces recursion of Pred M at genuine hosts. Determine: how the
# chain element after jm1 arises. Compare jm1 to jpP=parent(PredM)0(last), jm1P=Adm.
import sys, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-f7/python')
from red_model import Lng, entry, monoT, seg, adm, oper, diagSeq, parent, Adm, Pred, fmt, zeroT, Red, P
from trans_model import reduced, condV, condI, condIII, condVI, Trans, Mark, bpHeadT, ZB

def condcode(M):
    c=[]
    if condI(M): c.append('I')
    if condIII(M): c.append('III')
    if condV(M): c.append('V')
    if condVI(M): c.append('VI')
    return '+'.join(c) if c else 'none'

def gen(ml,mn,ms,cap,tb):
    seen=set();fr=[];pool=[]
    for u in range(ms):
        for v in range(u,u+ms+3):
            M=tuple(diagSeq(u,v))
            if M not in seen: seen.add(M);fr.append(list(M));pool.append(list(M))
    t0=time.time()
    while fr and len(pool)<cap and time.time()-t0<tb:
        nx=[]
        for M in fr:
            if Lng(M)<=1: continue
            for n in range(1,mn+1):
                N=oper(M,n)
                if Lng(N)>ml: continue
                t=tuple(N)
                if t not in seen: seen.add(t);nx.append(N);pool.append(N)
                if len(pool)>=cap: break
            if len(pool)>=cap: break
        fr=nx
    return pool

def run(ml,cap,budget,mn,ms):
    pool=gen(ml,mn,ms,cap,budget*0.5)
    print("pool",len(pool),flush=True)
    t0=time.time(); tot=0; facts={}
    for M in pool:
        if time.time()-t0>budget: break
        if not (reduced(M) and monoT(M)): continue
        if Lng(M)<3: continue
        j1=Lng(M)-1; jp=parent(M,0,j1)
        if jp is None: continue
        if not condV(M): continue
        if adm(M,jp): continue
        if Trans(Pred(M))==ZB: continue
        jm1=Adm(M,jp)
        c1=Mark(Pred(M),jm1)
        if bpHeadT(c1)==ZB: continue
        PM=Pred(M); LP=Lng(PM)
        if not reduced(PM): continue
        jpP=parent(PM,0,LP-1); jm1P=Adm(PM,jpP) if jpP is not None else None
        tot+=1
        # facts to characterise
        f=[]
        f.append(('jm1==jm1P', jm1==jm1P))
        f.append(('jm1==jpP', jm1==jpP))
        f.append(('PredM cond', condcode(PM)))
        f.append(('zeroT PredPred', zeroT(Pred(PM))))
        f.append(('jpP==j0-? d', (jp-jpP) if jpP is not None else None))
        f.append(('e1(Lng-2)==e1(j1)', entry(M,1,Lng(M)-2)==entry(M,1,j1)))
        f.append(('e1(Lng-2)==e1(jpP)+1', jpP is not None and entry(M,1,Lng(M)-2)==entry(PM,1,jpP)+1))
        f.append(('jpP==Lng-2? (adjacency)', jpP==LP-1-1))
        f.append(('e1(jpP)==e1(j0)', jpP is not None and entry(PM,1,jpP)==entry(M,1,jp)))
        for k,v in f:
            facts.setdefault(k,{}).setdefault(v,0)
            facts[k][v]+=1
        if tot<=12:
            print(f"M={fmt(M)} jm1={jm1} j0={jp} j1={j1}| PM cond={condcode(PM)} jpP={jpP} jm1P={jm1P} zTPP={zeroT(Pred(PM))} e1(L-2)={entry(M,1,Lng(M)-2)} e1(j1)={entry(M,1,j1)}")
    print("tot",tot)
    for k,d in facts.items():
        print(" ",k,":",d)

if __name__=='__main__':
    run(int(sys.argv[1]) if len(sys.argv)>1 else 14,
        int(sys.argv[2]) if len(sys.argv)>2 else 8000,
        int(sys.argv[3]) if len(sys.argv)>3 else 200,
        int(sys.argv[4]) if len(sys.argv)>4 else 16,
        int(sys.argv[5]) if len(sys.argv)>5 else 4)
