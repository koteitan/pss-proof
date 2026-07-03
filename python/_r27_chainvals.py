#!/usr/bin/env python3
# r27: for reduced-mono condV non-adm M, examine RightAnces M chain VALUES.
# Claims to test:
#  (C1) RightAnces M ! 1 == entry M 1 (j0+1)
#  (C2) ALL chain values after index 0 equal entry M 1 j1  (i.e. RA[i]==e_j1, i>=1)
#  (C3) RightAnces M ! 1 == entry M 1 j1
import sys, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-f7/python')
from red_model import Lng, entry, monoT, seg, adm, oper, diagSeq, parent, Adm, Pred, fmt, zeroT, Red, P
from trans_model import reduced, condV, condI, condIII, condVI, Trans, Mark, bpHeadT, ZB

def RA(M):
    if not reduced(M): return RA(Red(M))
    j1=Lng(M)-1
    if j1==0: return [] if M[0]==(0,0) else [entry(M,1,0)]
    if monoT(M):
        if zeroT(Pred(M)): return [0, entry(M,1,j1)]
        jp=parent(M,0,j1); jm1=Adm(M,jp); pre=seg(M,0,jm1)
        a=[0] if zeroT(pre) else RA(pre)
        if condI(M) or condIII(M) or condV(M) or condVI(M): return a+[entry(M,1,j1)]
        return a+[entry(M,1,jp), entry(M,1,j1)]
    comps=P(M); J1=len(comps)-1; PJ=comps[J1]; j0=j1-Lng(PJ)+1
    if PJ==[(0,0)]: return [0]
    return RA(PJ)

def gen(ml,mn,ms,cap):
    seen=set();fr=[];pool=[]
    for u in range(ms):
        for v in range(u,u+ms+3):
            M=tuple(diagSeq(u,v))
            if M not in seen: seen.add(M);fr.append(list(M));pool.append(list(M))
    while fr and len(pool)<cap:
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
    pool=gen(ml,mn,ms,cap)
    print("pool",len(pool),flush=True)
    t0=time.time(); tot=0; c1=0; c2=0; c3=0; bad2=[]
    ralen={}
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
        cc=Mark(Pred(M),jm1)
        if bpHeadT(cc)==ZB: continue
        tot+=1
        ra=RA(M)
        ralen[len(ra)]=ralen.get(len(ra),0)+1
        ej1=entry(M,1,j1); ej0p1=entry(M,1,jp+1)
        if len(ra)>=2 and ra[1]==ej0p1: c1+=1
        if len(ra)>=2 and ra[1]==ej1: c3+=1
        if all(ra[i]==ej1 for i in range(1,len(ra))): c2+=1
        else: bad2.append((fmt(M), ra, ej1))
    print(f"tot={tot}")
    print(f"  (C1) RA!1==e(j0+1): {c1}/{tot}")
    print(f"  (C3) RA!1==e(j1)  : {c3}/{tot}")
    print(f"  (C2) all RA[i>=1]==e(j1): {c2}/{tot}  bad={len(bad2)}")
    for b in bad2[:8]: print("     C2-CEX",b)
    print("  RA length dist:", dict(sorted(ralen.items())))

if __name__=='__main__':
    run(int(sys.argv[1]) if len(sys.argv)>1 else 12,
        int(sys.argv[2]) if len(sys.argv)>2 else 6000,
        int(sys.argv[3]) if len(sys.argv)>3 else 170,
        int(sys.argv[4]) if len(sys.argv)>4 else 6,
        int(sys.argv[5]) if len(sys.argv)>5 else 3)
