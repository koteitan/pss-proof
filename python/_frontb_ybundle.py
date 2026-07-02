#!/usr/bin/env python3
"""Empirically verify the full Ybundle over core-nontrunk A&B M and J<Lng(Br M)."""
import sys, itertools
sys.path.insert(0, __import__('os').path.dirname(__file__))
from red_model import (Lng, entry, monoT, multiT, zeroT, Red, diagSeq, IncrFirst,
                       funpow, seg, hasParent, parent, TrMax, Br, Joints,
                       FirstNodes, nextR_THE, le0)

def coreReduce(M):
    if entry(M,1,0)==0:
        return [(entry(M,0,j)-entry(M,0,0), entry(M,1,j)) for j in range(Lng(M))]
    return diagSeq(0,entry(M,1,0)-1)+funpow(IncrFirst,entry(M,1,0),M)

def RedCondA(M):
    for i in (0,1):
        for j in range(Lng(M)):
            if hasParent(M,i,j) and entry(M,i,parent(M,i,j))+1 != entry(M,i,j): return False
    return True
def RedCondB(M):
    for j in range(Lng(M)):
        if (not hasParent(M,0,j)) and entry(M,0,j) != entry(M,1,j): return False
    return True

def betaM(M): return Lng(M)-TrMax(M)
def muMono(M):
    if entry(M,0,0)==0 and entry(M,1,0)==0: return 2*betaM(M)
    cr=coreReduce(M)
    return 2*betaM(cr)+1
def nu(M):
    if multiT(M): return 1+sum(muMono(b) for b in Pblocks(M))
    return muMono(M)
def Pblocks(M):
    from red_model import P
    return P(M)

def npJ(M,J):
    b=Br(M)
    if entry(b[J],1,0)==0: return 0
    return nextR_THE(M,1,FirstNodes(M)[J])+1

def NJ(M,J):
    jn=Joints(M); b=Br(M)
    return [(entry(M,0,0)+jn[J]+1, entry(M,1,0)+npJ(M,J))]+b[J][1:]

def rebaseRow0(c,d,M):
    return [(a-c+d, bb) for (a,bb) in M]

def enum(maxlen, val):
    for n in range(1, maxlen+1):
        cells = [(a,b) for a in range(val+1) for b in range(val+1)]
        for M in itertools.product(cells, repeat=n):
            yield list(M)

def main():
    maxlen, val = 5, 4
    cand=0
    f_njt=0; f_lb=0; f_yt=0; f_ymono=0; f_yeq=0; f_ya=0; f_yb=0; f_nu=0
    ex=[]
    for M in enum(maxlen, val):
        if not monoT(M): continue
        if entry(M,0,0)!=0 or entry(M,1,0)!=0: continue
        if not (RedCondA(M) and RedCondB(M)): continue
        if TrMax(M)==Lng(M)-1: continue          # nontrunk
        b=Br(M)
        if len(b)==0: continue
        for J in range(len(b)):
            cand+=1
            njM=NJ(M,J)
            e=entry(njM,0,0)-entry(njM,1,0)
            Y=rebaseRow0(e,0,njM)
            # 1. NJ in T_PS (nonempty)
            if len(njM)==0: f_njt+=1; ex.append(("NJ empty",M,J))
            # 2. row-0 lower bound: forall j<Lng(NJ). e <= entry NJ 0 j
            for j in range(Lng(njM)):
                if not (e<=entry(njM,0,j)):
                    f_lb+=1
                    if len(ex)<10: ex.append(("lb",M,J,"e",e,"j",j,"nj",njM))
                    break
            # 3. Y in T_PS
            if len(Y)==0: f_yt+=1
            # 4. monoT Y
            if not monoT(Y): f_ymono+=1; (ex.append(("ymono",M,J,"Y",Y,"nj",njM)) if len(ex)<10 else None)
            # 5. entry Y 0 0 = entry Y 1 0
            if entry(Y,0,0)!=entry(Y,1,0): f_yeq+=1; (ex.append(("yeq",M,J,Y)) if len(ex)<10 else None)
            # 6. RedCondA Y
            if not RedCondA(Y): f_ya+=1; (ex.append(("ya",M,J,"Y",Y,"nj",njM)) if len(ex)<10 else None)
            # 7. RedCondB Y
            if not RedCondB(Y): f_yb+=1; (ex.append(("yb",M,J,"Y",Y,"nj",njM)) if len(ex)<10 else None)
            # 8. nu Y < nu M
            if not (nu(Y)<nu(M)): f_nu+=1; (ex.append(("nu",M,J,"nuY",nu(Y),"nuM",nu(M),"Y",Y)) if len(ex)<10 else None)
    print(f"candidates(M,J)={cand}")
    print(f"  NJ empty            : {f_njt}")
    print(f"  row-0 lower bound   : {f_lb}")
    print(f"  Y empty             : {f_yt}")
    print(f"  monoT Y             : {f_ymono}")
    print(f"  entry Y 0 0=1 0     : {f_yeq}")
    print(f"  RedCondA Y          : {f_ya}")
    print(f"  RedCondB Y          : {f_yb}")
    print(f"  nu Y < nu M         : {f_nu}")
    for e in ex[:12]: print("   EX",e)

main()
