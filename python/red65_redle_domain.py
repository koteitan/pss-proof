#!/usr/bin/env python3
"""Fast redle domains. For reduced M, Red M == M so leR M==leR(Red M) holds
trivially; we still EXPLICITLY recompute leR on a sample. For the full reduced
set we verify Red M==M (reduced) which is exactly the redle identity premise.
Also recompute the actual leR-equality on monoTstd (smaller) for a real check."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import Lng, entry, monoT, leR, Red, reduced, fmt
from d1pos_j0j1red_search import gen_std

def rankL(M): return Lng(M)
def valM(M): return max((max(a,b) for (a,b) in M), default=0)

def real_redle(Mset, name):
    """Explicitly recompute leR(M) vs leR(Red M) for every (i,j0,j1)."""
    strat={}; t=f=0; ce=[]
    for M in Mset:
        R=Red(M); ok=True; first=None
        if Lng(R)!=Lng(M): ok=False; first=('LNGMM',fmt(R))
        else:
            n=Lng(M)
            for i in (0,1):
                for j0 in range(n):
                    for j1 in range(n):
                        if leR(M,i,j0,j1)!=leR(R,i,j0,j1):
                            ok=False; first=(i,j0,j1); break
                    if not ok: break
                if not ok: break
        r,v=rankL(M),valM(M); strat.setdefault((r,v),[0,0])
        strat[(r,v)][0 if ok else 1]+=1
        if ok: t+=1
        else:
            f+=1
            if len(ce)<6: ce.append((fmt(M),first,fmt(R)))
    print(f"-- domain ({name}): TRUE={t} FALSE={f} TOTAL={t+f}")
    for k in sorted(strat):
        a,b=strat[k]; print(f"    L={k[0]:2d} val={k[1]:2d}: {a}/{b}/{a+b}")
    for c in ce: print("    CE:",c)

if __name__=='__main__':
    maxlen,maxval,KMAX=(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])) if len(sys.argv)>3 else (10,5,6)
    Ms=gen_std(maxlen,maxval,KMAX)
    redset=[M for M in Ms if reduced(M)]
    monostd=[M for M in Ms if monoT(M)]
    redmono=[M for M in monostd if reduced(M)]
    print(f"# standard={len(Ms)} reduced={len(redset)} monoTstd={len(monostd)} redANDmono={len(redmono)}")
    real_redle(monostd, "c: PT_PS (monoT standard)")
    real_redle(redmono, "e: PT_PS AND reduced")
    real_redle(redset, "b: reduced (Red M==M)")
