#!/usr/bin/env python3
"""Explore the true sub-case A decomposition of Br M' vs Br N'."""
import sys, itertools
sys.path.insert(0, __file__.rsplit('/',1)[0])
from red_model import (Lng, entry, seg, oper, P, Br, TrMax, FirstNodes,
                       is_standard, parent, idx1, le0, leR, monoT, hasParent)

def all_pairseqs(maxlen, maxval):
    for L in range(1, maxlen+1):
        cells = list(itertools.product(range(maxval+1), repeat=2))
        for tup in itertools.product(cells, repeat=L):
            yield list(tup)

def main():
    MAXLEN=4; MAXVAL=3; NMAX=4
    shown=0
    for N in all_pairseqs(MAXLEN, MAXVAL):
        if not is_standard(N): continue
        LN=Lng(N)
        if LN<2: continue
        if entry(N,1,LN-1)==0 and entry(N,0,LN-1)==0: continue
        if entry(N,1,LN-1)!=0: continue
        i1=idx1(N,LN-1)
        if i1!=0: continue
        if not hasParent(N,i1,LN-1): continue
        j0N=parent(N,0,LN-1)
        if not (j0N < LN-1): continue
        w=(LN-1)-j0N
        for n in range(2, NMAX+1):
            M=oper(N,n); LM=Lng(M)
            for j0p in range(0, j0N):
                for j1p in range(j0N+1, LM):
                    if j1p > LM-1: continue
                    if not (LN-2 <= j1p): continue
                    if not leR(M,0,j0p,j1p): continue
                    Mp=seg(M,j0p,j1p)
                    if not monoT(Mp): continue
                    Np=seg(N,j0p,LN-1)
                    TrNp=TrMax(Np)
                    if not (j0N - j0p <= TrNp): continue
                    a=j0p+TrNp+1
                    BrMp=Br(Mp); BrNp=Br(Np)
                    J1=Lng(BrNp)-1
                    # relate seg M a j1p and seg N a (LN-1)
                    # how many whole blocks does seg M a j1p cover past a?
                    if shown<25:
                        segMa=seg(M,a,j1p); segNa=seg(N,a,LN-1)
                        print(f"N={N} n={n} j0p={j0p} j1p={j1p} j0N={j0N} w={w} a={a} TrNp={TrNp}")
                        print(f"   BrNp={BrNp}  (J1={J1})")
                        print(f"   BrMp={BrMp}")
                        print(f"   takeJ1 BrNp = {BrNp[:J1]}")
                        print(f"   tail BrMp[J1:] = {BrMp[J1:]}")
                        shown+=1
    print("done")

if __name__=='__main__':
    main()
