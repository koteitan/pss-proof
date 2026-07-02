#!/usr/bin/env python3
"""Fast incremental brute over nonempty pairseqs. Flush each line. Catch Red
recursion blowups (garbage non-terminating shapes) and count them separately;
they are NOT T_PS counterexamples to a TRUE statement, just outside the model's
safe domain. Focus: RedCondA ==> red_le, le0-inv, le1-inv."""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, le0, le1, leR, Red, hasParent, parent, fmt)

def RedCondA(M):
    n=Lng(M)
    for i in (0,1):
        for j1 in range(n):
            if hasParent(M,i,j1):
                p=parent(M,i,j1)
                if entry(M,i,p)+1 != entry(M,i,j1):
                    return False
    return True

def main():
    maxlen,maxval = (int(sys.argv[1]),int(sys.argv[2])) if len(sys.argv)>2 else (4,3)
    vals=range(maxval+1)
    cells=[(a,b) for a in vals for b in vals]
    condA=rle_t=rle_f=rerr=le0f=le1f=lnf=0
    ces=[]
    for L in range(1,maxlen+1):
        for Mt in itertools.product(cells, repeat=L):
            M=list(Mt)
            if not RedCondA(M): continue
            condA+=1
            try:
                R=Red(M)
            except Exception:
                rerr+=1; continue
            n=Lng(M)
            if Lng(R)!=n:
                lnf+=1
                if len(ces)<8: ces.append(('LNG',fmt(M),fmt(R)))
                continue
            ok=True; o0=True; o1=True
            for j0 in range(n):
                for j1 in range(n):
                    if le0(M,j0,j1)!=le0(R,j0,j1): o0=False
                    if le1(M,j0,j1)!=le1(R,j0,j1): o1=False
                    for i in (0,1):
                        if leR(M,i,j0,j1)!=leR(R,i,j0,j1): ok=False
            if ok: rle_t+=1
            else:
                rle_f+=1
                if len(ces)<8: ces.append(('RLE',fmt(M),fmt(R)))
            if not o0: le0f+=1
            if not o1: le1f+=1
        print(f"  L<= {L}: condA={condA} rle_T={rle_t} rle_F={rle_f} REDERR={rerr} "
              f"LNGF={lnf} le0F={le0f} le1F={le1f}", flush=True)
    print(f"FINAL condA={condA} rle_T={rle_t} rle_F={rle_f} REDERR={rerr} "
          f"LNGF={lnf} le0F={le0f} le1F={le1f}", flush=True)
    for c in ces: print("  CE:",c, flush=True)

if __name__=='__main__':
    main()
