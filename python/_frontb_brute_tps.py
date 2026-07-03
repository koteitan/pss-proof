#!/usr/bin/env python3
"""Brute-force over ALL nonempty pairseqs (T_PS = {M != []}) up to small length/value,
filter by RedCondA, and check red_le / le0 / le1 invariance. This is the true T_PS
domain (NOT restricted to standard), which is what m_6_5_RedCondA_Red_le claims."""
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

def red_le_eq(M):
    try:
        R=Red(M)
    except Exception as e:
        return (None,('REDERR',str(e)[:40]))
    if Lng(R)!=Lng(M): return (False,('LNGMM',fmt(R)))
    n=Lng(M)
    for i in (0,1):
        for j0 in range(n):
            for j1 in range(n):
                if leR(M,i,j0,j1)!=leR(R,i,j0,j1):
                    return (False,(i,j0,j1,fmt(R)))
    return (True,None)

def le0_eq(M):
    R=Red(M); n=Lng(M)
    if Lng(R)!=n: return (False,('LNGMM',))
    for j0 in range(n):
        for j1 in range(n):
            if le0(M,j0,j1)!=le0(R,j0,j1): return (False,(j0,j1,fmt(R)))
    return (True,None)

def le1_eq(M):
    R=Red(M); n=Lng(M)
    if Lng(R)!=n: return (False,('LNGMM',))
    for j0 in range(n):
        for j1 in range(n):
            if le1(M,j0,j1)!=le1(R,j0,j1): return (False,(j0,j1,fmt(R)))
    return (True,None)

def main():
    maxlen,maxval = (int(sys.argv[1]),int(sys.argv[2])) if len(sys.argv)>2 else (4,3)
    print(f"# brute T_PS: maxlen={maxlen} maxval={maxval}")
    vals=range(maxval+1)
    cells=[(a,b) for a in vals for b in vals]
    tot=condA=0
    rle_t=rle_f=rle_err=0
    le0_f=le1_f=0
    ces=[]; ce0=[]; ce1=[]
    for L in range(1,maxlen+1):
        for M in itertools.product(cells, repeat=L):
            M=list(M)
            tot+=1
            if not RedCondA(M): continue
            condA+=1
            ok,first=red_le_eq(M)
            if ok is None: rle_err+=1; continue
            if ok: rle_t+=1
            else:
                rle_f+=1
                if len(ces)<10: ces.append((fmt(M),first))
            o0,f0=le0_eq(M)
            if not o0:
                le0_f+=1
                if len(ce0)<10: ce0.append((fmt(M),f0))
            o1,f1=le1_eq(M)
            if not o1:
                le1_f+=1
                if len(ce1)<10: ce1.append((fmt(M),f1))
    print(f"total pairseqs={tot}  RedCondA={condA}")
    print(f"(a) RedCondA ==> red_le: TRUE={rle_t} FALSE={rle_f} REDERR={rle_err}")
    for c in ces: print("    CE(a):",c)
    print(f"(c) RedCondA ==> le0 inv: FALSE={le0_f}")
    for c in ce0: print("    CE(c):",c)
    print(f"(c1) RedCondA ==> le1 inv: FALSE={le1_f}")
    for c in ce1: print("    CE(c1):",c)

if __name__=='__main__':
    main()
