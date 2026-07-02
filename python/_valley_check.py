#!/usr/bin/env python3
"""Empirical check of the cross-block VALLEY clause of oper_parent1_readback_interior,
the periodic row-1 readback, and the N->M le0 reflection.  Memoized le0 per sequence."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, nextrel0, idx1, hasParent, parent, oper,
                       diagSeq, IncrFirst)

def reach_matrix(M):
    n=Lng(M)
    edges=[(a,b) for a in range(n) for b in range(n) if nextrel0(M,a,b)]
    R=[[i==j for j in range(n)] for i in range(n)]
    changed=True
    while changed:
        changed=False
        for (c,d) in edges:
            for a in range(n):
                if R[a][c] and not R[a][d]:
                    R[a][d]=True; changed=True
    return R

def closure(depth, maxlen):
    seen=set(); frontier=[]
    for u in range(0,4):
        for v in range(u,7):
            d=tuple(diagSeq(u,v))
            if d and Lng(d)<=maxlen:
                frontier.append(d); seen.add(d)
    allM=set(frontier)
    for _ in range(depth):
        newf=[]
        for M in frontier:
            Ml=list(map(tuple,M))
            for n in range(1,4):
                try: O=tuple(oper(Ml,n))
                except Exception: continue
                if 1<=Lng(O)<=maxlen and O not in seen:
                    seen.add(O); newf.append(O); allM.add(O)
            I=tuple(IncrFirst(Ml))
            if 1<=Lng(I)<=maxlen and I not in seen:
                seen.add(I); newf.append(I); allM.add(I)
        frontier=newf
    return allM

def fmt(M): return "".join("(%d,%d)"%(a,b) for (a,b) in M)

def main():
    allM=closure(4,12)
    print("closure size:", len(allM))
    checked=0; vok=0; vbad=0; pok=0; pbad=0; rok=0; rbad=0
    bad=[]
    for M in allM:
        M=list(map(tuple,M)); L=Lng(M)
        if L<=1: continue
        j1=L-1
        if entry(M,0,j1)==0 and entry(M,1,j1)==0: continue
        if idx1(M,j1)!=1: continue
        if not hasParent(M,1,j1): continue
        j0=parent(M,1,j1)
        if j0 is None or not(j0<j1): continue
        w=j1-j0
        if w<=0: continue
        Rm=reach_matrix(M)
        def le0M(a,b): return a<L and b<L and Rm[a][b]
        for n in range(2,4):
            N=oper(M,n); LN=Lng(N)
            if LN!=j0+n*w: continue
            Rn=reach_matrix(N)
            def le0N(a,b): return a<LN and b<LN and Rn[a][b]
            # PERIODIC row-1 readback: entry N 1 (j0+qp*w+sp) == entry M 1 (j0+sp)
            for qp in range(n):
                for sp in range(w):
                    jp=j0+qp*w+sp
                    if jp>=LN: continue
                    if entry(N,1,jp)==entry(M,1,j0+sp): pok+=1
                    else:
                        pbad+=1
                        if len(bad)<20: bad.append(("PERIOD",fmt(M),n,qp,sp))
            for s in range(1,w):
                u=j0+s
                if not hasParent(M,1,u): continue
                pM=parent(M,1,u)
                if pM is None or pM<j0: continue
                for q in range(n):
                    y=j0+q*w+s; c=pM+q*w
                    if y>=LN: continue
                    checked+=1
                    eY=entry(N,1,y)
                    vfail=False
                    for jp in range(c+1,LN):
                        if Rn[jp][y]:
                            if entry(N,1,jp)<eY:
                                vfail=True
                                if len(bad)<20: bad.append(("VALLEY",fmt(M),n,q,s,jp,entry(N,1,jp),eY))
                                break
                            # REFLECTION: jp=j0+qp*w+sp, claim entry M 1 (j0+sp) >= entry M 1 u
                            d=jp-j0; qp=d//w; sp=d%w
                            if j0+qp*w+sp==jp:
                                if entry(M,1,j0+sp)>=entry(M,1,u): rok+=1
                                else:
                                    rbad+=1
                                    if len(bad)<25: bad.append(("REFL",fmt(M),n,q,s,jp,qp,sp,entry(M,1,j0+sp),entry(M,1,u)))
                    if vfail: vbad+=1
                    else: vok+=1
    print("checked:", checked)
    print("VALLEY ok/bad:", vok, vbad)
    print("PERIOD ok/bad:", pok, pbad)
    print("REFL(entryM j0+sp >= entryM u) ok/bad:", rok, rbad)
    print("--- bad ---")
    for e in bad: print(e)

if __name__=="__main__":
    main()
