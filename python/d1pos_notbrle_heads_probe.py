#!/usr/bin/env python3
"""Verify the EXACT head-value stub claims for the d1pos ¬brle regime-B descending assembly.

Stub design (what agent A delivers, what I cite):
  Br M' = PRE @ [TL]  where len(PRE)=J1=len(Br Np)-1, TL=Br M'[-1] single P-comp, and
  k = (j0' - jm2) div w  (block index of j0'),  Np = seg N j0r (LN-1), j0r=jm2+(j0'-jm2 mod w).
  For each J<J1:
    entry (PRE!J) 0 0 = entry (Br Np!J) 0 0 + k*delta     [row-0 +k*delta]
    entry (PRE!J) 1 0 = entry (Br Np!J) 1 0               [row-1 unshifted]
  junction (cdom (Br Np!(J1-1)) ... ) and tail vs Br Np!J1:
    entry TL 0 0 = entry (Br Np!J1) 0 0 + k*delta         [row-0 same shift]
    entry TL 1 0 <= entry (Br Np!J1) 1 0                  [row-1 drop or eq]
  => prefix descending (uniform row-0 shift + unshifted row-1 preserves descending(Br Np)),
     junction cdom (last PRE)(TL) from cdom(Br Np!(J1-1))(Br Np!J1) + the shift facts.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, Br, is_standard, fmt, le0)

def gen_std(maxlen, maxval, KMAX):
    base = [[(j, j) for j in range(u, v + 1)] for u in range(maxval + 1)
            for v in range(u, maxval + 1)]
    store = {fmt(m): m for m in base}; frontier = list(base)
    for _ in range(KMAX):
        newf = []
        for M in frontier:
            for n in range(1, 4):
                Mp = oper(M, n); key = fmt(Mp)
                if Mp and len(Mp) <= maxlen and all(a <= maxval and b <= maxval for (a, b) in Mp) \
                        and key not in store:
                    store[key] = Mp; newf.append(Mp)
        frontier = newf
    return [m for m in store.values() if is_standard(m)]

def is_d1pos(N):
    j1 = Lng(N) - 1
    return j1 >= 1 and not (entry(N,0,j1)==0 and entry(N,1,j1)==0) \
           and idx1(N, j1) == 1 and hasParent(N, 1, j1)

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (8, 4, 4)
    Ns = gen_std(maxlen, maxval, KMAX)
    d1 = [N for N in Ns if is_d1pos(N)]
    nb=0; r0pre=r1pre=0; preN=0; tl0=tl1=0; junc_cdom=0
    bad=[]
    for N in d1:
        LN=Lng(N); j1N=LN-1; jm2=parent(N,1,j1N); w=j1N-jm2
        delta=entry(N,0,j1N)-entry(N,0,jm2)
        for n in (1,2,3):
            M=oper(N,n)
            if Lng(M)<2: continue
            for j0p in range(Lng(M)):
                for j1p in range(j0p+1,Lng(M)):
                    if not le0(M,j0p,j1p): continue
                    Mp=seg(M,j0p,j1p)
                    if not monoT(Mp): continue
                    t=TrMax(Mp)
                    if t==Lng(Mp)-1: continue
                    if le0(Mp,t+1,Lng(Mp)-1): continue
                    BrMp=Br(Mp)
                    if len(BrMp)<2: continue
                    nb+=1
                    k=(j0p-jm2)//w
                    j0r=jm2+((j0p-jm2)%w)
                    Np=seg(N,j0r,LN-1)
                    if not (monoT(Np) and Br(Np)): bad.append(('np',fmt(N),n,j0p,j1p)); continue
                    BrNp=Br(Np); J1=len(BrNp)-1
                    PRE=BrMp[:-1]; TL=BrMp[-1]
                    if len(PRE)!=J1: bad.append(('len',fmt(N),n,j0p,j1p,len(PRE),J1)); continue
                    preN+=1
                    okr0=all(PRE[J][0][0]==BrNp[J][0][0]+k*delta for J in range(J1))
                    okr1=all(PRE[J][0][1]==BrNp[J][0][1] for J in range(J1))
                    if okr0: r0pre+=1
                    else: bad.append(('r0pre',fmt(N),n,j0p,j1p,k,delta,[c[0] for c in PRE],[c[0] for c in BrNp]))
                    if okr1: r1pre+=1
                    else: bad.append(('r1pre',fmt(N),n,j0p,j1p))
                    # tail head vs Br Np ! J1
                    if TL[0][0]==BrNp[J1][0][0]+k*delta: tl0+=1
                    else: bad.append(('tl0',fmt(N),n,j0p,j1p,k,delta,TL[0],BrNp[J1][0]))
                    if TL[0][1]<=BrNp[J1][0][1]: tl1+=1
                    else: bad.append(('tl1',fmt(N),n,j0p,j1p,TL[0],BrNp[J1][0]))
    print(f"#d1pos={len(d1)}  ¬brle multi={nb}  len(PRE)==J1: {preN}/{nb}")
    print(f"  PRE row-0 = BrNp+k*delta: {r0pre}/{preN}")
    print(f"  PRE row-1 = BrNp (unshifted): {r1pre}/{preN}")
    print(f"  TL row-0 = BrNp[J1]+k*delta: {tl0}/{preN}")
    print(f"  TL row-1 <= BrNp[J1]: {tl1}/{preN}")
    if bad: print("  BAD(first 8):"); [print('   ',b) for b in bad[:8]]
    else: print("  ALL CONSISTENT")

if __name__=='__main__': main()
