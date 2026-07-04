#!/usr/bin/env python3
# r33: test alternative sub-claims to prove entry M 1 j <= entry M 0 j.
# (c') hasParent M 0 j => entry M 1 j <= entry M 1 (parent0 j) + 1
# (b0) hasParent M 0 j & entry M 1 j>0 => hasParent M 1 j   (b restricted)
# (e)  hasParent M 1 j => le0 M (parent1 j) (parent0 j)     (p1 <= p0 in le0)
import sys, itertools
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, monoT, Red, hasParent, parent, le0, fmt)
def is_reduced(M): return Red(list(M))==list(M)
cp_ok=cp_bad=0; b0_ok=b0_bad=0; e_ok=e_bad=0
cex_cp=[]; cex_e=[]; nred=0
GRID=[(x,y) for x in range(4) for y in range(4)]
for L in range(2,6):
    for tup in itertools.product(GRID,repeat=L-1):
        M=[(0,0)]+list(tup)
        if not (monoT(M) and is_reduced(M)): continue
        nred+=1; n=Lng(M)
        for j in range(n):
            r1=entry(M,1,j); hp0=hasParent(M,0,j); hp1=hasParent(M,1,j)
            if hp0:
                p0=parent(M,0,j)
                if r1 <= entry(M,1,p0)+1: cp_ok+=1
                else:
                    cp_bad+=1
                    if len(cex_cp)<8: cex_cp.append((fmt(M),j,r1,entry(M,1,p0)))
                if r1>0:
                    if hp1: b0_ok+=1
                    else: b0_bad+=1
            if hp1:
                p1=parent(M,1,j); p0=parent(M,0,j) if hp0 else None
                if hp0 and le0(M,p1,p0): e_ok+=1
                else:
                    e_bad+=1
                    if len(cex_e)<8: cex_e.append((fmt(M),j,p1,p0))
print(f"reduced-monoT checked: {nred}")
print(f"[c'] hasP0 j => entry1 j <= entry1(p0)+1 : ok={cp_ok} bad={cp_bad}")
print(f"[b0] hasP0 & entry1>0 => hasP1 : ok={b0_ok} bad={b0_bad}")
print(f"[e]  hasP1 => le0 M p1 p0 : ok={e_ok} bad={e_bad}")
for x in cex_cp: print("  CEX-c' (M,j,r1,r1p0)",x)
for x in cex_e: print("  CEX-e (M,j,p1,p0)",x)
