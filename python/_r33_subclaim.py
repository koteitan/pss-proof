#!/usr/bin/env python3
# r33: FAST validation of the ROW10-induction sub-claims over reduced monoT.
# (a) hasParent M 1 j => hasParent M 0 j
# (b) entry M 1 j > 0 => hasParent M 1 j      [key: makes the induction clean]
# (c) hasParent M 1 j => entry M 1 (parent1) <= entry M 0 (parent1)  (IH shape)
# Also re-confirm MAIN: entry M 1 j <= entry M 0 j (all j), WITHOUT descending.
import sys, itertools
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, monoT, Br, Red, hasParent, parent, fmt)
def is_reduced(M): return Red(list(M))==list(M)
allj_ok=allj_bad=0; a_ok=a_bad=0; b_ok=b_bad=0
cex_all=[]; cex_a=[]; cex_b=[]; nred=0
GRID=[(x,y) for x in range(4) for y in range(4)]
for L in range(2,6):
    for tup in itertools.product(GRID,repeat=L-1):
        M=[(0,0)]+list(tup)
        if not (monoT(M) and is_reduced(M)): continue
        nred+=1
        n=Lng(M)
        for j in range(n):
            r0=entry(M,0,j); r1=entry(M,1,j)
            if r1<=r0: allj_ok+=1
            else:
                allj_bad+=1
                if len(cex_all)<8: cex_all.append((fmt(M),j,r0,r1))
            hp0=hasParent(M,0,j); hp1=hasParent(M,1,j)
            if hp1:
                if hp0: a_ok+=1
                else:
                    a_bad+=1
                    if len(cex_a)<8: cex_a.append((fmt(M),j))
            if r1>0:
                if hp1: b_ok+=1
                else:
                    b_bad+=1
                    if len(cex_b)<8: cex_b.append((fmt(M),j,r1,hp0))
print(f"reduced-monoT (no descending filter) checked: {nred}")
print(f"[MAIN] all j: entry M 1 j <= entry M 0 j : ok={allj_ok} bad={allj_bad}")
print(f"[a] hasParent1 j => hasParent0 j : ok={a_ok} bad={a_bad}")
print(f"[b] entry1 j>0 => hasParent1 j : ok={b_ok} bad={b_bad}")
for x in cex_all: print("  CEX-MAIN",x)
for x in cex_a: print("  CEX-a",x)
for x in cex_b: print("  CEX-b (M,j,r1,hasP0)",x)
