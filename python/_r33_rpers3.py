#!/usr/bin/env python3
# r33: fast (no Trans) check of RPERS-guarded: reg3(N) & cfbx_j1p<Lng-1 => reg3(Pred N)
# and cfbx_j1p(Pred N)=cfbx_j1p N.  Over reduced monoT Br!=[] with j0-geometry.
import sys, itertools
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, monoT, Red, Br, FirstNodes, Joints, TrMax, fmt)
def is_reduced(M): return Red(list(M))==list(M)
def cfbx_j1p(M): return FirstNodes(M)[len(Br(M))-1]
def reg2(M): return is_reduced(M) and monoT(M) and len(Br(M))>0
def guard(M):
    j1p=cfbx_j1p(M); return entry(M,0,j1p)>entry(M,1,j1p)
def reg3(M): return reg2(M) and guard(M)
def Pred(M): return M[:-1] if Lng(M)>1 else M
GRID=[(x,y) for x in range(3) for y in range(3)]
rp_ok=rp_bad=0; jp_ok=jp_bad=0; nstep=0; cex=[]
for L in range(3,7):
    for tup in itertools.product(GRID,repeat=L-1):
        M=[(0,0)]+list(tup)
        if not reg3(M): continue
        if cfbx_j1p(M) >= Lng(M)-1: continue  # only STEP
        nstep+=1
        P=Pred(M)
        if reg3(P): rp_ok+=1
        else:
            rp_bad+=1
            if len(cex)<10: cex.append((fmt(M),'reg2P' if reg2(P) else 'notreg2', 'g' if (len(Br(P))>0 and guard(P)) else 'ng'))
        if len(Br(P))>0 and cfbx_j1p(P)==cfbx_j1p(M): jp_ok+=1
        else: jp_bad+=1
print(f"STEP cases (reg3 & cfbx_j1p<Lng-1): {nstep}")
print(f"[RPERS-guarded] reg3(Pred N): ok={rp_ok} bad={rp_bad}")
print(f"[cfbx_j1p stable] cfbx_j1p(Pred N)=cfbx_j1p N: ok={jp_ok} bad={jp_bad}")
for x in cex: print("  CEX",x)
