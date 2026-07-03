#!/usr/bin/env python3
r"""r26: (A2) full-regime VE'(1) test; (B) direct W2 on brute straddle hosts,
robust against Trans exceptions."""
import sys, os, itertools, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm
from red_model import (Lng, entry, monoT, zeroT, seg, parent, Adm, fmt,
                       TrMax, Br, Joints, FirstNodes)
from trans_model import Trans, Mark, Pred, bpHeadT, bpHeadV, reduced, adm

def pr(*a): print(*a, flush=True)

def brute_reduced_monoT(n, K):
    out=[]
    for pairs in itertools.product(itertools.product(range(K+1),range(K+1)),repeat=n):
        S=list(pairs)
        if zeroT(S) or not monoT(S): continue
        if not reduced(S): continue
        out.append(S)
    return out

def descending(br):
    n=len(br)
    for a in range(n):
        for b in range(a,n):
            a0,a1=entry(br[a],0,0),entry(br[a],1,0)
            b0,b1=entry(br[b],0,0),entry(br[b],1,0)
            if not (a0>=b0 and (a0!=b0 or a1>=b1)): return False
    return True

def regime(M,m):
    br=Br(M)
    if not br: return False
    j1=Lng(M)-1; J1=len(br)-1
    j0p=Joints(M)[J1]; j1p=FirstNodes(M)[J1]
    if m>j1-1: return False
    if m<j0p: return True
    return (m==j0p and entry(M,0,j1p)==entry(M,1,j1p) and descending(br))

def safeT(M):
    try: return Trans(list(M))
    except Exception: return None

def ve1(S):
    j1=Lng(S)-1
    a=safeT(S); b=safeT(seg(S,1,j1))
    if a is None or b is None: return None
    return bpHeadT(a)==bpHeadT(b)

# (A2) full regime
pr("=== (A2) VE'(1) under FULL regime(M,1) ===")
hosts=[]
for n,K in [(3,5),(4,4),(5,3),(5,4)]:
    hosts += brute_reduced_monoT(n,K)
seen=set(); uh=[]
for S in hosts:
    k=tuple(S)
    if k not in seen: seen.add(k); uh.append(S)
pr(f"  hosts={len(uh)}")
reg_ve=[0,0]; nadm_reg_ve=[0,0]; reg_fail=[]
t0=time.time()
for S in uh:
    if time.time()-t0>90: pr("  (A2 budget)"); break
    if not (1<Lng(S)-1): continue
    if not regime(S,1): continue
    v=ve1(S)
    if v is None: continue
    reg_ve[0 if v else 1]+=1
    if not adm(S,1):
        nadm_reg_ve[0 if v else 1]+=1
    if not v and len(reg_fail)<12:
        reg_fail.append((fmt(S),'admS1=%s'%adm(S,1)))
pr(f"  regime(M,1) & VE1 = {reg_ve[0]}   regime & ~VE1 = {reg_ve[1]}")
pr(f"    of which ~adm-1: VE1 ok={nadm_reg_ve[0]} fail={nadm_reg_ve[1]}")
if reg_fail: pr("  regime failures:", reg_fail)

# (B) direct W2
pr("\n=== (B) direct W2 on brute straddle hosts ===")
Hs=[]
for n,K in [(4,4),(5,3),(5,4),(6,3)]:
    Hs += brute_reduced_monoT(n,K)
seen=set(); uH=[]
for H in Hs:
    k=tuple(H)
    if k not in seen: seen.add(k); uH.append(H)
pr(f"  host pool={len(uH)}")
W2ok=W2bad=0; ninst=0; w2cex=[]; innermono=[0,0]
# also: among W2 instances, does regime(S,1) hold for S=seg H (r-1) c?
reg_holds=[0,0]
t0=time.time()
for H in uH:
    if time.time()-t0>160: pr("  (B budget)"); break
    LH=Lng(H)
    for r in range(1,LH):
        if adm(H,r): continue
        for c in range(r+1,LH):
            S=seg(H,r-1,c)
            if zeroT(S) or not monoT(S) or not reduced(S): continue
            inner=seg(H,r,c)
            lhs=safeT(inner); rhs=safeT(S)
            if lhs is None or rhs is None: continue
            ninst+=1
            im=(not zeroT(inner)) and monoT(inner)
            innermono[0 if im else 1]+=1
            rg = regime(S,1)
            reg_holds[0 if rg else 1]+=1
            if bpHeadT(lhs)==bpHeadT(rhs): W2ok+=1
            else:
                W2bad+=1
                if len(w2cex)<15:
                    w2cex.append((fmt(H),'r=%d'%r,'c=%d'%c,'S=%s'%fmt(S),
                                  'regimeS1=%s'%rg,'innerMono=%s'%im))
pr(f"  W2 instances={ninst}  OK={W2ok}  BAD={W2bad}")
pr(f"  inner slice monoT yes={innermono[0]} no={innermono[1]}")
pr(f"  regime(S,1) holds for W2 slice: yes={reg_holds[0]} no={reg_holds[1]}")
if w2cex: pr("  W2 CEX:", w2cex)
pr("done")
