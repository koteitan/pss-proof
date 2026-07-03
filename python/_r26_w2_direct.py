#!/usr/bin/env python3
r"""r26-VE1CORE decisive experiment:
(A) Does VE'(1) hold under the REGIME condition monoT(seg S 1 (Lng-1)) (equiv.
    1<=j0'), rather than the wrong ~adm S 1?
(B) Is the ACTUAL W2 statement TRUE on brute-force straddle hosts H?
       W2: H reduced monoT, ~adm H r, 1<=r<c<Lng H, seg H (r-1) c reduced monoT
           ==> bpHeadT(Trans(seg H r c)) == bpHeadT(Trans(seg H (r-1) c))
(C) For W2 slices, is the inner slice seg H r c monoT (regime m=1)?
Also: is there any Lng-3 CEX?"""
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

def j0p(S):
    br=Br(S)
    if not br: return None
    return Joints(S)[len(br)-1]

def ve1(S):
    j1=Lng(S)-1
    return bpHeadT(Trans(list(S)))==bpHeadT(Trans(list(seg(S,1,j1))))

# ---- Lng-3 scan ----
pr("=== Lng-3 ~adm-1 reduced monoT hosts: any CEX? ===")
c3=0; f3=0
for S in brute_reduced_monoT(3,6):
    if adm(S,1): continue
    if not (1<Lng(S)-1): continue
    c3+=1
    if not ve1(S): f3+=1; pr("  L3 CEX:",fmt(S))
pr(f"  Lng-3 ~adm-1 hosts={c3}, VE1 failures={f3}")

# ---- (A) VE'(1) under regime monoT(slice) ----
pr("\n=== (A) VE'(1) restricted to slice-monoT (regime) ===")
hosts=[]
for n,K in [(3,5),(4,4),(5,3)]:
    hosts += brute_reduced_monoT(n,K)
seen=set(); uh=[]
for S in hosts:
    k=tuple(S)
    if k not in seen: seen.add(k); uh.append(S)
pr(f"  reduced monoT hosts (Lng>=3) = {len(uh)}")
# among ~adm-1 hosts, split by slice-monoT
tt=[0,0]; # slice-monoT & VE, slice-monoT & ~VE
badadm=[]; # regime-restricted failures
nadm_tot=0; nadm_slicemono=0
j0_ge1_ve=[0,0]
t0=time.time()
for S in uh:
    if time.time()-t0>90: pr("  (A time budget)"); break
    if adm(S,1): continue
    if not (1<Lng(S)-1): continue
    nadm_tot+=1
    j1=Lng(S)-1
    sl=seg(S,1,j1)
    smono = (not zeroT(sl)) and monoT(sl)
    try:
        v=ve1(S)
    except Exception: continue
    if smono:
        nadm_slicemono+=1
        tt[0 if v else 1]+=1
        if not v: badadm.append((fmt(S),'slice-monoT but VE1 FALSE'))
    # regime via j0': 1<=j0'
    jj=j0p(S)
    if jj is not None and 1<=jj:
        j0_ge1_ve[0 if v else 1]+=1
        if not v and len(badadm)<20: badadm.append((fmt(S),f'1<=j0p={jj} but VE1 FALSE'))
pr(f"  ~adm-1 hosts total={nadm_tot}")
pr(f"  slice-monoT & VE1  = {tt[0]}   slice-monoT & ~VE1 = {tt[1]}")
pr(f"  (1<=j0') & VE1     = {j0_ge1_ve[0]}   (1<=j0') & ~VE1 = {j0_ge1_ve[1]}")
if badadm: pr("  regime failures:", badadm[:20])

# ---- (B) direct W2 over brute straddle hosts ----
pr("\n=== (B) direct W2 statement on brute straddle hosts ===")
W2ok=W2bad=0; w2cex=[]
slice_mono=[0,0]  # inner slice monoT: yes/no among W2 instances
t0=time.time()
Hs=[]
for n,K in [(4,4),(5,3),(5,4),(6,3)]:
    Hs += brute_reduced_monoT(n,K)
seen=set(); uH=[]
for H in Hs:
    k=tuple(H)
    if k not in seen: seen.add(k); uH.append(H)
pr(f"  W2 host pool = {len(uH)}")
ninst=0
for H in uH:
    if time.time()-t0>150: pr("  (B time budget)"); break
    LH=Lng(H)
    for r in range(1,LH):
        if adm(H,r): continue           # need ~adm H r
        for c in range(r+1,LH):          # r<c<Lng H  (c<Lng means c<=LH-1)
            S=seg(H,r-1,c)               # left-extended slice
            if zeroT(S) or not monoT(S) or not reduced(S): continue  # SR
            inner=seg(H,r,c)
            try:
                lhs=bpHeadT(Trans(list(inner)))
                rhs=bpHeadT(Trans(list(S)))
            except Exception: continue
            ninst+=1
            im = (not zeroT(inner)) and monoT(inner)
            slice_mono[0 if im else 1]+=1
            if lhs==rhs: W2ok+=1
            else:
                W2bad+=1
                if len(w2cex)<15:
                    w2cex.append((fmt(H),f'r={r}',f'c={c}',
                                  'innerMono=%s'%im,'S=%s'%fmt(S)))
pr(f"  W2 instances={ninst}  OK={W2ok}  BAD={W2bad}")
pr(f"  inner slice monoT: yes={slice_mono[0]} no={slice_mono[1]}")
if w2cex: pr("  W2 CEX:", w2cex[:15])
pr("\ndone")
