#!/usr/bin/env python3
r"""r26 lean: (i) confirm the CEX is a valid W2 instance; (ii) brute-force W2
verdict on small straddle hosts; (iii) full-regime VE'(1) on small pool."""
import sys, os, itertools, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm
from red_model import (Lng, entry, monoT, zeroT, seg, parent, Adm, fmt,
                       Br, Joints, FirstNodes)
from trans_model import Trans, Mark, Pred, bpHeadT, reduced, adm

def pr(*a): print(*a, flush=True)
def safeT(M):
    try: return Trans(list(M))
    except Exception: return None
def brm(n,K):
    out=[]
    for pr_ in itertools.product(itertools.product(range(K+1),range(K+1)),repeat=n):
        S=list(pr_)
        if zeroT(S) or not monoT(S) or not reduced(S): continue
        out.append(S)
    return out
def descending(br):
    n=len(br)
    for a in range(n):
        for b in range(a,n):
            a0,a1=entry(br[a],0,0),entry(br[a],1,0); b0,b1=entry(br[b],0,0),entry(br[b],1,0)
            if not (a0>=b0 and (a0!=b0 or a1>=b1)): return False
    return True
def regime(M,m):
    br=Br(M)
    if not br: return False
    j1=Lng(M)-1; J1=len(br)-1; j0p=Joints(M)[J1]; j1p=FirstNodes(M)[J1]
    if m>j1-1: return False
    if m<j0p: return True
    return (m==j0p and entry(M,0,j1p)==entry(M,1,j1p) and descending(br))

# (i) the CEX as W2 instance
pr("=== (i) CEX as W2 instance (H, r, c) ===")
H=[(0,0),(1,1),(2,2),(1,0)]; r=1; c=3
pr("H=",fmt(H),"r=",r,"c=",c,"Lng H=",Lng(H))
pr("  reduced",reduced(H),"monoT",monoT(H),"~adm H r",not adm(H,r),
   "1<=r<c<LngH",(1<=r<c<Lng(H)))
S=seg(H,r-1,c); inner=seg(H,r,c)
pr("  SR: seg H(r-1)c=",fmt(S)," reduced",reduced(S),"monoT",monoT(S))
pr("  inner seg H r c=",fmt(inner))
pr("  bpHeadT Trans(inner)=",bpHeadT(safeT(inner)))
pr("  bpHeadT Trans(S)    =",bpHeadT(safeT(S)))
pr("  W2 holds:", bpHeadT(safeT(inner))==bpHeadT(safeT(S)),"<-- FALSE => W2 refuted")

# (ii) brute W2 verdict
pr("\n=== (ii) brute-force W2 verdict ===")
pool=[]
for n,K in [(4,3),(4,4),(5,2),(5,3)]:
    pool += brm(n,K)
seen=set(); uH=[]
for Hh in pool:
    k=tuple(Hh)
    if k not in seen: seen.add(k); uH.append(Hh)
pr("  host pool=",len(uH))
ok=bad=0; ninst=0; cex=[]; reg_bad=[0,0]
t0=time.time()
for Hh in uH:
    if time.time()-t0>120: pr("  (budget)"); break
    LH=Lng(Hh)
    for rr in range(1,LH):
        if adm(Hh,rr): continue
        for cc in range(rr+1,LH):
            SS=seg(Hh,rr-1,cc)
            if zeroT(SS) or not monoT(SS) or not reduced(SS): continue
            inn=seg(Hh,rr,cc)
            a=safeT(inn); b=safeT(SS)
            if a is None or b is None: continue
            ninst+=1
            rg=regime(SS,1)
            if bpHeadT(a)==bpHeadT(b):
                ok+=1
                if not rg: reg_bad[0]+=1  # W2 holds but regime false
            else:
                bad+=1
                if rg: reg_bad[1]+=1       # W2 fails but regime true (regime doesnt help)
                if len(cex)<12: cex.append((fmt(Hh),'r=%d'%rr,'c=%d'%cc,'regime=%s'%rg))
pr("  W2 instances=%d  OK=%d  BAD=%d"%(ninst,ok,bad))
pr("  (W2 ok & ~regime)=%d   (W2 bad & regime)=%d"%(reg_bad[0],reg_bad[1]))
if cex: pr("  W2 CEX:",cex)

# (iii) full-regime VE'(1) on small pool
pr("\n=== (iii) full-regime VE'(1) ===")
rv=[0,0]; nadmrv=[0,0]; fails=[]
for S in uH:
    if not (1<Lng(S)-1): continue
    if not regime(S,1): continue
    a=safeT(S); b=safeT(seg(S,1,Lng(S)-1))
    if a is None or b is None: continue
    v=(bpHeadT(a)==bpHeadT(b))
    rv[0 if v else 1]+=1
    if not adm(S,1): nadmrv[0 if v else 1]+=1
    if not v and len(fails)<10: fails.append((fmt(S),'adm1=%s'%adm(S,1)))
pr("  regime(S,1)&VE1 ok=%d fail=%d"%(rv[0],rv[1]))
pr("    of which ~adm-1: ok=%d fail=%d"%(nadmrv[0],nadmrv[1]))
if fails: pr("  regime-VE1 fails:",fails)
pr("done")
