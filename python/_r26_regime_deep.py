#!/usr/bin/env python3
r"""r26: DEEP + WIDE validation of the CORRECT regime-guarded VE'(1):
     cfbx_reg 1 S  ==>  cfbx_VE 1 S
   i.e. regime(S,1) ==> bpHeadT(Trans(seg S 1 (Lng S-1))) == bpHeadT(Trans S).
Straddle (brute) + deep (oper Lng>=9). verify-rank-depth: report any CEX."""
import sys, os, itertools, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm
from red_model import (Lng, entry, monoT, zeroT, seg, parent, Adm, fmt, diagSeq,
                       oper, Br, Joints, FirstNodes, TrMax)
from trans_model import Trans, Mark, Pred, bpHeadT, reduced, adm

def pr(*a): print(*a, flush=True)
_TC={}
_T0=Trans
def T(M):
    k=tuple(M)
    if k not in _TC:
        try: _TC[k]=_T0(list(M))
        except Exception: _TC[k]=None
    return _TC[k]
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
def ve1(S):
    a=T(S); b=T(seg(S,1,Lng(S)-1))
    if a is None or b is None: return None
    return bpHeadT(a)==bpHeadT(b)
def brm(n,K):
    out=[]
    for pr_ in itertools.product(itertools.product(range(K+1),range(K+1)),repeat=n):
        S=list(pr_)
        if zeroT(S) or not monoT(S) or not reduced(S): continue
        out.append(S)
    return out
def gen_pool(maxlen,maxn,maxseed,cap):
    seen=set(); fr=[]
    for u in range(maxseed):
        for v in range(u,u+maxseed+2):
            M=tuple(diagSeq(u,v))
            if M not in seen: seen.add(M); fr.append(list(M))
    pool=list(fr)
    while fr and len(pool)<cap:
        nx=[]
        for M in fr:
            if Lng(M)<=1: continue
            for nn in range(1,maxn+1):
                try: N=oper(M,nn)
                except Exception: continue
                if Lng(N)>maxlen: continue
                t=tuple(N)
                if t not in seen: seen.add(t); nx.append(N); pool.append(N)
                if len(pool)>=cap: break
            if len(pool)>=cap: break
        fr=nx
    return pool

def run(hosts, tag, tb=140, deepmin=0):
    ok=fail=0; cex=[]; nadm_ok=nadm_fail=0; maxL=0
    t0=time.time()
    for S in hosts:
        if time.time()-t0>tb: pr(f"  [{tag}] budget"); break
        if Lng(S)<3 or Lng(S)-1<2: continue
        if deepmin and Lng(S)<deepmin: continue
        if not regime(S,1): continue
        v=ve1(S)
        if v is None: continue
        maxL=max(maxL,Lng(S))
        if v: ok+=1
        else:
            fail+=1
            if len(cex)<15: cex.append((fmt(S),'adm1=%s'%adm(S,1),'TrMax=%d'%TrMax(S)))
        if not adm(S,1): nadm_ok+= (1 if v else 0); nadm_fail+= (0 if v else 1)
    pr(f"  [{tag}] regime-VE'(1): OK={ok} FAIL={fail} maxLng={maxL}"
       f"  (~adm-1 subset ok={nadm_ok} fail={nadm_fail})")
    if cex: pr(f"    CEX={cex}")
    return fail

# brute straddle
bt=[]
for n,K in [(4,4),(5,3),(6,2),(6,3)]:
    bt += brm(n,K)
seen=set(); ub=[]
for S in bt:
    k=tuple(S)
    if k not in seen: seen.add(k); ub.append(S)
pr(f"brute pool={len(ub)}")
f1=run(ub,"BRUTE",tb=150)

# deep oper
dp=gen_pool(maxlen=13,maxn=2,maxseed=7,cap=5000)
pr(f"deep oper pool={len(dp)} maxLng={max(Lng(x) for x in dp)}")
f2=run(dp,"DEEP>=9",tb=200,deepmin=9)
f3=run(dp,"DEEP>=7",tb=120,deepmin=7)

pr(f"\nSUMMARY regime-VE'(1) failures: brute={f1} deep9={f2} deep7={f3}")
pr("done")
