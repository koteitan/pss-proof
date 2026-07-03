#!/usr/bin/env python3
"""r24: for nadm condVI hosts, compute Trans(s84x_L M k), Trans(s84x_Lp M),
and check the abstract L-tower recurrence + the exact s0/b0/e3/ub core."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import Lng, entry, P, monoT, seg, diagSeq, parent, oper, fmt
import red_model as rm
import trans_model as tm
from _r15_vx_lib import (Trans, Mark, gen_pool, mono_hosts, guarded, SKIP,
                         condVI, internals, lessBT, flatBT)
from trans_model import (Dpt, ZB, adm, Adm, Pred, reduced, bpHeadV, bpHeadT,
                         scb_decomps)

def transJ0(M): return parent(M,0,Lng(M)-1)
def s84x_jm2(M): return parent(M,1,Lng(M)-1)
def s84x_L(M,n):
    jm2=s84x_jm2(M); Mn=oper(M,n)
    col=(entry(M,0,jm2)+n*(entry(M,0,Lng(M)-1)-entry(M,0,jm2)), entry(M,1,jm2))
    return Mn+[col]
def s84x_Lp(M):
    jm2=s84x_jm2(M)
    return seg(M,jm2,Lng(M)-2)+[(entry(M,0,Lng(M)-1), entry(M,1,jm2))]

def main():
    pool = gen_pool(maxlen=11, maxn=5, maxseed=4, cap=10000, oper_budget=4)
    hosts = mono_hosts(pool)
    nadm = [M for M in hosts if Lng(M)>=4 and Lng(M)-1>1 and reduced(M)
            and guarded(condVI,M,budget=5) is not SKIP and condVI(M)
            and not adm(M,transJ0(M))]
    print(f"nadm-j0 condVI hosts: {len(nadm)}")
    # variety: group by (t2 shape). Print a few with non-trivial t2/s0.
    print("\n=== L-values for nadm hosts (Lp, L1, L2) ===")
    shown=0
    for M in nadm:
        info=internals(M);
        if info is None: continue
        v=info['v']; t2=info['t2']; s1=info['s1']; b1=info['b1']
        Lp=guarded(s84x_Lp,M,budget=5); L1=guarded(s84x_L,M,1,budget=5); L2=guarded(s84x_L,M,2,budget=5)
        if Lp is SKIP or L1 is SKIP or L2 is SKIP: continue
        TLp=guarded(Trans,tuple(Lp),budget=8); TL1=guarded(Trans,tuple(L1),budget=8); TL2=guarded(Trans,tuple(L2),budget=8)
        if SKIP in (TLp,TL1,TL2): continue
        u=entry(M,1,transJ0(M))
        # only show variety: t2 with >1 principal or nested
        interesting = (len(t2[1])!=1) or (t2[1] and t2[1][0][2]!=ZB)
        if shown<8 and (interesting or shown<4):
            print(f"\nM={fmt(M)} v={v} u={u} t2={flatBT(t2)} s1={s1} b1={b1}")
            print(f"  Trans(Lp)  = {flatBT(TLp)}")
            print(f"  Trans(L1)  = {flatBT(TL1)}")
            print(f"  Trans(L2)  = {flatBT(TL2)}")
            shown+=1

    # Hypothesis A: flatBT(Trans(s84x_L M k)) = s1 @ [Dv] @ [Du]^{k+1} @ [Z] @ b1  (k>=1)
    #   i.e. the L-host tower is D_v(D_u^{k+1} 0)
    print("\n=== Hypothesis: Trans(s84x_L M k) = s1 [Dv] [Du]^{k+1} [Z] b1 ===")
    def Dtower(u,k):
        t=ZB
        for _ in range(k): t=Dpt(u,t)
        return t
    ok=0;tot=0;bad=[]
    for M in nadm:
        info=internals(M)
        if info is None: continue
        v=info['v']; s1=info['s1']; b1=info['b1']; u=entry(M,1,transJ0(M))
        for k in range(1,min(Lng(M),6)):
            L=guarded(s84x_L,M,k,budget=5)
            if L is SKIP: continue
            TL=guarded(Trans,tuple(L),budget=8)
            if TL is SKIP: continue
            want=s1+[('D',v)]+flatBT(Dtower(u,k+1))+b1
            tot+=1
            if flatBT(TL)==want: ok+=1
            else: bad.append((fmt(M),k,flatBT(TL),want))
    print(f"  matches {ok}/{tot}")
    for b in bad[:6]: print("  BAD:",b)

    # And Trans(M[m]) = s1 [Dv] [Du]^m [Z] b1  (m>=1), k=m in d6x cf'
    print("\n=== Trans(M[m]) = s1 [Dv] [Du]^m [Z] b1 (k=m) ===")
    ok2=0;tot2=0;bad2=[]
    for M in nadm:
        info=internals(M)
        if info is None: continue
        v=info['v']; s1=info['s1']; b1=info['b1']; u=entry(M,1,transJ0(M))
        for m in range(1,min(Lng(M)+1,7)):
            Mm=guarded(oper,M,m,budget=5)
            if Mm is SKIP: continue
            TM=guarded(Trans,tuple(Mm),budget=8)
            if TM is SKIP: continue
            want=s1+[('D',v)]+flatBT(Dtower(u,m))+b1
            tot2+=1
            if flatBT(TM)==want: ok2+=1
            else: bad2.append((fmt(M),m,flatBT(TM),want))
    print(f"  matches {ok2}/{tot2}")
    for b in bad2[:6]: print("  BAD:",b)

if __name__=='__main__':
    main()
