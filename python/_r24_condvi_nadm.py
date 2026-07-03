#!/usr/bin/env python3
"""r24: characterize the NON-admissible-j0 condVI hosts and check whether the
L-tower route (Trans(M[m]) = Trans(s84x_L M (m-1))) gives the d6x cf' shape
s1 @ flatBP(DB (transV M) (Dtower (M_{1,j0}) k)) @ b1."""
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
def Dtower(u,k):
    t=ZB
    for _ in range(k): t=Dpt(u,t)
    return t
def flatBP(v,t): return [('D',v)]+flatBT(t)

def scbdecomp_c2(M):
    """canonical (s1,b1) from Trans(Pred M) at flat(c1)"""
    info=internals(M)
    if info is None: return None
    return info['s1'], info['b1'], info

def main():
    pool = gen_pool(maxlen=11, maxn=5, maxseed=4, cap=10000, oper_budget=4)
    hosts = mono_hosts(pool)
    nadm = [M for M in hosts if Lng(M)>=4 and Lng(M)-1>1 and reduced(M)
            and guarded(condVI,M,budget=5) is not SKIP and condVI(M)
            and not adm(M,transJ0(M))]
    print(f"nadm-j0 condVI hosts: {len(nadm)}")

    print("\n=== sample nadm internals + M[n] ===")
    for M in nadm[:5]:
        info=internals(M)
        j0=transJ0(M); j1=Lng(M)-1
        u=entry(M,1,j0)
        v=info['v']; t2=info['t2']; c1=info['c1']; c2=info['c2']
        jm1=info['jm1']; s1=info['s1']; b1=info['b1']
        print(f"\nM={fmt(M)}  j0={j0} j1={j1} M1j0={u} M1j1={entry(M,1,j1)} jm1(Adm)={jm1}")
        print(f"  v={v} t2={t2}")
        print(f"  c1={flatBT(c1)}  c2={flatBT(c2)}  s1={s1} b1={b1}")
        print(f"  Trans M = {flatBT(Trans(M))}")
        for n in range(1,min(Lng(M),5)):
            Mn=guarded(oper,M,n,budget=5)
            if Mn is SKIP: continue
            Tn=guarded(Trans,tuple(Mn),budget=8)
            print(f"  M[{n}]={fmt(Mn):26s} Trans={flatBT(Tn) if Tn is not SKIP else '?'}")

    # check the d6x cf' closed form: flatBT(Trans M[m]) = s1 @ flatBP(v, Dtower(u,k)) @ b1
    print("\n=== d6x cf' shape check on nadm: exists k s.t. flat = s1 @ [Dv] Dtower(u,k) @ b1 ===")
    okc=0; totc=0; bad=[]
    for M in nadm:
        info=internals(M)
        if info is None: continue
        s1=info['s1']; b1=info['b1']; v=info['v']; j0=transJ0(M); u=entry(M,1,j0)
        for m in range(2, min(Lng(M)+1,7)):
            Mn=guarded(oper,M,m,budget=5)
            if Mn is SKIP: continue
            Tn=guarded(Trans,tuple(Mn),budget=8)
            if Tn is SKIP: continue
            fn=flatBT(Tn)
            totc+=1
            # search k in 0..m
            found=None
            for k in range(0, m+2):
                want=s1+flatBP(v,Dtower(u,k))+b1
                if fn==want: found=k; break
            if found is not None: okc+=1
            else: bad.append((fmt(M),m,fn,s1,v,u,b1))
    print(f"  cf' shape matches {okc}/{totc}")
    for b in bad[:6]: print("  BAD:",b)

    # also: is M[m] = s84x_L M (m-1) structurally? (boundary regime)
    print("\n=== boundary M[Suc n] = s84x_L M n check (nadm) ===")
    def s84x_L(M,n):
        jm2=parent(M,1,Lng(M)-1)
        Mn=oper(M,n)
        col=(entry(M,0,jm2)+n*(entry(M,0,Lng(M)-1)-entry(M,0,jm2)), entry(M,1,jm2))
        return Mn+[col]
    okb=0;totb=0;badb=[]
    for M in nadm:
        for n in range(1,min(Lng(M),5)):
            Mn1=guarded(oper,M,n+1,budget=5)
            if Mn1 is SKIP: continue
            L=guarded(s84x_L,M,n,budget=5)
            if L is SKIP: continue
            totb+=1
            if list(Mn1)==list(L): okb+=1
            else: badb.append((fmt(M),n,fmt(Mn1),fmt(L)))
    print(f"  M[Suc n]=L_n matches {okb}/{totb}")
    for b in badb[:5]: print("  BAD:",b)

if __name__=='__main__':
    main()
