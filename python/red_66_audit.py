#!/usr/bin/env python3
"""Empirically audit §6.6 (simplification / reducedness) propositions on T_PS,
to validate the next section before formalizing it (and catch over-claims).

  reduced_slice  : M∈RT_PS, j0'≤TrMax M≤j1'≤Lng-1 ⟹ seg M j0' j1' ∈ RT_PS   (1026)
  P_reduced      : M∈T_PS ⟹ (M∈RT_PS ⟺ ∀ blocks of P M reduced)              (1034)
  reduced_oper   : M∈RT_PS, n≥1 ⟹ M[n] ∈ RT_PS                                (1046)
  reduced_iff_cond: M∈T_PS ⟹ (M∈RT_PS ⟺ RedCondA M ∧ RedCondB M)             (1054)
  Red_leftend_1  : entry (Red M) 1 0 = entry M 1 0                            (1064)
"""
import itertools, os
from red_model import Red, fmt, Lng, entry, P, monoT, le0, oper, seg, TrMax, reduced
from red_charac import RedCondA, RedCondB

def enum(maxlen,maxe):
    cols=[(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    for L in range(1,maxlen+1):
        for M in itertools.product(cols,repeat=L): yield list(M)

def p_reduced_slice(M):
    if not reduced(M): return True
    n=Lng(M); t=TrMax(M)
    for a in range(n):
        for b in range(a,n):
            if a<=t<=b<=n-1:
                if not reduced(seg(M,a,b)): return False
    return True
def p_P_reduced(M):
    return reduced(M)==all(reduced(b) for b in P(M))
def p_reduced_oper(M):
    if not reduced(M): return True
    return all(reduced(oper(M,nn)) for nn in (1,2,3))
def p_reduced_iff_cond(M):
    return reduced(M)==(RedCondA(M) and RedCondB(M))
def p_Red_leftend1(M):
    return entry(Red(M),1,0)==entry(M,1,0)

PROPS={"reduced_slice":p_reduced_slice,"P_reduced":p_P_reduced,
       "reduced_oper":p_reduced_oper,"reduced_iff_cond":p_reduced_iff_cond,
       "Red_leftend_1":p_Red_leftend1}

def main():
    os.chdir(os.path.dirname(__file__))
    res={k:[0,0,None] for k in PROPS}
    for M in enum(4,2):
        for k,f in PROPS.items():
            try: ok=f(M)
            except Exception: ok=False
            res[k][0]+=1
            if not ok:
                res[k][1]+=1
                if res[k][2] is None: res[k][2]=fmt(M)
    print(f"{'proposition':18s} {'pass':>6s} {'fail':>6s}  result")
    for k,(p,fl,ex) in res.items():
        tag="OK(T_PS)" if fl==0 else f"FALSE on T_PS (ex={ex})"
        print(f"{k:18s} {p:6d} {fl:6d}  {tag}")

if __name__=="__main__": main()
