#!/usr/bin/env python3
"""Audit §6.5/§6.6 propositions on all of T_PS for falsity (over-claimed domain)."""
import itertools, os
from red_model import (Red, fmt, Lng, entry, P, multiT, monoT, zeroT, le0, le1,
    leR, nextR, TrMax, Br, oper, IncrFirst, seg)

def Pred(M): return M[:-1] if Lng(M)>1 else M
def reduced(M): return Red(M)==M   # RT_PS membership

def enum(maxlen,maxe):
    cols=[(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    for L in range(1,maxlen+1):
        for M in itertools.product(cols,repeat=L):
            yield list(M)

# each prop: name -> (fn(M)->bool ok, needs_n)
def p_Red_zeroT(M): return zeroT(M)==zeroT(Red(M))
def p_Red_monoT(M): return monoT(M)==monoT(Red(M))
def p_P_Red(M): return P(Red(M))==[Red(b) for b in P(M)]
def p_Red_idem(M): return Red(Red(M))==Red(M)
def p_Red_Pred(M): return Red(Pred(M))==Pred(Red(M))
def p_Red_IncrFirst(M): return Red(IncrFirst(M))==Red(M)
def p_Red_le(M):
    R=Red(M); n=Lng(M)
    return all(leR(M,i,a,b)==leR(R,i,a,b) for i in(0,1) for a in range(n) for b in range(n))
def p_Lng_Red(M): return Lng(Red(M))==Lng(M)
def p_Red_leftend1(M): return entry(Red(M),1,0)==entry(M,1,0)
def p_P_reduced(M): return reduced(M)==all(reduced(b) for b in P(M))
def p_reduced_oper(M,n):
    if not reduced(M): return True   # premise
    return reduced(oper(M,n))
def p_Red_oper(M,n): return oper(Red(M),n)==Red(oper(M,n))

PROPS_noN={
 "6.5 Red_zeroT":p_Red_zeroT, "6.5 Red_monoT":p_Red_monoT, "6.5 P_Red":p_P_Red,
 "6.5 Red_idem":p_Red_idem, "6.5 Red_Pred":p_Red_Pred, "6.5 Red_IncrFirst":p_Red_IncrFirst,
 "6.5 Red_le":p_Red_le, "6.5 Lng_Red":p_Lng_Red, "6.6 Red_leftend_1":p_Red_leftend1,
 "6.6 P_reduced":p_P_reduced,
}
PROPS_N={ "6.5 Red_oper":p_Red_oper, "6.6 reduced_oper":p_reduced_oper }

def main():
    os.chdir(os.path.dirname(__file__))
    res={k:[0,0,None] for k in list(PROPS_noN)+list(PROPS_N)}  # pass,fail,counterex
    for M in enum(4,2):
        for k,f in PROPS_noN.items():
            try: ok=f(M)
            except Exception: ok=False
            if ok: res[k][0]+=1
            else:
                res[k][1]+=1
                if res[k][2] is None: res[k][2]=fmt(M)
        for k,f in PROPS_N.items():
            okall=True; ce=None
            for n in (1,2,3):
                try: ok=f(M,n)
                except Exception: ok=False
                if not ok: okall=False; ce=f"{fmt(M)}[{n}]"; break
            if okall: res[k][0]+=1
            else:
                res[k][1]+=1
                if res[k][2] is None: res[k][2]=ce
    print(f"{'proposition':22s} {'pass':>6s} {'fail':>6s}  min counterexample")
    for k,(p,fl,ce) in res.items():
        tag = "OK(T_PS)" if fl==0 else "FALSE on T_PS"
        print(f"{k:22s} {p:6d} {fl:6d}  {tag:14s} {ce or ''}")

if __name__=="__main__": main()
