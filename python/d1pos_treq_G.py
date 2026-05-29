#!/usr/bin/env python3
"""Verify TrEq with formula-G (j0red,j1red): TrMax(seg M j0' j1')==TrMax(seg N j0red j1red)?
Also verify the FULL Br identity (LOW=butlast, tail=last) again for formula G, with
shamt=q0*delta, AND verify j0red<j1red and j1red<=LN-1 always hold."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, multiT, Br, is_standard, fmt, le0)
from d1pos_j0j1red_search import gen_std, is_d1pos_mono, brle, full_facts

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (10, 4, 6)
    Ns = [N for N in gen_std(maxlen, maxval, KMAX) if is_d1pos_mono(N)]
    tot=0; treq_ok=0; full_ok=0; bound_ok=0
    treq_fail=[]; full_fail=[]
    for N in Ns:
        LN = Lng(N); jm2 = parent(N, 1, LN-1); w = LN-1-jm2
        if w<=0: continue
        delta=entry(N,0,LN-1)-entry(N,0,jm2)
        for n in (1,2,3):
            M = oper(N, n)
            if Lng(M) < 2: continue
            for j0p in range(Lng(M)):
                for j1p in range(j0p+1, Lng(M)):
                    if j1p < LN-1: continue
                    if not le0(M, j0p, j1p): continue
                    Mp = seg(M, j0p, j1p)
                    if not monoT(Mp): continue
                    if brle(Mp): continue
                    tot += 1
                    q0=(j0p-jm2)//w if j0p>=jm2 else 0
                    j0red=jm2+(j0p-jm2)%w if j0p>=jm2 else j0p
                    j1red=min(j0red+(j1p-j0p),LN-1)
                    shamt=q0*delta
                    Np=seg(N,j0red,j1red)
                    if (j0red<j1red<=LN-1): bound_ok+=1
                    else: continue
                    if TrMax(Mp)==TrMax(Np): treq_ok+=1
                    elif len(treq_fail)<6: treq_fail.append((fmt(N),n,j0p,j1p,'TrM',TrMax(Mp),'TrNp',TrMax(Np),'j0red',j0red,'j1red',j1red))
                    if le0(N,j0red,j1red) and full_facts(N,j0red,j1red,Mp,shamt): full_ok+=1
                    elif len(full_fail)<6: full_fail.append((fmt(N),n,j0p,j1p,'j0red',j0red,'j1red',j1red,'shamt',shamt))
    print(f"#cases={tot} KMAX={KMAX}")
    print(f"  bound(j0red<j1red<=LN-1): {bound_ok}/{tot}")
    print(f"  TrEq: {treq_ok}/{tot}")
    for f in treq_fail: print("    TREQ-FAIL",f)
    print(f"  FULL facts: {full_ok}/{tot}")
    for f in full_fail: print("    FULL-FAIL",f)

if __name__=='__main__': main()
