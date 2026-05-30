#!/usr/bin/env python3
"""TARGET (fill-A): in d0pos residual context with formula-G (j0red,j1red),
   TrMax(seg N j0red j1red) == Lng(seg N j0red j1red)-1   ==>   brle(M')
   ( "reference trunk fills => M' single-component (brle)" ).
EQUIVALENTLY contrapositive: not brle(M') ==> TrMax(Np) < Lng(Np)-1 (tnc strict).
Domain = the keystone-invocation domain: N std d1pos mono, M=N[n] (n>=1),
M'=seg M j0' j1' monoT, le0 M j0' j1', j1' >= LN-1, j0'<j1'<Lng M.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, multiT, Br, is_standard, fmt, le0)
from d1pos_j0j1red_search import gen_std, is_d1pos_mono, brle

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (10, 4, 6)
    Ns = [N for N in gen_std(maxlen, maxval, KMAX) if is_d1pos_mono(N)]
    tot=0; impl_ok=0; impl_fail=[]
    contra_ok=0; contra_fail=[]
    fills=0; nofills=0
    for N in Ns:
        LN = Lng(N); jm2 = parent(N, 1, LN-1); w = LN-1-jm2
        if w<=0: continue
        for n in (1,2,3):
            M = oper(N, n)
            if Lng(M) < 2: continue
            for j0p in range(Lng(M)):
                for j1p in range(j0p+1, Lng(M)):
                    if j1p < LN-1: continue
                    if not le0(M, j0p, j1p): continue
                    Mp = seg(M, j0p, j1p)
                    if not monoT(Mp): continue
                    tot += 1
                    j0red=jm2+(j0p-jm2)%w if j0p>=jm2 else j0p
                    j1red=min(j0red+(j1p-j0p),LN-1)
                    if not (j0red<j1red<=LN-1):
                        # out of formula domain; skip (should not gate the lemma)
                        continue
                    Np=seg(N,j0red,j1red)
                    trunkfills = (TrMax(Np)==Lng(Np)-1)
                    b = brle(Mp)
                    if trunkfills: fills+=1
                    else: nofills+=1
                    # forward implication: trunkfills => brle
                    if (not trunkfills) or b: impl_ok+=1
                    elif len(impl_fail)<8: impl_fail.append((fmt(N),n,j0p,j1p,'TrNp',TrMax(Np),'LNp-1',Lng(Np)-1,'brle',b))
                    # contrapositive: not brle => not trunkfills (TrMax Np < Lng Np -1)
                    if b or (not trunkfills): contra_ok+=1
                    elif len(contra_fail)<8: contra_fail.append((fmt(N),n,j0p,j1p,'TrNp',TrMax(Np),'LNp-1',Lng(Np)-1))
    print(f"#cases(in-domain)={tot} KMAX={KMAX} len<={maxlen} val<={maxval}")
    print(f"  trunkfills={fills}  not-fills={nofills}")
    print(f"  IMPLICATION (trunkfills => brle): {impl_ok}/{impl_ok+len(impl_fail)}")
    for f in impl_fail: print("    IMPL-FAIL",f)
    print(f"  CONTRAPOSITIVE (not brle => TrMax Np < LNp-1): {contra_ok}/{contra_ok+len(contra_fail)}")
    for f in contra_fail: print("    CONTRA-FAIL",f)

if __name__=='__main__': main()
