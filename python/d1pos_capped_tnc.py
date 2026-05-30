#!/usr/bin/env python3
"""For the CAPPED contrapositive residual: in d0pos notbrle cases (formula-G),
is TrMax M' <= c = j1red-1-j0red ?  (the in-block confinement the capped keystone
needs to start the agree/stop machinery).  Split by capped/uncapped.
Also report the contrapositive conclusion tnc: TrMax Np <= c."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, multiT, Br, is_standard, fmt, le0, nextR)
from d1pos_j0j1red_search import gen_std, is_d1pos_mono, brle

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (11, 5, 6)
    Ns = [N for N in gen_std(maxlen, maxval, KMAX) if is_d1pos_mono(N)]
    nb=0; cap=0; unc=0
    cap_tncM=0; cap_tncM_fail=[]
    cap_tncNp=0
    unc_tncM=0
    # ALSO: does the stop hold on Np side at TrMax Np? (needed for agree route)
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
                    if brle(Mp): continue
                    j0red=jm2+(j0p-jm2)%w if j0p>=jm2 else j0p
                    j1red=min(j0red+(j1p-j0p),LN-1)
                    if not (j0red<j1red<=LN-1): continue
                    Np=seg(N,j0red,j1red)
                    nb+=1
                    c=j1red-1-j0red
                    capped = (j1red != j0red+(j1p-j0p))
                    TrMp=TrMax(Mp); TrNp=TrMax(Np)
                    if capped:
                        cap+=1
                        if TrMp<=c: cap_tncM+=1
                        elif len(cap_tncM_fail)<8: cap_tncM_fail.append((fmt(N),n,j0p,j1p,'TrMp',TrMp,'c',c))
                        if TrNp<=c: cap_tncNp+=1
                    else:
                        unc+=1
                        if TrMp<=c: unc_tncM+=1
    print(f"#notbrle in-domain={nb} (capped={cap} uncapped={unc}) KMAX={KMAX}")
    print(f"  CAPPED  TrMax M' <= c : {cap_tncM}/{cap}")
    for f in cap_tncM_fail: print("    capM-FAIL",f)
    print(f"  CAPPED  TrMax Np <= c : {cap_tncNp}/{cap}")
    print(f"  UNCAP   TrMax M' <= c : {unc_tncM}/{unc}")

if __name__=='__main__': main()
