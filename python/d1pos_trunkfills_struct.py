#!/usr/bin/env python3
"""Structural probe of the trunkfills => brle cases.
In trunkfills (TrMax Np == Lng Np -1) cases, report:
  c = j1red-1-j0red, TrMax Mp, Lng Mp -1, capped?, which disjunct, and
  whether TrMax Mp == c+1 (== TrMax Np == Lng Np -1) always, and
  in capped cases whether le0 Mp (TrMax Mp +1) (Lng Mp -1).
Also: is the uncapped trunkfills case exactly TrMax Mp == Lng Mp -1?
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, multiT, Br, is_standard, fmt, le0)
from d1pos_j0j1red_search import gen_std, is_d1pos_mono, brle

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (11, 5, 6)
    Ns = [N for N in gen_std(maxlen, maxval, KMAX) if is_d1pos_mono(N)]
    tot=0
    a_TrMp_eq_c1=0; a_fail=[]               # TrMax Mp == c+1 ?
    unc_disj1=0; unc_fail=[]                # uncapped => TrMax Mp == Lng Mp -1
    cap_disj2=0; cap_fail=[]                # capped => le0 Mp (TrMax Mp+1)(Lng Mp -1)
    n_unc=0; n_cap=0
    # extra: TrMax Mp >= c always? and trunk of Mp reaches c?
    trmp_ge_c=0
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
                    j0red=jm2+(j0p-jm2)%w if j0p>=jm2 else j0p
                    j1red=min(j0red+(j1p-j0p),LN-1)
                    if not (j0red<j1red<=LN-1): continue
                    Np=seg(N,j0red,j1red)
                    if TrMax(Np)!=Lng(Np)-1: continue  # only trunkfills
                    tot+=1
                    c=j1red-1-j0red
                    capped = (j1red != j0red+(j1p-j0p))
                    TrMp=TrMax(Mp); LMp1=Lng(Mp)-1
                    if TrMp>=c: trmp_ge_c+=1
                    if TrMp==c+1: a_TrMp_eq_c1+=1
                    elif len(a_fail)<6: a_fail.append((fmt(N),n,j0p,j1p,'TrMp',TrMp,'c+1',c+1,'cap',capped))
                    if capped:
                        n_cap+=1
                        if le0(Mp,TrMp+1,LMp1): cap_disj2+=1
                        elif len(cap_fail)<6: cap_fail.append((fmt(N),n,j0p,j1p,'TrMp',TrMp,'LMp1',LMp1))
                    else:
                        n_unc+=1
                        if TrMp==LMp1: unc_disj1+=1
                        elif len(unc_fail)<6: unc_fail.append((fmt(N),n,j0p,j1p,'TrMp',TrMp,'LMp1',LMp1))
    print(f"#trunkfills cases={tot} KMAX={KMAX} (uncapped={n_unc} capped={n_cap})")
    print(f"  TrMax Mp >= c : {trmp_ge_c}/{tot}")
    print(f"  TrMax Mp == c+1 (==TrMax Np): {a_TrMp_eq_c1}/{tot}")
    for f in a_fail: print("    AeqFAIL",f)
    print(f"  UNCAPPED disj1 (TrMax Mp == Lng Mp -1): {unc_disj1}/{n_unc}")
    for f in unc_fail: print("    UNCfail",f)
    print(f"  CAPPED disj2 (le0 Mp (TrMp+1)(LMp-1)): {cap_disj2}/{n_cap}")
    for f in cap_fail: print("    CAPfail",f)

if __name__=='__main__': main()
