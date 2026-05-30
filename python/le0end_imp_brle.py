#!/usr/bin/env python3
"""GENERAL claim: for any monoT Mp in T_PS,  le0 Mp 0 (Lng Mp -1) ==> brle(Mp).
Test on ALL std slices (not just d1pos domain) and on raw std seqs, deep rank.
brle = TrMax==Lng-1 or le0 (TrMax+1)(Lng-1).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, multiT, Br, is_standard, fmt, le0)
from d1pos_j0j1red_search import gen_std

def brle(Mp):
    t=TrMax(Mp); return t==Lng(Mp)-1 or le0(Mp,t+1,Lng(Mp)-1)

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (11, 5, 6)
    Ns = gen_std(maxlen, maxval, KMAX)
    tot=0; ok=0; fail=[]
    # test on the sequences themselves AND on all their le0-slices
    seen=set()
    for N in Ns:
        cands=[N]
        # also slices
        for j0 in range(Lng(N)):
            for j1 in range(j0+1, Lng(N)):
                cands.append(seg(N,j0,j1))
        for Mp in cands:
            if Lng(Mp)<2: continue
            key=fmt(Mp)
            if key in seen: continue
            seen.add(key)
            if not monoT(Mp): continue
            if not le0(Mp,0,Lng(Mp)-1): continue
            tot+=1
            if brle(Mp): ok+=1
            elif len(fail)<10: fail.append((fmt(Mp),'TrMax',TrMax(Mp),'Lng-1',Lng(Mp)-1,
                                            'le0suf',le0(Mp,TrMax(Mp)+1,Lng(Mp)-1)))
    print(f"#monoT le0end seqs={tot} KMAX={KMAX}")
    print(f"  le0end => brle : {ok}/{tot}")
    for f in fail: print("   FAIL",f)

if __name__=='__main__': main()
