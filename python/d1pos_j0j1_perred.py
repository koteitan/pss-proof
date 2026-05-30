#!/usr/bin/env python3
"""Test j0red/j1red as period-reductions of j0'/j1' (NOT of a)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, multiT, Br, IdxSum, IncrFirst, is_standard, fmt, le0, funpow)
from d1pos_j0j1red_search import gen_std, is_d1pos_mono, brle, full_facts

def perred(x,jm2,w):
    if x<jm2: return x,0
    return jm2+(x-jm2)%w, (x-jm2)//w

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (10, 4, 6)
    Ns = [N for N in gen_std(maxlen, maxval, KMAX) if is_d1pos_mono(N)]
    tot=0
    # several full-pair-formula candidates
    names=['F_j0red=perred(j0p),j1red=perred(j0p)+(j1p-j0p)',
           'G_j0red=perred(j0p),j1red=min(perred(j0p)+(j1p-j0p),LN-1)',
           'H_j0red=perred(j0p),j1red=perred(j0p)+(j1p-j0p) capped via mod']
    ok={k:0 for k in names}; fail={k:[] for k in names}
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
                    j0red,q0=perred(j0p,jm2,w)
                    shamt=q0*delta
                    width=j1p-j0p
                    cands={
                      names[0]:(j0red, j0red+width),
                      names[1]:(j0red, min(j0red+width,LN-1)),
                      names[2]:(j0red, j0red+(width if j0red+width<=LN-1 else (width%w if (j0red+width%w)>j0red else width%w))),
                    }
                    for k,(j0r,j1r) in cands.items():
                        good=(0<=j0r<j1r<=LN-1 and le0(N,j0r,j1r)
                              and full_facts(N,j0r,j1r,Mp,shamt))
                        if good: ok[k]+=1
                        elif len(fail[k])<3:
                            fail[k].append((fmt(N),n,j0p,j1p,'j0r',j0r,'j1r',j1r,'shamt',shamt))
    print(f"#cases={tot} KMAX={KMAX}")
    for k in names:
        print(f"  {k}: {ok[k]}/{tot}")
        for f in fail[k][:2]: print("     ",f)

if __name__=='__main__': main()
