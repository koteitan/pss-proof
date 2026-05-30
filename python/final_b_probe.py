#!/usr/bin/env python3
"""Probe the structural relationship Br M' vs Br Np (free j1red) for the proof route.

For each ¬brle residual case, classify uncapped (j1red=j0red+(j1'-j0')) vs capped,
and check whether:
  (U)  Br M' = map(IncrFirst^^shamt)(Br Np)  ENTIRELY (uncapped)
  (C)  butlast(Br M') = map(IncrFirst^^shamt)(butlast(Br Np))  and tail relation
  also: relationship of the slice (j0'+T+1, j1') to block coords.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, multiT, Br, FirstNodes, IdxSum, IncrFirst, is_standard,
                       fmt, le0, funpow)

def gen_std(maxlen, maxval, KMAX):
    base = [[(j, j) for j in range(u, v + 1)] for u in range(maxval + 1)
            for v in range(u, maxval + 1)]
    store = {fmt(m): m for m in base}; frontier = list(base)
    for _ in range(KMAX):
        newf = []
        for M in frontier:
            for n in range(1, 4):
                Mp = oper(M, n); key = fmt(Mp)
                if Mp and len(Mp) <= maxlen and all(a <= maxval and b <= maxval for (a, b) in Mp) \
                        and key not in store:
                    store[key] = Mp; newf.append(Mp)
        frontier = newf
    return [m for m in store.values() if is_standard(m)]

def is_d1pos_mono(N):
    j1 = Lng(N) - 1
    return j1 >= 1 and monoT(N) and not (entry(N,0,j1)==0 and entry(N,1,j1)==0) \
           and idx1(N, j1) == 1 and hasParent(N, 1, j1)

def brle(Mp):
    t = TrMax(Mp)
    return t == Lng(Mp) - 1 or le0(Mp, t + 1, Lng(Mp) - 1)

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (12, 4, 8)
    Ns = [N for N in gen_std(maxlen, maxval, KMAX) if is_d1pos_mono(N)]
    tot=0; ncap=0; nunc=0
    fU=0; fC_pre=0
    treq=0; jge=0
    # also check: TrMax M' == TrMax Np (TrEq), and j0red < jm2 possibility
    j0red_lt_jm2=0
    for N in Ns:
        LN = Lng(N); jm2 = parent(N, 1, LN - 1); w = LN - 1 - jm2
        if w <= 0: continue
        delta = entry(N,0,LN-1) - entry(N,0,jm2)
        for n in (1, 2, 3):
            M = oper(N, n)
            if Lng(M) < 2: continue
            LM = Lng(M)
            for j0p in range(LM):
                for j1p in range(j0p + 1, LM):
                    if j1p < LN - 1: continue
                    if not le0(M, j0p, j1p): continue
                    Mp = seg(M, j0p, j1p)
                    if not monoT(Mp): continue
                    if brle(Mp): continue
                    tot += 1
                    if jm2 <= j0p:
                        q = (j0p - jm2)//w; j0red = jm2 + (j0p - jm2)%w
                    else:
                        q = 0; j0red = j0p
                    if j0red < jm2: j0red_lt_jm2 += 1
                    j1red = min(j0red + (j1p - j0p), LN - 1)
                    shamt = q*delta
                    BrMp = Br(Mp); Np = seg(N, j0red, j1red); BrNp = Br(Np)
                    T_Mp = TrMax(Mp); T_Np = TrMax(Np)
                    if T_Mp == T_Np: treq += 1
                    uncapped = (j0red + (j1p - j0p) <= LN - 1)
                    if uncapped:
                        nunc += 1
                        # whole shift
                        if BrMp != [funpow(IncrFirst, shamt, c) for c in BrNp]:
                            fU += 1
                    else:
                        ncap += 1
                        # butlast shift
                        if BrMp[:-1] != [funpow(IncrFirst, shamt, c) for c in BrNp[:-1]]:
                            fC_pre += 1
    print(f"#cases={tot}  uncapped={nunc} capped={ncap}")
    print(f"  TrEq(TrMax M'=TrMax Np)={treq}/{tot}")
    print(f"  j0red<jm2 (regime-A inside)={j0red_lt_jm2}")
    print(f"  uncapped: Br M' = shift(Br Np) ENTIRELY fails={fU}/{nunc}")
    print(f"  capped:   butlast Br M' = shift(butlast Br Np) fails={fC_pre}/{ncap}")

if __name__ == '__main__':
    main()
