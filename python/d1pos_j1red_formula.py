#!/usr/bin/env python3
"""Find a CLOSED FORM for the free N-side endpoint j1red in the d0pos ¬brle stub.

Context exactly as the stub: N std monoT d1pos (i1=1, hasParent), M=oper(N,n),
M'=seg M j0' j1' monoT, le0 M j0' j1', bge (Lng N-1<=j1'), ¬brle.
LOW source on M: Yp = seg M' (t+1)(Lng M'-1), t=TrMax M', absolute M-indices [a..j1'], a=j0'+t+1.
first node fnM = a+c. LOW = P(seg M a (fnM-1)).  j0red = period-reduce(a).
We want j1red with: j0red<j1red<Lng N, le0 N j0red j1red, Lng(Br(seg N j0red j1red))=len(Br M').

Test candidate j1red formulas and report which (if any) is universally correct at rank>=6.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, multiT, Br, IdxSum, is_standard, fmt, le0)

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
    t = TrMax(Mp); return t == Lng(Mp)-1 or le0(Mp, t+1, Lng(Mp)-1)

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (10, 4, 6)
    Ns = [N for N in gen_std(maxlen, maxval, KMAX) if is_d1pos_mono(N)]
    tot=0
    # candidates keyed by name -> count ok
    cand_ok = {}
    cand_fail = {}
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
                    t = TrMax(Mp)
                    a = j0p + t + 1
                    # j0red
                    if a < jm2:
                        j0red = a
                    else:
                        j0red = jm2 + (a-jm2)%w
                    if not (j0red < LN-1): continue
                    LbrM = len(Br(Mp))
                    tot += 1
                    # candidate j1red formulas:
                    cands = {}
                    # C1: period reduce j1' : jm2 + (j1'-jm2) mod w  (if >=jm2)
                    if j1p >= jm2:
                        cands['C1_perred_j1p'] = jm2 + (j1p-jm2)%w
                    # C2: j0red + (number-of-blocks * something) -> just j0red + (LbrM)  no
                    # C3: smallest j1red>j0red with matching Br length AND le0  (the existence one)
                    # C4: j0red + (j1p - a)  i.e. shift the M-range width back to N
                    cands['C4_j0red_plus_width'] = j0red + (j1p - a)
                    # C5: reduce the right end as period of (a + (j1p-a)) but in N coords:
                    #     i.e. j0red + ((j1p - a) mod w)
                    cands['C5_j0red_plus_width_mod_w'] = j0red + ((j1p-a)%w)
                    # C6: jm2 + (j1p - jm2) mod w but if result <= j0red, add w
                    if j1p>=jm2:
                        r = jm2 + (j1p-jm2)%w
                        cands['C6_perred_j1p_bumped'] = r if r>j0red else r+w
                    for name,jr in cands.items():
                        cand_ok.setdefault(name,0); cand_fail.setdefault(name,[])
                        ok = (j0red < jr <= LN-1 and le0(N,j0red,jr)
                              and len(Br(seg(N,j0red,jr)))==LbrM)
                        if ok: cand_ok[name]+=1
                        elif len(cand_fail[name])<4:
                            cand_fail[name].append((fmt(N),n,j0p,j1p,'jr=',jr,'j0red=',j0red,
                                                    'LbrM=',LbrM,'got=',
                                                    len(Br(seg(N,j0red,jr))) if j0red<jr<=LN-1 else 'oob'))
    print(f"#cases={tot}  (rank KMAX={KMAX})")
    for name in cand_ok:
        print(f"  {name}: {cand_ok[name]}/{tot}")
        if cand_fail[name]:
            for f in cand_fail[name][:3]: print("      FAIL", f)

if __name__=='__main__':
    main()
