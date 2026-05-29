#!/usr/bin/env python3
"""Pin the d0pos ¬brle LOW take-identity in the EXACT residual context.

Target lemma oper_d1pos_notbrle_LOW_take_eq:
  LOW = P(seg Yp 0 (c-1)) = map (IncrFirst^^(q*delta)) (take J1 (Br Np))
where (d0pos i1=1, residual context, regime B  jm2 <= j0'):
  N monoT std, M=oper(N,n) n>=1, idx1 N (Lng N-1)=1, hasParent N 1 (Lng N-1),
  jm2=parent N 1 (Lng N-1), w=Lng N-1-jm2, delta=entry N 0(Lng N-1)-entry N 0 jm2>0,
  M'=seg M j0' j1' monoT, le0 M j0' j1', bge: Lng N-1 <= j1', NOT brle, jm2<=j0',
  q=(j0'-jm2) div w, j0red=jm2+(j0'-jm2) mod w, Np=seg N j0red (Lng N-1),
  J1=Lng(Br Np)-1,
  Yp=seg M' (TrMax M'+1)(Lng M'-1), c=FirstNodes(M')!J1 - (TrMax M'+1),
  LOW=P(seg Yp 0 (c-1)).

Also pin sub-identities (for the proof skeleton):
  (i)   c = (FirstNodes(M')!J1) - (TrMax M'+1)   [in Yp-coords]
  (ii)  seg Yp 0 (c-1) = seg M' (TrMax M'+1) (FirstNodes(M')!J1 - 1)
  (iii) the N-side: take J1 (Br Np) = P(seg N (jm2+s0)(jm2+e0)) for the right s0,e0
        with s0 = TrMax(Np)+1 - ??? -- we directly check the take-eq.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, Br, FirstNodes, IncrFirst, funpow, is_standard, fmt, le0)

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
        if len(sys.argv) > 3 else (8, 3, 5)
    Ns = gen_std(maxlen, maxval, KMAX)
    d1 = [N for N in Ns if is_d1pos_mono(N)]
    n_resid_nb = 0
    fail_take = 0; tot_take = 0
    fail_ii = 0; tot_ii = 0
    fail_lowsrc = 0; tot_lowsrc = 0
    ex_fail = []
    for N in d1:
        LN = Lng(N); jm2 = parent(N, 1, LN - 1); w = LN - 1 - jm2
        if w <= 0: continue
        delta = entry(N,0,LN-1) - entry(N,0,jm2)
        if delta <= 0: continue
        for n in (1, 2, 3):
            M = oper(N, n)
            if Lng(M) < 2: continue
            LM = Lng(M)
            for j0p in range(LM):
                for j1p in range(j0p + 1, LM):
                    if not le0(M, j0p, j1p): continue
                    Mp = seg(M, j0p, j1p)
                    if not monoT(Mp): continue
                    if j1p < LN - 1: continue       # bge
                    if brle(Mp): continue           # ¬brle only
                    if j0p < jm2: continue          # regime B
                    n_resid_nb += 1
                    q = (j0p - jm2) // w
                    j0red = jm2 + (j0p - jm2) % w
                    if j0red >= LN: continue
                    Np = seg(N, j0red, LN - 1)
                    if Lng(Np) < 1: continue
                    brNp = Br(Np)
                    J1 = Lng(brNp) - 1
                    if J1 < 0: continue
                    fn = FirstNodes(Mp)
                    if J1 >= len(fn): continue
                    trMp = TrMax(Mp)
                    Yp = seg(Mp, trMp + 1, Lng(Mp) - 1)
                    c = fn[J1] - (trMp + 1)         # anchor in Yp-coords
                    if c < 1: continue
                    if c - 1 > Lng(Yp) - 1: continue
                    LOW = P(seg(Yp, 0, c - 1))
                    # (ii): seg Yp 0 (c-1) = seg Mp (TrMax+1) (fn[J1]-1)
                    tot_ii += 1
                    lhs_ii = seg(Yp, 0, c - 1)
                    rhs_ii = seg(Mp, trMp + 1, fn[J1] - 1)
                    if lhs_ii != rhs_ii:
                        fail_ii += 1
                    # TARGET take-eq
                    tot_take += 1
                    rhs = [funpow(IncrFirst, q * delta, comp) for comp in brNp[:J1]]
                    if LOW != rhs:
                        fail_take += 1
                        if len(ex_fail) < 6:
                            ex_fail.append((fmt(N), n, j0p, j1p, q, j0red,
                                            "LOW="+str([fmt(c2) for c2 in LOW]),
                                            "rhs="+str([fmt(c2) for c2 in rhs])))
    print(f"#d1pos-mono std = {len(d1)}")
    print(f"residual ¬brle regime-B slices = {n_resid_nb}")
    print(f"(ii) seg-Yp = seg-Mp endpoint reshape: {tot_ii-fail_ii}/{tot_ii}")
    print(f"TARGET take-eq  LOW = map(IncrFirst^q*delta)(take J1 (Br Np)): {tot_take-fail_take}/{tot_take}")
    if fail_take:
        for e in ex_fail: print("  FAIL", e)

if __name__ == '__main__':
    main()
