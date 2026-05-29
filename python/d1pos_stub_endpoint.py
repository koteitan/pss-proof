#!/usr/bin/env python3
"""LINCHPIN #2: is the ¬brle stub FALSE with N-side endpoint = Lng N-1 (agent A, KMAX>=6),
and does the FREE-endpoint j1red fix it?

Residual context: N std monoT d1pos (i1=1, hasParent), M=oper(N,n), M'=seg M j0' j1' monoT,
le0 M j0' j1', bge (Lng N-1<=j1'), ¬brle. jm2=parent N 1 (Lng N-1), w=Lng N-1-jm2,
q=(j0'-jm2) div w, j0red=jm2+(j0'-jm2) mod w (regime B; A: j0'<jm2 => q=0, j0red=j0').
Check:
  (FIX0) Np_fixed = seg N j0red (Lng N-1): length(Br M') == Lng(Br Np_fixed) ?  (agent A: FALSE rank>=6)
  (FREE) EXISTS j1red, j0red<j1red<Lng N, le0 N j0red j1red, length(Br M')==Lng(Br(seg N j0red j1red)) ? (agent A: TRUE)
Also test the agent-A minimal witness directly.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, Br, is_standard, fmt, le0)

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

def witness(N, n, j0p, j1p):
    LN = Lng(N); jm2 = parent(N, 1, LN-1); w = LN-1-jm2
    if w <= 0: return None
    q = (j0p - jm2)//w if j0p >= jm2 else 0
    j0red = jm2 + ((j0p-jm2) % w) if j0p >= jm2 else j0p
    return jm2, w, q, j0red

def check(maxlen, maxval, KMAX):
    Ns = [N for N in gen_std(maxlen, maxval, KMAX) if is_d1pos_mono(N)]
    tot = fix0_ok = free_ok = 0
    fix0_fail_ex = []
    for N in Ns:
        LN = Lng(N)
        for n in (1,2,3):
            M = oper(N, n)
            if Lng(M) < 2: continue
            for j0p in range(Lng(M)):
                for j1p in range(j0p+1, Lng(M)):
                    if not le0(M, j0p, j1p): continue
                    Mp = seg(M, j0p, j1p)
                    if not monoT(Mp): continue
                    if j1p < LN-1: continue            # bge
                    if brle(Mp): continue              # ¬brle only
                    w = witness(N, n, j0p, j1p)
                    if w is None: continue
                    jm2, ww, q, j0red = w
                    if not (j0red < LN-1): continue
                    tot += 1
                    LbrM = len(Br(Mp))
                    # FIX0: endpoint Lng N-1
                    if le0(N, j0red, LN-1):
                        Npf = seg(N, j0red, LN-1)
                        if len(Br(Npf)) == LbrM:
                            fix0_ok += 1
                        elif len(fix0_fail_ex) < 5:
                            fix0_fail_ex.append((fmt(N), n, j0p, j1p, LbrM, len(Br(Npf))))
                    # FREE: exists j1red
                    found = False
                    for j1red in range(j0red+1, LN):
                        if le0(N, j0red, j1red) and len(Br(seg(N, j0red, j1red))) == LbrM:
                            found = True; break
                    if found: free_ok += 1
    print(f"[len{maxlen}/val{maxval}/KMAX{KMAX}] ¬brle residual witnesses={tot}")
    print(f"  (FIX0) length(Br M')==Lng(Br(seg N j0red (Lng N-1))): {fix0_ok}/{tot}")
    print(f"  (FREE) EXISTS j1red<Lng N with le0 & length match: {free_ok}/{tot}")
    if fix0_fail_ex: print("  FIX0 fails (LbrM vs LbrNp_fixed):", fix0_fail_ex)

if __name__ == '__main__':
    # agent-A minimal witness direct
    N=[(0,0),(1,1),(2,1),(2,1),(2,1)]
    print("minimal witness N=",fmt(N),"std=",is_standard(N),"d1pos_mono=",is_d1pos_mono(N))
    if is_d1pos_mono(N):
        M=oper(N,2); Mp=seg(M,4,7)
        jm2=parent(N,1,Lng(N)-1); w=Lng(N)-1-jm2; q=(4-jm2)//w; j0red=jm2+((4-jm2)%w)
        print(f"  M={fmt(M)} M'={fmt(Mp)} monoT={monoT(Mp)} le0M={le0(M,4,7)} ¬brle={not brle(Mp)}")
        print(f"  jm2={jm2} w={w} q={q} j0red={j0red} len(Br M')={len(Br(Mp))} "
              f"Lng(Br(seg N j0red {Lng(N)-1}))={len(Br(seg(N,j0red,Lng(N)-1)))}")
    a = sys.argv[1:] or ['10','4','6']
    check(int(a[0]), int(a[1]), int(a[2]))
