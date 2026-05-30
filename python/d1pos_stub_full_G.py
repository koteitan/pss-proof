#!/usr/bin/env python3
"""DEEP verify the EXACT existential of oper_d1pos_notbrle_LOW_take_eq using
formula-G witnesses (free j1red = min cap).  Tests the FULL fact set the
existential claims, in the EXACT stub context (NOT the capped take-check).

Stub context: N monoT std, i1=1, hasParent N 1 (Lng N-1), M=oper(N,n) n>=1,
  M'=seg M j0' j1' in T_PS, le0 M j0' j1', j0'<j1', j1'<Lng M, Lng N-1<=j1', NOT brle.
Formula G:
  jm2=parent N 1 (Lng N-1), w=Lng N-1-jm2, delta=entry N 0(Lng N-1)-entry N 0 jm2,
  q   = (j0'-jm2)//w   if jm2<=j0' else 0
  j0red = jm2+(j0'-jm2)%w if jm2<=j0' else j0'
  j1red = min(j0red+(j1'-j0'))(Lng N-1)
  shamt = q*delta,  LOW=butlast(Br M'),  tail=last(Br M').
Existential facts (the shows):
  F1 j0red<j1red
  F2 j1red<=Lng N-1
  F3 le0 N j0red j1red
  F4 Br M' = LOW@[tail]      (i.e. Br M' nonempty -> always true by construction)
  F5 Br Np != []     (Np=seg N j0red j1red)
  F6 len LOW = Lng(Br Np)-1
  F7 forall J<len LOW: entry(LOW!J)0 0 = entry(Br Np!J)0 0 + shamt
                       entry(LOW!J)1 0 = entry(Br Np!J)1 0
  F8 entry tail 0 0 = entry(Br Np!(Lng(Br Np)-1))0 0 + shamt
  F9 entry tail 1 0 <= entry(Br Np!(Lng(Br Np)-1))1 0
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
        if len(sys.argv) > 3 else (12, 4, 8)
    Ns = gen_std(maxlen, maxval, KMAX)
    d1 = [N for N in Ns if is_d1pos_mono(N)]
    n_resid = 0
    F = {k: [0,0] for k in ['F1','F2','F3','F5','F6','F7','F8','F9']}
    ex = {k: [] for k in F}
    def chk(key, cond, info):
        F[key][1]+=1
        if cond: F[key][0]+=1
        elif len(ex[key])<4: ex[key].append(info)
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
                    n_resid += 1
                    # formula G
                    if jm2 <= j0p:
                        q = (j0p - jm2)//w
                        j0red = jm2 + (j0p - jm2)%w
                    else:
                        q = 0
                        j0red = j0p
                    j1red = min(j0red + (j1p - j0p), LN - 1)
                    shamt = q*delta
                    Np = seg(N, j0red, j1red)
                    brM = Br(Mp); brNp = Br(Np)
                    info = (fmt(N), n, j0p, j1p, q, j0red, j1red)
                    chk('F1', j0red < j1red, info)
                    chk('F2', j1red <= LN - 1, info)
                    chk('F3', le0(N, j0red, j1red), info)
                    chk('F5', len(brNp) != 0, info)
                    if len(brM)==0:
                        # F4 fails: cannot split
                        continue
                    LOW = brM[:-1]; tail = brM[-1]
                    chk('F6', len(LOW) == Lng(brNp) - 1, info+("lenLOW=%d lenBrNp=%d"%(len(LOW),len(brNp)),))
                    if len(brNp)>=1:
                        ok7 = True
                        for J in range(len(LOW)):
                            if J >= len(brNp): ok7=False; break
                            if entry(LOW[J],0,0) != entry(brNp[J],0,0)+shamt: ok7=False; break
                            if entry(LOW[J],1,0) != entry(brNp[J],1,0): ok7=False; break
                        chk('F7', ok7, info+("LOW="+str([fmt(c) for c in LOW]),)+("brNp="+str([fmt(c) for c in brNp]),))
                        last = Lng(brNp)-1
                        chk('F8', entry(tail,0,0) == entry(brNp[last],0,0)+shamt,
                            info+("tail="+fmt(tail),"brNplast="+fmt(brNp[last])))
                        chk('F9', entry(tail,1,0) <= entry(brNp[last],1,0), info)
    print(f"#d1pos-mono std = {len(d1)}, residual ¬brle slices = {n_resid}")
    for k in ['F1','F2','F3','F5','F6','F7','F8','F9']:
        ok,tot = F[k]
        print(f"  {k}: {ok}/{tot}" + ("  *** FAIL" if ok<tot else ""))
        if ok<tot:
            for e in ex[k]: print("     ", e)

if __name__ == '__main__':
    main()
