#!/usr/bin/env python3
"""Discover the (j0red,j1red) pair structure for the d0pos ¬brle FREE stub.
For each residual case, enumerate ALL (j0red,j1red) with j0red<j1red<=LN-1, le0 N,
and Lng(Br(seg N j0red j1red))==len(Br M').  Print, per case, the candidate pairs
together with M-side quantities (jm2,w,a,j0',j1',c,t) to spot the closed form.
Also report the FULL fact set (pre0/pre1/tl0/tl1) for each matching pair to see
which pairs additionally satisfy the row-shift facts (the real witness).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, multiT, Br, IdxSum, IncrFirst, is_standard, fmt, le0, funpow)

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

def full_facts(N,j0red,j1red,Mp,shamt):
    """check pre0/pre1/tl0/tl1 with LOW=butlast(Br Mp), tail=last(Br Mp)."""
    Np=seg(N,j0red,j1red); BrNp=Br(Np)
    if len(BrNp)==0: return False
    BrM=Br(Mp); LOW=BrM[:-1]; tail=BrM[-1]
    if len(LOW)!=len(BrNp)-1: return False
    for J in range(len(LOW)):
        if entry(LOW[J],0,0)!=entry(BrNp[J],0,0)+shamt: return False
        if entry(LOW[J],1,0)!=entry(BrNp[J],1,0): return False
    last=BrNp[len(BrNp)-1]
    if entry(tail,0,0)!=entry(last,0,0)+shamt: return False
    if not (entry(tail,1,0)<=entry(last,1,0)): return False
    return True

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (10, 4, 6)
    Ns = [N for N in gen_std(maxlen, maxval, KMAX) if is_d1pos_mono(N)]
    tot=0; have_full=0; nofull=[]
    rows=[]
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
                    t=TrMax(Mp); a=j0p+t+1; LbrM=len(Br(Mp))
                    if a<jm2: qa=0; j0r_w=a
                    else: qa=(a-jm2)//w; j0r_w=jm2+(a-jm2)%w
                    shamt=qa*delta
                    # enumerate matching pairs with full facts
                    fullpairs=[]
                    for j0red in range(0,LN-1):
                        for j1red in range(j0red+1,LN):
                            if not le0(N,j0red,j1red): continue
                            if len(Br(seg(N,j0red,j1red)))!=LbrM: continue
                            if full_facts(N,j0red,j1red,Mp,shamt):
                                fullpairs.append((j0red,j1red))
                    if fullpairs:
                        have_full+=1
                        rows.append((LN,jm2,w,n,j0p,j1p,t,a,j0r_w,qa,LbrM,fullpairs))
                    else:
                        nofull.append((fmt(N),n,j0p,j1p,'shamt',shamt,'LbrM',LbrM))
    print(f"#cases={tot}  have_full_witness={have_full}  no_full={len(nofull)}")
    if nofull:
        print("NO-FULL examples:")
        for f in nofull[:8]: print("  ",f)
    # Now: for cases WITH full witness, look at the relation of the chosen pair.
    # try formula: j0red = j0r_w (period-reduce a); j1red = ? . Print the j1red options.
    print("\n--- full-witness rows (LN,jm2,w,n,j0p,j1p,t,a,j0r_w,qa,LbrM,fullpairs) ---")
    mism=0
    for r in rows[:40]:
        print("  ",r)
    # check: does j0r_w appear as a j0red in some fullpair, and what is j1red then?
    print("\n--- testing j0red=j0r_w; collect j1red when j0red matches ---")
    formula_ok=0; formula_fail=[]
    for (LN,jm2,w,n,j0p,j1p,t,a,j0r_w,qa,LbrM,fullpairs) in rows:
        js=[jr for (j0r,jr) in fullpairs if j0r==j0r_w]
        if js:
            formula_ok+=1
        else:
            formula_fail.append((LN,jm2,w,n,j0p,j1p,a,j0r_w,fullpairs))
    print(f"  j0red=j0r_w has a full witness: {formula_ok}/{len(rows)}")
    for f in formula_fail[:10]: print("    FAIL",f)

if __name__=='__main__':
    main()
