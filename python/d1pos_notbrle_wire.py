#!/usr/bin/env python3
"""DEEP verification of the d0pos ¬brle ASSEMBLY wiring (descending_shift_append route).

Exact residual context (m_6_8_slice_Br_descending_monoT, d0pos jlarge):
  N monoT std, i1=1, M=oper(N,n), M'=seg M j0' j1' monoT, le0 M j0' j1', bge Lng N-1<=j1', ¬brle.
We verify the descending_shift_append-based assembly:
  Yp = seg M' (TrMax M'+1)(Lng M'-1)  (multiT since ¬brle & TrMax<end)
  c  = last FirstNodes(Yp) position (row-0 left-min anchor); Br M' = P(seg Yp 0 (c-1)) @ [tail]
  LOW source = seg M (a)(fnM-1)  -- a block-shifted copy of an N-side branch slice
  q  = (j0red-jm2) period index; Np = seg N j0red (Lng N-1); descending(Br Np) (IH)
  LOW = map(IncrFirst^^(q*delta)) (take J1 (Br Np)),  J1 = Lng(Br Np)-1
  tail = single comp;  descending_shift_append on Q=Br Np, PRE=LOW, TL=tail.
Check the HEAD facts the brick needs:
  lenPRE  : len LOW = Lng(Br Np)-1
  pre0/J  : entry(LOW!J)0 0 = entry(Br Np!J)0 0 + q*delta
  pre1/J  : entry(LOW!J)1 0 = entry(Br Np!J)1 0
  tl0     : entry tail 0 0  = entry(Br Np!(Lng-1))0 0 + q*delta
  tl1     : entry tail 1 0 <= entry(Br Np!(Lng-1))1 0
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
        if len(sys.argv) > 3 else (9, 4, 5)
    Ns = [N for N in gen_std(maxlen, maxval, KMAX) if is_d1pos_mono(N)]
    tot=0; fails=[]
    regA=0; regB=0
    for N in Ns:
        LN = Lng(N); jm2 = parent(N, 1, LN - 1); w = LN-1-jm2
        delta = entry(N,0,LN-1)-entry(N,0,jm2)
        for n in (1, 2, 3):
            M = oper(N, n)
            if Lng(M) < 2: continue
            for j0p in range(Lng(M)):
                for j1p in range(j0p + 1, Lng(M)):
                    if j1p < LN-1: continue          # bge
                    if not le0(M, j0p, j1p): continue
                    Mp = seg(M, j0p, j1p)
                    if not monoT(Mp): continue
                    if brle(Mp): continue            # ¬brle only
                    tot += 1
                    # --- assembly ---
                    t = TrMax(Mp)
                    Yp = seg(Mp, t+1, Lng(Mp)-1)
                    if not multiT(Yp):
                        fails.append(("Yp not multi", fmt(N),n,j0p,j1p)); continue
                    # anchor c = start index (within Yp) of the LAST P-component of Yp
                    PY = P(Yp)
                    c = IdxSum(PY)[len(PY)-1]
                    # split: P Yp = P(seg Yp 0 c-1) @ [seg Yp c end]
                    tail = seg(Yp, c, Lng(Yp)-1)
                    split = P(seg(Yp,0,c-1)) + [tail]
                    if P(Yp) != split:
                        fails.append(("P split", fmt(N),n,j0p,j1p,fmt(Yp),c)); continue
                    if c==0:
                        fails.append(("c=0", fmt(N),n,j0p,j1p,fmt(Yp))); continue
                    if not all(entry(Yp,0,c)<=entry(Yp,0,jj) for jj in range(c)):
                        fails.append(("lmin", fmt(N),n,j0p,j1p,fmt(Yp),c)); continue
                    if multiT(tail):
                        fails.append(("tail multi", fmt(N),n,j0p,j1p)); continue
                    # Br Mp = P Yp  (since TrMax<end)
                    BrMp = Br(Mp)
                    if BrMp != P(Yp):
                        fails.append(("BrMp!=PYp", fmt(N),n,j0p,j1p)); continue
                    LOW = P(seg(Yp,0,c-1))
                    # LOW source on M:  the absolute indices.
                    # Yp lives at M indices [j0p+t+1 .. j1p]; seg Yp 0 c-1 = M[j0p+t+1 .. j0p+t+c]
                    a = j0p + t + 1
                    fnM = j0p + t + 1 + c            # absolute first-node = LOW end +1
                    # LOW = P(seg M a (fnM-1))
                    if LOW != P(seg(M, a, fnM-1)):
                        fails.append(("LOW src", fmt(N),n,j0p,j1p)); continue
                    # period reduce: a is in block q
                    if a < jm2:
                        # regime A: a < jm2  (q=0 shift)
                        q = 0; j0red = a; regA+=1
                    else:
                        q = (a - jm2)//w; j0red = jm2 + (a-jm2)%w; regB+=1
                    Np = seg(N, j0red, LN-1)
                    BrNp = Br(Np)
                    if len(BrNp)==0:
                        fails.append(("BrNp empty", fmt(N),n,j0p,j1p)); continue
                    J1 = len(BrNp)-1
                    # check LOW = map(IncrFirst^^(q*delta))(take J1 BrNp)
                    shifted = [funpow(IncrFirst, q*delta, comp) for comp in BrNp[:J1]]
                    if LOW != shifted:
                        fails.append(("LOW!=shift(takeJ1 BrNp)", fmt(N),n,j0p,j1p,
                                      fmt(Np), q, J1, [fmt(x) for x in LOW], [fmt(x) for x in shifted])); continue
                    # lenPRE
                    if len(LOW) != len(BrNp)-1:
                        fails.append(("lenPRE", fmt(N),n,j0p,j1p)); continue
                    # head facts pre0/pre1
                    ok=True
                    for J in range(len(LOW)):
                        if entry(LOW[J],0,0) != entry(BrNp[J],0,0)+q*delta: ok=False; break
                        if entry(LOW[J],1,0) != entry(BrNp[J],1,0): ok=False; break
                    if not ok:
                        fails.append(("pre0/1", fmt(N),n,j0p,j1p)); continue
                    # tail facts tl0/tl1 against BrNp[J1] = BrNp[last]
                    last = BrNp[J1]
                    if entry(tail,0,0) != entry(last,0,0)+q*delta:
                        fails.append(("tl0", fmt(N),n,j0p,j1p, fmt(tail), fmt(last), q, delta)); continue
                    if not (entry(tail,1,0) <= entry(last,1,0)):
                        fails.append(("tl1", fmt(N),n,j0p,j1p, fmt(tail), fmt(last))); continue
    print(f"#d1pos-mono std={len(Ns)}  ¬brle-residual cases checked={tot}")
    print(f"  regimeA(a<jm2)={regA}  regimeB(a>=jm2)={regB}")
    if fails:
        print(f"  FAILURES={len(fails)}:")
        for f in fails[:20]: print("   ", f)
    else:
        print("  ALL assembly facts hold (lenPRE,pre0,pre1,tl0,tl1, LOW=shift(takeJ1 BrNp), P-split).")

if __name__ == '__main__':
    main()
