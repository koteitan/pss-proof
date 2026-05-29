#!/usr/bin/env python3
"""Verify the FULL d1pos ¬brle regime-B descending assembly the Isabelle proof will build.

For each standard d1pos N (rank-stratified), M=oper(N,n), monoT slice M'=seg M j0' j1'
with leR M 0 j0' j1', nonempty Br, ¬brle (multi).  All such are regime B (j0'>=jm2).
Period-reduce j0' into [jm2, j1N):  j0r = jm2 + ((j0'-jm2) mod w).  Set Np=seg N j0r (LN-1).
Then verify, for the proof:
  (a) Np monoT, Br Np nonempty, descending (Br Np) [IH]
  (b) Br M' = (Br Np)[0..J1-1] @ [tail],  J1=len(Br Np)-1, tail single comp
  (c) junction (last prefix = Br Np!(J1-1)) cdom tail:
       tail head row0 = Mp_{0,0 of tail} = M_{0,j1'}? NO -- tail head is at fnM.
     Actually mirror d0zero: tail = seg M fnM j1', tail head row0 = entry M 0 fnM,
     prefix-last = Br Np!(J1-1).  The KEY junction is between Br Np!(J1-1) and Br Np!J1,
     and tail head = (Br Np!J1) head shifted.  Report the head equalities the proof uses:
       entry tail 0 0 (=entry M 0 fnM)  vs  entry (Br Np!J1) 0 0 (+ k*delta?)
       entry tail 1 0 (=entry M 1 fnM)  vs  entry (Br Np!J1) 1 0
Report sub-case split on j1' vs j1N.
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

def is_d1pos(N):
    j1 = Lng(N) - 1
    return j1 >= 1 and not (entry(N,0,j1)==0 and entry(N,1,j1)==0) \
           and idx1(N, j1) == 1 and hasParent(N, 1, j1)

def descending(comps):
    # cdom adjacent: c0-head row0 of right <= left, and tie => row1 right<=left
    def cdom(L,R):
        l0,l1=L[0]; r0,r1=R[0]
        if r0> l0: return False
        if r0==l0 and r1> l1: return False
        return True
    return all(cdom(comps[i],comps[i+1]) for i in range(len(comps)-1))

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (7, 3, 4)
    Ns = gen_std(maxlen, maxval, KMAX)
    d1 = [N for N in Ns if is_d1pos(N)]
    nb=0; npmono=0; fold_ok=0; junc_ok=0
    sub_j1lt=0; sub_j1ge=0
    tail_single=0; desc_all=0
    bad=[]
    for N in d1:
        LN=Lng(N); j1N=LN-1; jm2=parent(N,1,j1N); w=j1N-jm2
        delta=entry(N,0,j1N)-entry(N,0,jm2)
        for n in (1,2,3):
            M=oper(N,n)
            if Lng(M)<2: continue
            for j0p in range(Lng(M)):
                for j1p in range(j0p+1,Lng(M)):
                    if not le0(M,j0p,j1p): continue
                    Mp=seg(M,j0p,j1p)
                    if not monoT(Mp): continue
                    t=TrMax(Mp)
                    if t==Lng(Mp)-1: continue
                    if le0(Mp,t+1,Lng(Mp)-1): continue
                    BrMp=Br(Mp)
                    if len(BrMp)<2: continue
                    nb+=1
                    # period reduce
                    assert j0p>=jm2, ("regimeA!", fmt(N),n,j0p,j1p)
                    j0r=jm2+((j0p-jm2)%w)
                    Np=seg(N,j0r,LN-1)
                    if not (monoT(Np) and Br(Np)):
                        bad.append(('npmono',fmt(N),n,j0p,j1p,j0r,fmt(Np)))
                        continue
                    npmono+=1
                    BrNp=Br(Np)
                    if not descending(BrNp):
                        bad.append(('descNp',fmt(N),n,j0p,j1p)); continue
                    desc_all+=1
                    J1=len(BrNp)-1
                    # fold: BrMp prefix == BrNp[:J1], tail = BrMp[-1]
                    if [fmt(c) for c in BrMp[:-1]]==[fmt(c) for c in BrNp[:J1]]:
                        fold_ok+=1
                    else:
                        bad.append(('fold',fmt(N),n,j0p,j1p,[fmt(c) for c in BrMp],[fmt(c) for c in BrNp]))
                        continue
                    tail=BrMp[-1]
                    if len(P(tail))==1: tail_single+=1
                    else: bad.append(('tailmulti',fmt(N),n,j0p,j1p,fmt(tail)))
                    # junction: tail head vs BrNp[J1] head
                    hM=tail[0]; hC=BrNp[J1][0]
                    # proof: row0 hM[0] == hC[0] (+? shift); row1 hM[1] < hC[1] (drop) OR <=
                    r0tie = (hM[0]==hC[0])
                    r1drop = (hM[1] <= hC[1])
                    if r0tie and r1drop: junc_ok+=1
                    else: bad.append(('junc',fmt(N),n,j0p,j1p,hM,hC))
                    # subcase
                    if j1p< j0p+ (j1N-jm2):  # rough; track j1' vs j1N in M-coords block0
                        pass
                    if j1p < (jm2 + w):  # j1' < j1N within first block? track
                        sub_j1lt+=1
                    else:
                        sub_j1ge+=1
    print(f"#d1pos={len(d1)}  ¬brle multi={nb}")
    print(f"  Np(period-reduced) monoT & Br nonempty: {npmono}/{nb}")
    print(f"  descending(Br Np): {desc_all}/{npmono}")
    print(f"  fold Br M'[:-1]==Br Np[:J1]: {fold_ok}/{desc_all}")
    print(f"  tail single P-comp: {tail_single}/{fold_ok}")
    print(f"  junction r0-tie & r1-drop: {junc_ok}/{fold_ok}")
    if bad: print("  BAD (first 8):"); [print("   ",b) for b in bad[:8]]
    else: print("  ALL CONSISTENT")

if __name__=='__main__':
    main()
