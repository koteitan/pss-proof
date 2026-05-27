"""Empirical audit for the §6.8 d0zero case-A standalone TrMax-equality lemma.

Context (worktree pss_mechanized.thy ~9203, d0zero, lt0): M = N[n], N standard
(monoT), entry N 1 (Lng N-1) = 0, idx1 N (Lng N-1)=0, j0N=parent N 0 (Lng N-1),
w=Lng N-1-j0N, j0' < j0N < j1', leR M 0 j0' j1' (le0 M j0' j1').

Claim 1 (TrMax-equality): TrMax (seg M j0' j1') = TrMax (seg N j0' (Lng N - 1)).
Claim 2 (row-1 boundary inequality):
    entry N 1 j0N <= entry N 1 (Lng N - 2).
Run: python3 slice_trmaxeq_audit.py
"""
from red_model import (oper, diagSeq, seg, Br, le0, monoT, Lng, entry, TrMax,
                       idx1, hasParent, parent)
def tup(M): return tuple(M)

UB=5; NMAX=4; KMAX=4
S=[set([tup(diagSeq(u,v)) for u in range(UB+1) for v in range(u,UB+1)])]
for k in range(1,KMAX+1):
    Sk=set()
    for M in S[k-1]:
        for n in range(1,NMAX+1):
            try: Sk.add(tup(oper(list(M),n)))
            except Exception: pass
    S.append(Sk)
ST=set().union(*S)

tot=0
c1_ok=c1_bad=0
c2_ok=c2_bad=0
c1_bad_ex=[]; c2_bad_ex=[]
for Nt in ST:
    N=list(Nt); LN=Lng(N)
    if LN<=1: continue
    if not monoT(N): continue
    j1N=LN-1
    if entry(N,1,j1N)!=0: continue   # d0zero
    if idx1(N,j1N)!=0: continue
    if not hasParent(N,0,j1N): continue
    j0N=parent(N,0,j1N)
    if j0N is None or not (j0N<j1N): continue
    w=j1N-j0N
    for n in range(2,NMAX+1):   # n>1 (jlarge needs blocks)
        M=oper(N,n)
        LM=Lng(M)
        if LM != j0N + n*w: continue  # generic d0zero layout
        for j0p in range(0,j0N):        # j0' < j0N
            for j1p in range(j0N+1,LM):  # j0N < j1'
                if not le0(M,j0p,j1p): continue  # leR M 0 j0' j1'
                if j1p > LM-1: continue
                tot+=1
                # Claim 1
                lhs=TrMax(seg(M,j0p,j1p))
                rhs=TrMax(seg(N,j0p,j1N))
                if lhs==rhs: c1_ok+=1
                else:
                    c1_bad+=1
                    if len(c1_bad_ex)<5:
                        c1_bad_ex.append((N,n,j0p,j1p,lhs,rhs))
    # Claim 2 (depends only on N)
    if j1N>=1:
        if entry(N,1,j0N) <= entry(N,1,LN-2):
            c2_ok+=1
        else:
            c2_bad+=1
            if len(c2_bad_ex)<5:
                c2_bad_ex.append((N,j0N,entry(N,1,j0N),entry(N,1,LN-2)))

print(f"qualifying (N,n,j0',j1') case-A contexts: {tot}")
print(f"Claim1 TrMax(seg M j0' j1')=TrMax(seg N j0' (LngN-1)): ok={c1_ok} bad={c1_bad} "
      f"{'OK' if c1_bad==0 else 'FAIL'}")
for ex in c1_bad_ex: print("  C1 violation:", ex)
print(f"Claim2 entry N 1 j0N <= entry N 1 (LngN-2): ok={c2_ok} bad={c2_bad} "
      f"{'OK' if c2_bad==0 else 'FAIL'}")
for ex in c2_bad_ex: print("  C2 violation:", ex)
