"""Verify the ABSTRACT lemma I'll prove:

If M', N' in T_PS, agree pointwise on [0,c] (M'!s=N'!s for s<=c), c<Lng M', c<Lng N',
TrMax N' <= c, and (boundary) ~nextR M' 1 (TrMax N') (TrMax N'+1), then TrMax M'=TrMax N'.

Below-trunk: j'<TrMax N' => nextR N' 1 j' (j'+1) (TrMax_trunk_step), transfers to M'
via nextrel1_prefix_imp since j',j'+1<=TrMax N'<=c. Stop given by hypothesis. TrMax_eqI.

Here verify: with c = Lng N' - 2 (agreement region), TrMax N' <= c always (case A),
and the boundary hypothesis IS exactly what holds. So the abstract lemma is sound and
the residual is the boundary hypothesis.
"""
from red_model import (oper, diagSeq, seg, le0, monoT, Lng, entry, TrMax,
                       idx1, hasParent, parent, nextrel1)
def tup(M): return tuple(M)
def nextR1(M,a,b): return nextrel1(M,a,b)
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
ok=bad=0
for Nt in ST:
    N=list(Nt); LN=Lng(N)
    if LN<=1 or not monoT(N): continue
    j1N=LN-1
    if entry(N,1,j1N)!=0 or idx1(N,j1N)!=0 or not hasParent(N,0,j1N): continue
    j0N=parent(N,0,j1N)
    if j0N is None or not(j0N<j1N): continue
    w=j1N-j0N
    for n in range(2,NMAX+1):
        M=oper(N,n); LM=Lng(M)
        if LM != j0N + n*w: continue
        for j0p in range(0,j0N):
            for j1p in range(j0N+1,LM):
                if not le0(M,j0p,j1p): continue
                Np=seg(N,j0p,j1N); Mp=seg(M,j0p,j1p); LNp=Lng(Np)
                c=LNp-2
                TN=TrMax(Np)
                # check agreement [0,c]
                agree=all(Mp[s]==Np[s] for s in range(c+1))
                assert agree, (N,n,j0p,j1p)
                assert TN<=c
                # boundary hypothesis must hold (M' stops at TN)
                bnd = not nextR1(Mp,TN,TN+1)
                if bnd: ok+=1
                else: bad+=1
print(f"abstract-lemma soundness: agreement+TN<=c hold; boundary holds: ok={ok} bad={bad} "
      f"{'OK' if bad==0 else 'FAIL'}")
