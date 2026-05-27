"""Refined audit: understand the TrMax-equality stop condition for d0zero case A.

For each case-A context, with N'=seg N j0' (LngN-1), M'=seg M j0' j1',
T = TrMax N' = TrMax M' (claim 1). Investigate the stop step at T in M':
  nextR M' 1 T (T+1) must FAIL. Where does index T+1 of M' map to?
Also test variants of the boundary inequality only in the cases that matter.
"""
from red_model import (oper, diagSeq, seg, Br, le0, monoT, Lng, entry, TrMax,
                       idx1, hasParent, parent, nextrel1)
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

# In M' coordinates index s maps to M index j0'+s. With d0zero layout
# M index x>=j0N maps periodically to N index j0N + (x-j0N) mod w.
# We want: when T = (LngN-1) - 1 - j0' (i.e. trunk of N' reaches its last index),
# the stop in M' at T occurs. Investigate the row-1 values around the boundary.

boundary_cases=0
ineq_variants={}
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
                Np=seg(N,j0p,j1N)
                Mp=seg(M,j0p,j1p)
                T=TrMax(Mp)
                TN=TrMax(Np)
                if T!=TN: continue
                LNp=Lng(Np)  # = j1N - j0' + 1
                # is T at the boundary, i.e. trunk reaches last index of N' minus?
                # N' last index = LNp-1 = j1N - j0'.
                if T == LNp-1:
                    boundary_cases+=1
                    # stop at T fails because T = last index (no T+1). skip.
ans=boundary_cases
print("contexts where TrMax(N') = Lng N' - 1 (trunk fills N', Br N'=[]):", ans)
