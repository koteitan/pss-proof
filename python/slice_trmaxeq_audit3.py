"""Where do M' = seg M j0' j1' and N' = seg N j0' (LngN-1) agree pointwise,
and what is the prefix length on which TrMax_eqI can be driven?

M index x: for x<j0N, M!x=N!x. For x>=j0N, M!x=N!(j0N+(x-j0N) mod w) (period w).
So M'!s = M!(j0'+s).  N'!s = N!(j0'+s).
They agree for j0'+s < j0N i.e. s < j0N - j0'. Call P = j0N - j0' (prefix len in M').
After that M' is periodic with period w = j1N - j0N, repeating block N[j0N..j1N-1].
N' continues as N from j0N to j1N (one block + final col).

Claim: TrMax M' = TrMax N' and both equal min(TrMax-of-N'-trunk).
Let's check: is TrMax N' always < P = j0N - j0' ? (trunk stays in shared prefix)
If so, TrMax_eqI transfers trivially via nextrel1_prefix_imp on prefix [0, TrMax N'].
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

tot=0
tm_lt_P=0; tm_eq_P=0; tm_gt_P=0
# Also: relationship between TrMax N' and P = j0N-j0'
exs_ge=[]
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
                Np=seg(N,j0p,j1N); Mp=seg(M,j0p,j1p)
                TN=TrMax(Np)
                P=j0N-j0p  # prefix length in M'/N' where they agree
                tot+=1
                if TN < P: tm_lt_P+=1
                elif TN==P:
                    tm_eq_P+=1
                    if len(exs_ge)<6: exs_ge.append(("EQ",N,n,j0p,j1p,TN,P))
                else:
                    tm_gt_P+=1
                    if len(exs_ge)<6: exs_ge.append(("GT",N,n,j0p,j1p,TN,P))

print(f"total case-A: {tot}")
print(f"TrMax N' < P (=j0N-j0'): {tm_lt_P}")
print(f"TrMax N' = P            : {tm_eq_P}")
print(f"TrMax N' > P            : {tm_gt_P}")
for e in exs_ge: print("  ", e)
