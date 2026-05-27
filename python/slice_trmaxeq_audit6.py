"""Pin down the EXACT inequality needed and verify it on the needed domain.

The hard stop arises when j1' is a block-start (r'=(j1'-j0N)%w==0, j1'=j0N+q*w, q>=1)
AND le0 M j0' j1' holds. Then M' last col = M!j1' has row-1 = entry N 1 j0N, and
M' second-last col = M!(j1'-1) has row-1 = entry N 1 (j1N-1)=entry N 1 (LngN-2).
M' stops because entry N 1 j0N <= entry N 1 (LngN-2)  -- need this ON THIS DOMAIN.

Test the inequality entry N 1 j0N <= entry N 1 (Lng N - 2) RESTRICTED to:
  exists q>=1 with j0N+q*w < LM=Lng M and le0 M j0' (j0N+q*w) for some j0'<j0N.
i.e. the cases where a block-start j1' is le0-reachable from a j0'<j0N.

Actually simpler hypothesis from N alone: in d0zero with the parent chain, is
  entry N 1 (LngN-2) >= entry N 1 j0N
true whenever there EXISTS a valid case-A context with j1' a reachable block start?
"""
from red_model import (oper, diagSeq, seg, le0, monoT, Lng, entry, TrMax,
                       idx1, hasParent, parent, nextrel1, nextR)
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

needed_ok=needed_bad=0
exs=[]
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
            # block-start targets j1' = j0N+q*w, q>=1
            for q in range(1,n):
                j1p=j0N+q*w
                if j1p>=LM or j1p<=j0N: continue
                if not le0(M,j0p,j1p): continue
                # this is exactly a hard-stop context. check inequality
                if entry(N,1,j0N) <= entry(N,1,LN-2):
                    needed_ok+=1
                else:
                    needed_bad+=1
                    if len(exs)<8: exs.append((N,n,j0p,j1p,entry(N,1,j0N),entry(N,1,LN-2)))

print(f"hard-stop (block-start j1', le0 reachable) contexts: ok={needed_ok} bad={needed_bad} "
      f"{'OK' if needed_bad==0 else 'FAIL'}")
for e in exs: print("  ", e)
