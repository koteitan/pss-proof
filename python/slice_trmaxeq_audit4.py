"""Corrected: M and N agree on [0, j1N-1] = [0, LngN-2] (period w breaks only
at x=j1N where M!j1N=N!j0N != N!j1N). So M' and N' agree on indices s with
j0'+s <= j1N-1, i.e. s <= (j1N-1)-j0' = LNp-2  (LNp = Lng N' = j1N-j0'+1).

So agreement region is [0, LNp-2]; they differ only at the LAST index LNp-1.

Check: is TrMax N' always <= LNp-2 (so trunk and trunk-step lie in agreement)?
i.e. TrMax N' < LNp-1 = Lng N' - 1, i.e. Br N' != [] always in case A?
And does the stop at TrMax N' lie within agreement (TrMax N'+1 <= LNp-2)?
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
tm_le=0; tm_gt=0  # TrMax N' vs LNp-2 (agreement upper bound)
stop_in_agree=0; stop_out=0
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
            for j1p in range(j0N+1,LM):
                if not le0(M,j0p,j1p): continue
                Np=seg(N,j0p,j1N); Mp=seg(M,j0p,j1p)
                TN=TrMax(Np); LNp=Lng(Np)
                agree_ub=LNp-2  # agree on [0, agree_ub]
                tot+=1
                if TN<=agree_ub: tm_le+=1
                else:
                    tm_gt+=1
                    if len(exs)<6: exs.append(("TN>ub",N,n,j0p,j1p,TN,agree_ub))
                # stop step index TN+1
                if TN+1<=agree_ub: stop_in_agree+=1
                else:
                    stop_out+=1
                    # need: TN+1 = LNp-1 (the differing last index); verify
                    if TN+1!=LNp-1 and len(exs)<12:
                        exs.append(("stop!=last",N,n,j0p,j1p,TN,LNp))

print(f"total case-A: {tot}")
print(f"TrMax N' <= agree_ub (=LNp-2): {tm_le}   TrMax N' > ub: {tm_gt}")
print(f"stop index TN+1 in agreement: {stop_in_agree}   stop at differing last idx: {stop_out}")
for e in exs: print("  ", e)
