"""The 72 hard cases: TrMax N' = LNp-2 (trunk one short of end), stop step at the
differing last index. Investigate why M' stops there (no nextR M' 1 (LNp-2)(LNp-1)).

In M' the last index s=LNp-1 maps to M index j1'. We have j1' in some block q.
M!j1' = N!(j0N + (j1'-j0N) mod w). row-1 value entry M 1 j1' = entry N 1 (j0N+r')
where r' = (j1'-j0N) mod w.

For nextR M' 1 (LNp-2)(LNp-1) to hold we'd need entry M' 1 (LNp-2) < entry M' 1 (LNp-1)
AND le0 M' (LNp-2)(LNp-1) AND row-1 minimality. Since M' stops, ONE of these fails.

In N': nextR N' 1 (LNp-2)(LNp-1) ALSO fails (TrMax N' = LNp-2). N' last col is N!j1N,
entry N 1 j1N = 0 (d0zero!). So in N', entry N' 1 (LNp-1) = 0, and the row-1
strict-increase entry N' 1 (LNp-2) < 0 is impossible -> N' stops because the last
col has row-1 = 0.

For M': what is entry M' 1 (LNp-1) = entry M 1 j1' = entry N 1 (j0N+r')? Print it,
and entry M' 1 (LNp-2). Find what makes M' stop.
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

# reasons M' stops at LNp-2 -> LNp-1
reason_count={}
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
                if TN!=LNp-2: continue   # the hard cases
                a=LNp-2; b=LNp-1
                # why does M' stop at a->b?
                v_a=entry(Mp,1,a); v_b=entry(Mp,1,b)
                strict = v_a < v_b
                l0 = le0(Mp,a,b)
                # minimality: exists j with a<j and le0 Mp j b and entry Mp 1 j < entry Mp 1 b
                minfail = any(a<j and le0(Mp,j,b) and entry(Mp,1,j)<v_b for j in range(Lng(Mp)))
                if not strict: r="not_strict(v_a>=v_b)"
                elif not l0: r="no_le0"
                elif minfail: r="min_fail"
                else: r="UNKNOWN_should_hold!"
                reason_count[r]=reason_count.get(r,0)+1
                if r=="UNKNOWN_should_hold!" and len(exs)<6:
                    exs.append((N,n,j0p,j1p,v_a,v_b))
                if r=="not_strict(v_a>=v_b)" and len(exs)<8:
                    r_off=(j1p-j0N)%w
                    exs.append(("strict-fail",N,n,j0p,j1p,"v_a",v_a,"v_b",v_b,"r'",r_off,
                                "eN1_j0N",entry(N,1,j0N)))

print("reasons M' stops at the differing last index (TrMax N'=LNp-2):")
for k,v in reason_count.items(): print(f"  {k}: {v}")
for e in exs: print("  ", e)
