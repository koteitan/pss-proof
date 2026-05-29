"""§6.8 d1pos (i1=1) caseA TrMax-equality empirical check.

Target lemma TrMax_seg_oper_d1pos_eq_caseA:
  N in T_PS, 1<Lng N, notzero, hasParent N (idx1 N (Lng N-1)) (Lng N-1),
  i1 = idx1 N (Lng N-1) = 1, parR1: nextR N 1 (parent N 1 (Lng N-1)) (Lng N-1),
  1<=n, j0' < parent N 1 (Lng N-1)  [caseA], Lng N-2 <= j1', j1' < Lng (N[n])
  ==> TrMax (seg (N[n]) j0' j1') = TrMax (seg N j0' (Lng N-1)).

Mirrors d0zero caseA but with i1=1 (d0pos): row-0 shifts by k*delta, row-1 unshifted.
"""
from red_model import (oper, diagSeq, seg, Lng, entry, idx1, hasParent,
                       parent, multiT, zeroT, nextR, TrMax)
def tup(M): return tuple(M)

UB=4; NMAX=3; KMAX=4
S=[set([tup(diagSeq(u,v)) for u in range(UB+1) for v in range(u,UB+1)])]
for k in range(1,KMAX+1):
    Sk=set()
    for M in S[k-1]:
        for n in range(1,NMAX+1):
            try: Sk.add(tup(oper(list(M),n)))
            except Exception: pass
    S.append(Sk)

def monoT(M): return Lng(M)>1 and not multiT(M) and not zeroT(M)

tot=0; fail=0; ex=[]; nstd=0
for k in range(1,KMAX+1):
    for Ntup in S[k-1]:
        N=list(Ntup)
        if Lng(N)<=1: continue
        if multiT(N) or zeroT(N): continue   # need 1<Lng N, not multi/zero
        j1N=Lng(N)-1
        if entry(N,0,j1N)==0 and entry(N,1,j1N)==0: continue  # notzero
        if entry(N,1,j1N)<=0: continue        # i1=1 (d1pos)
        i1=idx1(N,j1N)
        if i1!=1: continue
        if not hasParent(N,i1,j1N): continue
        j0N=parent(N,1,j1N)                   # ?j0N = parent N 1 (Lng N-1)
        if j0N is None: continue
        # parR1: nextR N 1 j0N (Lng N-1) (parent is the unique row-1 nextR ancestor)
        if not nextR(N,1,j0N,j1N): continue
        if not (j0N<j1N): continue            # j0Nlt
        for n in range(1,NMAX+1):
            M=oper(N,n)
            LM=Lng(M)
            if LM<=1: continue
            for j0 in range(0,j0N):            # caseA: j0' < j0N
                for j1 in range(j0+1,LM):      # j1' < Lng M
                    if not (j1N-1<=j1): continue   # Lng N-2 <= j1' (bge)
                    tot+=1
                    lhs=TrMax(seg(M,j0,j1))
                    rhs=TrMax(seg(N,j0,j1N))
                    if lhs!=rhs:
                        fail+=1
                        if len(ex)<8: ex.append((tuple(N),n,j0,j1,lhs,rhs))
print(f"d1pos caseA total slices = {tot}")
print(f"  TrMax equality failures = {fail}  {'OK' if fail==0 else 'FAIL'}")
for e in ex:
    print("   FAIL N=",e[0]," n=",e[1]," j0',j1'=",e[2],e[3]," lhs=",e[4]," rhs=",e[5])
