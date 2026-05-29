"""§6.8 d0pos (i1=1) sub-case audit.

Setup mirrors the Isabelle proof: M = N[n], N in SkT_PS, N monoT, 1<Lng N,
i1 = idx1 N (Lng N-1) = 1 (entry N 1 (Lng N-1) > 0), slice seg M j0' j1' with
j0'<j1'<=Lng M-1, leR M 0 j0' j1', and the slice reaches: Lng N-1 <= j1' (jlarge).

We verify:
  (V0) A0 is VACUOUS: in this branch j_{-2}^N = parent N 1 (Lng N-1) < Lng N-1 <= j1',
       so j1' <= j_{-2}^N never happens.
  (VC) the article's true case split: j0' < j_{-2}^N (caseC-like) vs j0' >= j_{-2}^N.
  Counts per article sub-case, and a global check that descending(Br(seg M j0' j1'))
  holds (sanity: the whole theorem is true).
"""
from red_model import (oper, diagSeq, seg, Lng, P, Br, entry, idx1, hasParent,
                       parent, multiT, zeroT, leR, nextR)
def tup(M): return tuple(M)

UB=4; NMAX=3; KMAX=3
S=[set([tup(diagSeq(u,v)) for u in range(UB+1) for v in range(u,UB+1)])]
for k in range(1,KMAX+1):
    Sk=set()
    for M in S[k-1]:
        for n in range(1,NMAX+1):
            try: Sk.add(tup(oper(list(M),n)))
            except Exception: pass
    S.append(Sk)

def monoT(M): return Lng(M)>1 and not multiT(M) and not zeroT(M)

def descending(Q):
    L=len(Q)
    for J0 in range(L):
        for J1 in range(J0,L):
            if Q[J0][0][0] < Q[J1][0][0]: return False
            if Q[J0][0][0]==Q[J1][0][0] and Q[J0][0][1] < Q[J1][0][1]: return False
    return True

v0_fail=0; tot=0; cC=0; cBprefix=0; desc_fail=0; ex=[]
A0_seen=0
for k in range(1,KMAX+1):
    for Ntup in S[k-1]:
        N=list(Ntup)
        if Lng(N)<=1: continue
        if not (monoT(N) or multiT(N) or zeroT(N)): pass
        # need N not multi, not zero, 1<Lng N -> monoT N
        if multiT(N) or zeroT(N): continue
        j1N=Lng(N)-1
        if entry(N,0,j1N)==0 and entry(N,1,j1N)==0: continue  # notzero
        if entry(N,1,j1N)<=0: continue  # need i1=1 (d0pos)
        i1=idx1(N,j1N)
        if i1!=1: continue
        if not hasParent(N,i1,j1N): continue
        j2N=parent(N,1,j1N)   # = ?j0N
        if j2N is None or not (j2N<j1N): continue
        for n in range(1,NMAX+1):
            M=oper(N,n)
            if Lng(M)<=1: continue
            LM=Lng(M)
            for j0 in range(LM):
                for j1 in range(j0+1,LM):
                    if j1>LM-1: continue
                    if not leR(M,0,j0,j1): continue
                    if not (j1N<=j1): continue   # jlarge branch
                    tot+=1
                    # V0: A0 vacuity
                    if j1<=j2N:
                        A0_seen+=1
                    # case split
                    if j0<j2N: cC+=1
                    else: cBprefix+=1
                    # global truth sanity
                    if not descending(Br(seg(M,j0,j1))):
                        desc_fail+=1
                        if len(ex)<5: ex.append((tuple(M),j0,j1))
print(f"d0pos (i1=1) jlarge slices total = {tot}")
print(f"  (V0) A0 (j1' <= j_2N) occurrences = {A0_seen}  (expect 0 => A0 VACUOUS)")
print(f"  j0' < j_2N  (caseC-like)         = {cC}")
print(f"  j0' >= j_2N (prefix-shift)        = {cBprefix}")
print(f"  descending(Br(seg M j0' j1')) failures = {desc_fail}  {'OK' if desc_fail==0 else 'FAIL'}")
for e in ex: print("   DESC-FAIL M=",e[0]," j0',j1'=",e[1],e[2])
