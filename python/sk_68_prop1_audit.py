"""§6.8 prop1 (slice_Br_descending) empirical audit.

Proposition (pss_paper p_6_8_standard_slice_Br_descending):
  M in ST_PS, j0' < j1' <= Lng M - 1, (0,j0') <=_M (0,j1')
  ==> monoT (seg M j0' j1') AND descending (Br (seg M j0' j1')).
Run: python3 sk_68_prop1_audit.py
"""
from red_model import oper, diagSeq, seg, Br, le0, monoT, Lng
def tup(M): return tuple(M)

UB=4; NMAX=2; KMAX=3   # full UB=4,KMAX=5 set is too large for the O(L^2) check
S=[set([tup(diagSeq(u,v)) for u in range(UB+1) for v in range(u,UB+1)])]
for k in range(1,KMAX+1):
    Sk=set()
    for M in S[k-1]:
        for n in range(1,NMAX+1):
            try: Sk.add(tup(oper(list(M),n)))
            except Exception: pass
    S.append(Sk)
ST=set().union(*S)

def descending(Q):
    L=len(Q)
    for J0 in range(L):
        for J1 in range(J0,L):
            if Q[J0][0][0] < Q[J1][0][0]:
                return False
            if Q[J0][0][0]==Q[J1][0][0] and Q[J0][0][1] < Q[J1][0][1]:
                return False
    return True

tot=viol_mono=viol_desc=0
for M in ST:
    M=list(M); j1max=Lng(M)-1
    for j0 in range(0,j1max+1):
        for j1 in range(j0+1,j1max+1):
            if le0(M,j0,j1):
                tot+=1
                sl=seg(M,j0,j1)
                if not monoT(sl): viol_mono+=1
                if not descending(Br(sl)): viol_desc+=1
print(f"prop1: qualifying (j0'<j1', (0,j0')<=(0,j1')) pairs={tot}")
print(f"  monoT(seg) violations={viol_mono}  {'OK' if viol_mono==0 else 'FAIL'}")
print(f"  descending(Br(seg)) violations={viol_desc}  {'OK' if viol_desc==0 else 'FAIL'}")
