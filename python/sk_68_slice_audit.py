"""§6.8 prop1 reduction audit: slice_P_descending.

prop1 (slice_Br_descending) reduces (via seg_of_seg) to:
  slice_P_descending: M in ST_PS, a<=b<=Lng M-1  =>  descending(P(seg M a b)).
This checks (G1): descending(P(seg M a b)) for EVERY slice of a standard form
  (0 violations expected). The row-0 part is m_6_4_P_leftend_mono; the content
  is the row-1 tie-break.
Run: python3 sk_68_slice_audit.py
"""
from red_model import oper, diagSeq, seg, Lng, P
def tup(M): return tuple(M)

UB=4; NMAX=2; KMAX=3
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
            if Q[J0][0][0] < Q[J1][0][0]: return False
            if Q[J0][0][0]==Q[J1][0][0] and Q[J0][0][1] < Q[J1][0][1]: return False
    return True

tot=viol=0; ex=[]
for M in ST:
    M=list(M); n=Lng(M)
    for a in range(n):
        for b in range(a,n):
            Y=seg(M,a,b); tot+=1
            if not descending(P(Y)):
                viol+=1
                if len(ex)<6: ex.append((tuple(M),a,b,tuple(Y)))
print(f"(G1) descending(P(seg M a b)) for every slice of M in ST_PS:")
print(f"  slices={tot} violations={viol}  {'OK' if viol==0 else 'FAIL'}")
for e in ex: print("  VIOL M=",e[0]," a,b=",e[1],e[2]," Y=",e[3])
