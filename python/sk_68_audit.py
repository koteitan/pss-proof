"""§6.8 prop2 (standard_P_components descending) empirical audit.

Proposition: for M in ST_PS, J0'<=J1'<=Lng(P M)-1 with equal row-0 left ends
  (P(M)_{J0'})_{0,0} = (P(M)_{J1'})_{0,0}, the row-1 left ends are weakly
  decreasing:  (P(M)_{J0'})_{1,0} >= (P(M)_{J1'})_{1,0}.
Also checks the article's last-three-cases display being about row-0 (typo
candidate): the displayed >= is actually the row-1 statement.
Run: python3 sk_68_audit.py
"""
from red_model import oper, P, diagSeq
def tup(M): return tuple(M)

UB=4; NMAX=3; KMAX=5
S=[set([tup(diagSeq(u,v)) for u in range(UB+1) for v in range(u,UB+1)])]
for k in range(1,KMAX+1):
    Sk=set()
    for M in S[k-1]:
        for n in range(1,NMAX+1):
            try: Sk.add(tup(oper(list(M),n)))
            except Exception: pass
    S.append(Sk)
ST=set().union(*S)

def r0(c): return c[0][0]   # (c)_{0,0}
def r1(c): return c[0][1]   # (c)_{1,0}

print("=== prop2: equal row-0 left ends => row-1 weakly decreasing ===")
tot=viol=0
for M in ST:
    comps=P(list(M))
    L=len(comps)
    for J0 in range(L):
        for J1 in range(J0,L):
            if r0(comps[J0])==r0(comps[J1]):
                tot+=1
                if not (r1(comps[J0])>=r1(comps[J1])):
                    viol+=1
                    if viol<=5: print("  VIOL",M,J0,J1)
print(f"  equal-row0 pairs={tot} violations={viol}  {'OK' if viol==0 else 'FAIL'}")

# Helper checks for the planned proof:
def multiT(M):
    # multi = not zero and not mono; mono = strictly increasing row-0 left-ends
    # use red_model's own notion via P length>1
    return len(P(list(M)))>1

print("=== helper: components of P(c[n]) for non-multi c keep left column ===")
tot=ok=0
for c in ST:
    if multiT(c): continue
    for n in range(1,NMAX+1):
        try: cn=oper(list(c),n)
        except Exception: continue
        for d in P(cn):
            tot+=1
            ok+= (r0(d)==r0(c) and r1(d)==r1(c))
print(f"  nonmulti P(c[n]) comps={tot} keep-leftcol={ok}  {'OK' if tot==ok else 'FAIL'}")

print("=== helper: entry(M[n]) i 0 = entry M i 0 (oper preserves left column) ===")
tot=ok=0
for M in ST:
    for n in range(1,NMAX+1):
        try: Mn=oper(list(M),n)
        except Exception: continue
        if not Mn: continue
        tot+=1
        ok+= (Mn[0][0]==M[0][0] and Mn[0][1]==M[0][1])
print(f"  oper instances={tot} keep-leftcol={ok}  {'OK' if tot==ok else 'FAIL'}")
