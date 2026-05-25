"""§6.7 standard_P_components empirical audit (faithful model).

Verifies the proposition (P-components of S_k elements are in S_k, SAME rank)
and the two sub-lemmas that the article proof omits:
  T : forall X in S_k, every P-component P(X)_J in S_k.
  R : non-last P-components of X in S_k have row-1 all zero.
  U : row1z(c) & c in S_k  =>  c in S_{k+1}.
Also shows S_{k-1} ⊄ S_k (the article proof's implicit monotonicity is false).
Run: python3 sk_67_audit.py
"""
from red_model import oper, P, diagSeq
def tup(M): return tuple(M)
def row1z(c): return all(p[1]==0 for p in c)

UB=4; NMAX=3; KMAX=5
S=[set([tup(diagSeq(u,v)) for u in range(UB+1) for v in range(u,UB+1)])]
for k in range(1,KMAX+1):
    Sk=set()
    for M in S[k-1]:
        for n in range(1,NMAX+1):
            try: Sk.add(tup(oper(list(M),n)))
            except Exception: pass
    S.append(Sk)

print("=== T: all P-components of X in S_k are in S_k ===")
for k in range(KMAX+1):
    bad=sum(1 for X in S[k] for c in P(list(X)) if tup(c) not in S[k])
    print(f"  k={k} |S_k|={len(S[k])} violations={bad}")

print("=== monotonicity S_{k-1} ⊆ S_k is FALSE ===")
for k in range(1,KMAX+1):
    miss=len([M for M in S[k-1] if M not in S[k]])
    print(f"  k={k}: |S_{k-1}\\S_k|={miss}")

print("=== R: non-last P-components have row-1 all zero ===")
tot=ok=0
for k in range(KMAX):
    for X in S[k]:
        comps=P(list(X))
        for J in range(len(comps)-1):
            tot+=1; ok+= row1z(comps[J])
print(f"  non-last={tot} row1-all-zero={ok}  {'OK' if tot==ok else 'FAIL'}")

print("=== U: row1z(c) & c∈S_k ⟹ c∈S_(k+1) ===")
tot=ok=0
for k in range(KMAX):
    for X in S[k]:
        if row1z(X):
            tot+=1; ok+= (X in S[k+1])
print(f"  row1z∈S_k={tot} also∈S_(k+1)={ok}  {'OK' if tot==ok else 'FAIL'}")
