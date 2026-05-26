from red_model import oper, P, diagSeq, Lng
def tup(M): return tuple(M)
# Test aaf6's witness: diagSeq u v == diagSeq u (v+1) [1] (=Pred)?
print("=== diagSeq u v == oper(diagSeq u (v+1), 1) ? ===")
ok=tot=0
for u in range(6):
    for v in range(u,6):
        lhs=diagSeq(u,v); rhs=oper(diagSeq(u,v+1),1); tot+=1
        if lhs==rhs: ok+=1
        else: print(f"  MISMATCH u={u} v={v}: {lhs} vs {rhs}")
print(f"  {ok}/{tot}")

# Now test monotonicity S_k ⊆ S_{k+1} with a LARGER bound to push truncation away,
# and ALSO check whether apparent S_k\S_{k+1} are all at the v=UB boundary.
UB=6; NMAX=4; KMAX=4
S=[set([tup(diagSeq(u,v)) for u in range(UB+1) for v in range(u,UB+1)])]
for k in range(1,KMAX+1):
    Sk=set()
    for M in S[k-1]:
        for n in range(1,NMAX+1):
            try: Sk.add(tup(oper(list(M),n)))
            except Exception: pass
    S.append(Sk)
print("=== S_k \\ S_{k+1}: are all 'missing' at truncation boundary? ===")
def maxentry(M): return max((max(a,b) for (a,b) in M), default=0)
for k in range(KMAX):
    miss=[M for M in S[k] if M not in S[k+1]]
    # boundary = contains an entry == UB (would need UB+1 source, truncated out)
    nonbdry=[M for M in miss if maxentry(M) < UB]
    print(f"k={k}: |S_k\\S_{k+1}|={len(miss)}  of which NOT-at-boundary(maxentry<UB)={len(nonbdry)}")
    for M in nonbdry[:5]: print("    real counterexample?:", M)
