from red_model import oper, P, diagSeq, Lng, multiT
def tup(M): return tuple(M)
def row1z(M): return all(p[1]==0 for p in M)
def Pred(M): return M[:-1] if Lng(M)>1 else M
UB=4; NMAX=3; KMAX=5
allstd=set([tup(diagSeq(u,v)) for u in range(UB+1) for v in range(u,UB+1)])
S=[set(allstd)]
for k in range(1,KMAX+1):
    Sk=set()
    for M in S[k-1]:
        for n in range(1,NMAX+1):
            try: Sk.add(tup(oper(list(M),n)))
            except Exception: pass
    S.append(Sk); allstd|=Sk

# nonmulti-oper_1 signature: M nonmulti, P(M[2]) = [Pred M, Pred M] (>=2 equal comps = Pred M)
# check Row1Zero(Pred M) in that case.
tot=ok=0; bad=[]
for X in allstd:
    M=list(X)
    if not multiT(M) and Lng(M)>1:
        PM2=P(oper(M,2))
        # oper_1 case: all components equal Pred M and there are n(=2) of them
        if len(PM2)>=2 and all(tup(c)==tup(Pred(M)) for c in PM2):
            tot+=1
            if row1z(Pred(M)): ok+=1
            elif len(bad)<8: bad.append((tup(M),tup(Pred(M))))
print(f"nonmulti-oper_1 monomials: Row1Zero(Pred M) = {ok}/{tot}")
for (M,pm) in bad: print(f"  FAIL M={M} Pred={pm}")

# ALSO directly verify the folded predicate end-to-end:
# Phi(X) = (forall J: P X!J in S_k) and (forall J<last: Row1Zero(P X!J)), for X in S_k
print("=== folded Φ(X) over S_k (T ∧ R) violations ===")
for k in range(KMAX+1):
    vT=vR=0
    for X in S[k]:
        comps=P(list(X))
        for J,c in enumerate(comps):
            if tup(c) not in S[k]: vT+=1
            if J<len(comps)-1 and not row1z(c): vR+=1
    print(f"k={k}: T-viol={vT} R-viol={vR}")
