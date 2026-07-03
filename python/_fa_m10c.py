import itertools, os
os.chdir(os.path.dirname(__file__))
from red_model import Red, Lng, entry, monoT, nextrel0, diagSeq, IncrFirst, funpow, seg
from red_charac import RedCondA
def enum(maxlen,maxe):
    cols=[(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    for L in range(1,maxlen+1):
        for M in itertools.product(cols,repeat=L): yield list(M)
def congR(A,X):
    if Lng(A)!=Lng(X): return False
    n=Lng(X)
    return all(nextrel0(A,p,q)==nextrel0(X,p,q) for p in range(n) for q in range(n)) and \
           all(entry(A,1,j)==entry(X,1,j) for j in range(n))
# claim: congR (IncrFirst^m10 M) (Red M)
c=0; cf=0; ex=None
for M in enum(4,3):
    if not monoT(M) or not RedCondA(M): continue
    if entry(M,1,0)>0:
        m10=entry(M,1,0); IM=funpow(IncrFirst,m10,M)
        c+=1
        if not congR(IM,Red(M)): cf+=1; ex=ex or (M, IM, Red(M))
print(f"congR (IncrFirst^m10 M)(Red M): {c} tested {cf} fail ex={ex}")
