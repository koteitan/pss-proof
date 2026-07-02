import itertools, os
os.chdir(os.path.dirname(__file__))
from red_model import Red, Lng, entry, monoT, zeroT, nextrel0, diagSeq, IncrFirst, funpow
from red_charac import RedCondA
def enum(maxlen,maxe):
    cols=[(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    for L in range(1,maxlen+1):
        for M in itertools.product(cols,repeat=L): yield list(M)
def coreReduce(M):
    m00=entry(M,0,0); m10=entry(M,1,0)
    if m10==0: return [(entry(M,0,j)-m00, entry(M,1,j)) for j in range(Lng(M))]
    return diagSeq(0,m10-1)+funpow(IncrFirst,m10,M)
def congR(A,X):
    if Lng(A)!=Lng(X): return False
    n=Lng(X)
    return all(nextrel0(A,p,q)==nextrel0(X,p,q) for p in range(n) for q in range(n)) and \
           all(entry(A,1,j)==entry(X,1,j) for j in range(n))
# Hypothesis: congR M ((IncrFirst^^m10) M) holds (IncrFirst preserves nextrel0+row1)
i1=0; i1f=0; ex=None
# Hypothesis: Red argA = diagSeq 0 (m10-1) @ Red M  (b2_N_eq_diag_RedM)
b2=0; b2f=0; exb=None
for M in enum(4,3):
    if not monoT(M) or not RedCondA(M): continue
    if entry(M,1,0)>0:
        m10=entry(M,1,0)
        IM=funpow(IncrFirst,m10,M)
        i1+=1
        if not congR(M,IM): i1f+=1; ex=ex or M
        arg=coreReduce(M)
        b2+=1
        if Red(arg)!=diagSeq(0,m10-1)+Red(M): b2f+=1; exb=exb or M
print(f"congR M (IncrFirst^m10 M): {i1} tested {i1f} fail ex={ex}")
print(f"Red argA = diag @ Red M: {b2} tested {b2f} fail ex={exb}")
