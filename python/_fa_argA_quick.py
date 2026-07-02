import itertools, os
os.chdir(os.path.dirname(__file__))
from red_model import Red, Lng, entry, monoT, nextrel0, diagSeq, IncrFirst, funpow
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
a=0; af=0; ex=None
for M in enum(3,2):
    if not monoT(M) or not RedCondA(M): continue
    if entry(M,1,0)>0:
        arg=coreReduce(M); a+=1
        if not congR(arg,Red(arg)): af+=1; ex=ex or (M,arg)
print(f"congR argA (Red argA) [enum3,2]: {a} tested {af} fail ex={ex}")
