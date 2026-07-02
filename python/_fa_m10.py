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
    if m10==0:
        return [(entry(M,0,j)-m00, entry(M,1,j)) for j in range(Lng(M))]
    return diagSeq(0,m10-1)+funpow(IncrFirst,m10,M)
rca=0; rcaf=0; ex=None
mz=0; mzf=0; exz=None
for M in enum(4,3):
    if not monoT(M) or not RedCondA(M): continue
    if entry(M,1,0)>0:  # m10>0 branch
        arg=coreReduce(M)
        rca+=1
        if not RedCondA(arg): rcaf+=1; ex=ex or M
        mz+=1
        if not (monoT(arg) or zeroT(arg)): mzf+=1; exz=exz or M
print(f"m10>0 RedCondA(argA): {rca} tested {rcaf} fail ex={ex}")
print(f"m10>0 monoT-or-zeroT(argA): {mz} tested {mzf} fail ex={exz}")
