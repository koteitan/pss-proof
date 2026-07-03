import itertools, os
os.chdir(os.path.dirname(__file__))
from red_model import Red, Lng, entry, monoT, TrMax, nextrel0
from red_charac import RedCondA, hasParent, parent
def enum(maxlen,maxe):
    cols=[(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    for L in range(1,maxlen+1):
        for M in itertools.product(cols,repeat=L): yield list(M)
tot=fail=0; ex=None
for M in enum(6,3):
    if not monoT(M) or not RedCondA(M): continue
    if entry(M,0,0)==0 and entry(M,1,0)==0 and TrMax(M)==Lng(M)-1:
        tot+=1
        for k in range(Lng(M)-1):
            # row0: nextrel0 k (k+1) and unique parent
            if not nextrel0(M,k,k+1): fail+=1; ex=(M,'n0',k); break
            if not hasParent(M,0,k+1): fail+=1; ex=(M,'hp',k); break
            if parent(M,0,k+1)!=k: fail+=1; ex=(M,'par',k); break
print(f"trunk-core row0 consec: {tot} tested, {fail} fail, ex={ex}")
