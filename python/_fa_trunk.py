import itertools, os
os.chdir(os.path.dirname(__file__))
from red_model import Red, Lng, entry, monoT, TrMax
from red_charac import RedCondA
def enum(maxlen,maxe):
    cols=[(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    for L in range(1,maxlen+1):
        for M in itertools.product(cols,repeat=L): yield list(M)
tot=fail=0; ex=None
for M in enum(5,3):
    if not monoT(M) or not RedCondA(M): continue
    if entry(M,0,0)==0 and entry(M,1,0)==0 and TrMax(M)==Lng(M)-1:
        tot+=1
        if not all(entry(M,0,k)==k and entry(M,1,k)==k for k in range(Lng(M))):
            fail+=1
            if ex is None: ex=M
print(f"trunk-core diag: {tot} tested, {fail} fail, ex={ex}")
