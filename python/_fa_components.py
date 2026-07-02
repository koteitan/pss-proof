import itertools, os
os.chdir(os.path.dirname(__file__))
from red_model import Red, Lng, entry, monoT, nextrel0
from red_charac import RedCondA
def enum(maxlen,maxe):
    cols=[(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    for L in range(1,maxlen+1):
        for M in itertools.product(cols,repeat=L): yield list(M)
r1tot=r1f=0; n0tot=n0f=0; ex1=exn=None
for M in enum(4,3):
    if not monoT(M) or not RedCondA(M): continue
    R=Red(M); n=Lng(M)
    if Lng(R)!=n: continue
    r1tot+=1
    if not all(entry(M,1,j)==entry(R,1,j) for j in range(n)):
        r1f+=1; ex1=ex1 or M
    n0tot+=1
    ok=all(nextrel0(M,p,q)==nextrel0(R,p,q) for p in range(n) for q in range(n))
    if not ok: n0f+=1; exn=exn or M
print(f"row1 eq: {r1tot} tested {r1f} fail ex={ex1}")
print(f"nextrel0 eq: {n0tot} tested {n0f} fail ex={exn}")
