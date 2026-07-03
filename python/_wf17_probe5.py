import itertools
from red_model import *
def npJ(M,J):
    b=Br(M);fn=FirstNodes(M)
    if entry(b[J],1,0)==0:return 0
    return THE_nextR(M,1,fn[J])+1
def NJ(M,J):
    b=Br(M);jn=Joints(M);m00=entry(M,0,0);m10=entry(M,1,0)
    return [(m00+jn[J]+1,m10+npJ(M,J))]+b[J][1:]
def cores(maxlen,maxval):
    out=[]
    for L in range(2,maxlen+1):
        for body in itertools.product(range(maxval+1),repeat=2*L):
            M=[(body[2*j],body[2*j+1]) for j in range(L)]
            if M[0]!=(0,0):continue
            try:
                if not monoT(M):continue
                if Red(M)!=M:continue
                if TrMax(M)==Lng(M)-1:continue
            except:continue
            out.append(M)
    return out
# row1 cross: relationships
n=0; f_ej1=0; f_p=0; f_e1p=0; f_kkrel=0
for M in cores(5,3):
    Jstar=len(Br(M))-1
    blks=[]
    for J in range(Jstar):
        np=npJ(M,J);jn=Joints(M)[J];eJ=jn+1-np
        blks+=funpow(IncrFirst,eJ,Red(NJ(M,J)))
    off=1+TrMax(M)+len(blks)
    j1=Lng(M)-1; kk=j1-off
    for i in [1]:
        if not hasParent(M,i,j1):continue
        p=parent(M,i,j1)
        if p>=off:continue
        n+=1
        nps=npJ(M,Jstar)
        if entry(M,1,j1)!=nps: f_ej1+=1
        if nps!=p+1: f_p+=1
        if entry(M,1,p)!=p: f_e1p+=1
        # is entry block row1 constant within block? entry(M,1,off)==entry(M,1,j1)?
        if entry(M,1,off)!=entry(M,1,j1): f_kkrel+=1
print(f"row1 cross n={n}: entry1_j1!=npJ*:{f_ej1}  npJ*!=p+1:{f_p}  entry1_p!=p:{f_e1p}  entry1_off!=entry1_j1:{f_kkrel}")
