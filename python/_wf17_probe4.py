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
# When kk==0 (last block singleton), is j1==FirstNodes!Jstar and entry M 0 j1 = Joints!Jstar+1 = entry(M,0,Joints!Jstar)+1 always?
n=0;f1=0;f2=0;f3=0
for M in cores(5,3):
    Jstar=len(Br(M))-1
    blks=[]
    for J in range(Jstar):
        np=npJ(M,J);jn=Joints(M)[J];eJ=jn+1-np
        blks+=funpow(IncrFirst,eJ,Red(NJ(M,J)))
    off=1+TrMax(M)+len(blks)
    j1=Lng(M)-1; kk=j1-off
    if kk!=0: continue
    n+=1
    fn=FirstNodes(M); jn=Joints(M)
    if fn[Jstar]!=j1: f1+=1
    if entry(M,0,j1)!=jn[Jstar]+1: f2+=1
    if entry(M,0,jn[Jstar])!=jn[Jstar]: f3+=1   # joint on diagonal trunk => entry=joint
print(f"kk==0 cases n={n}: fn[Jstar]!=j1:{f1}  entry0_j1!=Joints+1:{f2}  entry0_Joint!=Joint(diag):{f3}")
