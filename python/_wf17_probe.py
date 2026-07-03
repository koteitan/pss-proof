import itertools
from red_model import *
def npJ(M,J):
    b=Br(M); fn=FirstNodes(M)
    if entry(b[J],1,0)==0: return 0
    return THE_nextR(M,1,fn[J])+1
def NJ(M,J):
    b=Br(M); jn=Joints(M); m00=entry(M,0,0); m10=entry(M,1,0)
    return [(m00+jn[J]+1, m10+npJ(M,J))]+b[J][1:]
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
# For row0 cross cases: is the last block length 1 (so off==j1)?  And is FirstNodes!Jstar==off?
c0len1=0; c0off=0; n0=0; n1=0
r1_block_singleton=0
for M in cores(4,3):
    Jstar=len(Br(M))-1
    blks=[]
    for J in range(Jstar):
        np=npJ(M,J);jn=Joints(M)[J];eJ=jn+1-np
        blks+=funpow(IncrFirst,eJ,Red(NJ(M,J)))
    off=1+TrMax(M)+len(blks)
    j1=Lng(M)-1
    fn=FirstNodes(M)
    for i in range(2):
        if not hasParent(M,i,j1):continue
        p=parent(M,i,j1)
        if p>=off:continue
        if i==0:
            n0+=1
            if off==j1: c0len1+=1
            if fn[Jstar]==off: c0off+=1
        else:
            n1+=1
            if off==j1: r1_block_singleton+=1
print(f"row0 cross n={n0}: lastblk_singleton(off==j1)={c0len1}, FirstNodes!Jstar==off:{c0off}")
print(f"row1 cross n={n1}: lastblk_singleton(off==j1)={r1_block_singleton}")
