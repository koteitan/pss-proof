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
# claims when kk>0 row0 parent is in-block; and entry M 0 off = Joints*+1 unconditional
f_off=0; n=0; f_kkpos_inblock=0; n_kkpos_haspar0=0
for M in cores(5,3):
    Jstar=len(Br(M))-1
    blks=[]
    for J in range(Jstar):
        np=npJ(M,J);jn=Joints(M)[J];eJ=jn+1-np
        blks+=funpow(IncrFirst,eJ,Red(NJ(M,J)))
    off=1+TrMax(M)+len(blks)
    j1=Lng(M)-1; kk=j1-off
    jn=Joints(M)
    n+=1
    if entry(M,0,off)!=jn[Jstar]+1: f_off+=1
    # kk>0: is the row0 parent of j1 in-block?
    if kk>0 and hasParent(M,0,j1):
        n_kkpos_haspar0+=1
        p=parent(M,0,j1)
        if p<off: f_kkpos_inblock+=1
print(f"n={n}: entry0_off!=Joints*+1:{f_off}")
print(f"kk>0 & hasParent row0: {n_kkpos_haspar0}, of which CROSS(p<off): {f_kkpos_inblock}")
