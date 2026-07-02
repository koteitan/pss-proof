import itertools
from red_model import *
src=open('_wf19_valpin.py').read()
exec(src.split('def main')[0].split('from red_model import *\n')[1])
def gen_cores(maxlen, maxval):
    seqs=[]
    for L in range(2,maxlen+1):
        for body in itertools.product(range(maxval+1), repeat=2*L):
            M=[(body[2*j],body[2*j+1]) for j in range(L)]
            if M[0]!=(0,0): continue
            try:
                if not monoT(M): continue
                if Red(M)!=M: continue
                if TrMax(M)==Lng(M)-1: continue
            except Exception: continue
            seqs.append(M)
    return seqs
cores=gen_cores(5,3)
nc=0
# minimality check: for x>q with le0 N x lastN, entry N 1 x >= eRs1kk
# also characterize WHICH x qualify (are they all in the Rs tail? or include diag?)
f_min=0
detail=[]
for M in cores:
    Jstar=len(Br(M))-1; j1=Lng(M)-1
    if not hasParent(M,1,j1): continue
    p=parent(M,1,j1)
    blks=[]
    for J in range(Jstar):
        np=npJ(M,J); jn=Joints(M)[J]; eJ=jn+1-np
        blks+=funpow(IncrFirst,eJ,Red(NJ(M,J)))
    off=1+TrMax(M)+len(blks)
    if p>=off: continue
    Rs=Red(NJ(M,Jstar)); kk=Lng(NJ(M,Jstar))-1
    if kk==0: continue
    eRs10=entry(Rs,1,0); eRs1kk=entry(Rs,1,kk)
    if eRs10==0: continue
    d=eRs10-1; N=diagSeq(0,d)+Rs
    if not (RedCondA(N) and RedCondB(N)): continue
    nc+=1
    lastN=Lng(N)-1; q=eRs1kk-1
    LN=Lng(N)
    bad=[]
    for x in range(LN):
        if x>q and le0(N,x,lastN):
            if entry(N,1,x)<eRs1kk:
                bad.append((x,entry(N,1,x)))
    if bad:
        f_min+=1
        if len(detail)<5: detail.append((fmt(M),q,eRs1kk,lastN,d,bad))
print("cases:",nc,"minimality violations:",f_min)
for x in detail: print(x)
