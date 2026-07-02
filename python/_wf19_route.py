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
f_parval=0; f_haspar=0; f_eRs1kk_pos=0
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
    eRs10=entry(Rs,1,0)
    N=diagSeq(0,eRs10-1)+Rs if eRs10>0 else Rs
    if not (RedCondA(N) and RedCondB(N)): continue
    nc+=1
    eRs1kk=entry(Rs,1,kk)
    lastN=Lng(N)-1
    # does lastN have a row1 parent in N?
    if not hasParent(N,1,lastN): f_haspar+=1; continue
    parval=entry(N,1,parent(N,1,lastN))
    if parval!=p: f_parval+=1; print("PARVAL FAIL",fmt(M),"p",p,"parval",parval)
    if eRs1kk<=0: f_eRs1kk_pos+=1
print("cases:",nc,"hasParent lastN fail:",f_haspar,"entry N 1 parent == p fail:",f_parval,"eRs1kk<=0:",f_eRs1kk_pos)
