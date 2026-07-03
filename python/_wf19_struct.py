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
f=[0]*8
names=["q<=d (q in diag prefix)","entry N 1 q = q","entry N 1 lastN = eRs1kk",
       "nextR N 1 q lastN","entry N 0 q < entry N 0 lastN? (le0 dir)","le0 N q lastN",
       "q = eRs1kk-1","entry N 1 q < entry N 1 lastN"]
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
    if eRs10==0: continue  # need diag prefix; check this never happens
    d=eRs10-1
    N=diagSeq(0,d)+Rs
    if not (RedCondA(N) and RedCondB(N)): continue
    nc+=1
    lastN=Lng(N)-1
    q=eRs1kk-1
    if not (q<=d): f[0]+=1
    if entry(N,1,q)!=q: f[1]+=1
    if entry(N,1,lastN)!=eRs1kk: f[2]+=1
    if not nextR(N,1,q,lastN): f[3]+=1
    if not (entry(N,0,q)<entry(N,0,lastN)): f[4]+=1
    if not le0(N,q,lastN): f[5]+=1
    if parent(N,1,lastN)!=q: f[6]+=1
    if not (entry(N,1,q)<entry(N,1,lastN)): f[7]+=1
print("cases:",nc)
for n,c in zip(names,f): print(f"  {n}: fail {c}")
# also: does eRs10==0 ever happen in our cross-block kk>0 cases?
