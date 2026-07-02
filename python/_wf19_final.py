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
nc=0; f_resid=0; f_concl=0
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
    lastN=Lng(N)-1
    # RESIDUAL hypothesis (parent-value pin):
    resid = hasParent(N,1,lastN) and (entry(N,1,parent(N,1,lastN))==p)
    if not resid: f_resid+=1
    # CONCLUSION via the proof: RedCondA N => entry N1 par +1 = entry N1 lastN;
    #   entry N1 par = p, entry N1 lastN = eRs1kk  => eRs1kk = p+1 = Suc p
    par=parent(N,1,lastN)
    derived = entry(N,1,par)+1
    target = entry(N,1,lastN)
    # so valpin: entry Rs 1 kk == Suc p
    ok = (derived==target) and (entry(N,1,par)==p) and (entry(N,1,lastN)==eRs1kk) and (eRs1kk==p+1)
    if not ok: f_concl+=1
print("cases:",nc,"residual(parent-value pin) fails:",f_resid,"conclusion-chain fails:",f_concl)
