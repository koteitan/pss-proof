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
# Use the ACTUAL N from wf15: prefix length based on entry Rs 1 0
nc=0; f_chain=0; f_e10=0
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
    if eRs10>0: N=diagSeq(0,eRs10-1)+Rs
    else: N=Rs
    if not (RedCondA(N) and RedCondB(N)): continue
    nc+=1
    eRs1kk=entry(Rs,1,kk)
    lastN=Lng(N)-1
    # the diagonal columns of N: index t has value (t,t) for t in 0..eRs10-1 (if eRs10>0)
    # the parent of lastN in row1
    if not hasParent(N,1,lastN):
        print("no par lastN", fmt(M)); continue
    q=parent(N,1,lastN)
    # chain: entry N 1 q +1 = entry N 1 lastN (RedCondA), entry N 1 lastN = eRs1kk, q==p, entry N 1 q == q
    lhs=entry(N,1,q)+1; rhs=entry(N,1,lastN)
    ok = (lhs==rhs) and (entry(N,1,lastN)==eRs1kk) and (q==p) and (entry(N,1,q)==q)
    if not ok:
        f_chain+=1
        print("CHAIN FAIL", fmt(M),"p",p,"eRs10",eRs10,"eRs1kk",eRs1kk,"q",q,"lastN",lastN,"eNq",entry(N,1,q),"N",fmt(N))
print("cases (RedCondA N holds, actual-N):", nc, "chain fails:", f_chain)
