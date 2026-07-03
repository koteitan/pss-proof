import itertools, sys
from red_model import *
exec(open('_wf19_valpin.py').read().split('def main')[0].split('import itertools, sys\nfrom red_model import *\n')[1])

# re-run but only report the 3 RedCondA-N-fail cases and verify that
# WHEN RedCondA N holds, the goal chain (q+1=eRs1kk via RedCondA N at lastN) holds.
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
viaN_fail=0; nholds=0
for M in cores:
    Jstar=len(Br(M))-1
    j1=Lng(M)-1
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
    eRs1kk=entry(Rs,1,kk)
    if eRs1kk>0: N=diagSeq(0,eRs1kk-1)+Rs
    else: N=Rs
    rcaN = RedCondA(N)
    if not rcaN:
        print("RedCondA N FALSE:", fmt(M), "p=",p,"eRs1kk=",eRs1kk, "N=",fmt(N))
        continue
    nholds+=1
    # the proof path: RedCondA N at lastN, parent = q = eRs1kk-1, entry N 1 q = q
    lastN=Lng(N)-1
    if not hasParent(N,1,lastN):
        print("N lastN no row1 parent!", fmt(M)); continue
    q=parent(N,1,lastN)
    # RedCondA N => entry N 1 q +1 = entry N 1 lastN
    lhs=entry(N,1,q)+1; rhs=entry(N,1,lastN)
    # entry N 1 lastN = entry Rs 1 kk (tail), entry N 1 q = q
    if not (lhs==rhs and entry(N,1,lastN)==eRs1kk and q==p):
        viaN_fail+=1
        print("VIA-N CHAIN FAIL", fmt(M), q, p, lhs, rhs, eRs1kk)
print("cases where RedCondA N holds:", nholds, " via-N chain fails:", viaN_fail)
