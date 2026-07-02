import itertools, sys
from red_model import *

def npJ(M,J):
    b=Br(M); fn=FirstNodes(M)
    if entry(b[J],1,0)==0: return 0
    par=THE_nextR(M,1,fn[J])
    return par+1

def NJ(M,J):
    b=Br(M); jn=Joints(M); m00=entry(M,0,0); m10=entry(M,1,0)
    return [(m00+jn[J]+1, m10+npJ(M,J))]+b[J][1:]

def gen_cores(maxlen, maxval):
    seqs=[]
    for L in range(2,maxlen+1):
        for body in itertools.product(range(maxval+1), repeat=2*L):
            M=[(body[2*j],body[2*j+1]) for j in range(L)]
            if M[0]!=(0,0): continue
            if not (entry(M,0,0)==0 and entry(M,1,0)==0): continue
            try:
                if not monoT(M): continue
                if Red(M)!=M: continue
                if TrMax(M)==Lng(M)-1: continue
            except Exception:
                continue
            seqs.append(M)
    return seqs

def main():
    cores=gen_cores(4,3)
    print("reduced monoT nontrunk cores:", len(cores))
    nrow0=0; nrow1=0; fail0=0; fail1=0; crosstot=0
    examples0=[]; examples1=[]
    for M in cores:
        Jstar=len(Br(M))-1
        blks=[]
        for J in range(Jstar):
            np=npJ(M,J); jn=Joints(M)[J]; eJ=jn+1-np
            blks+=funpow(IncrFirst,eJ,Red(NJ(M,J)))
        off=1+TrMax(M)+len(blks)
        j1=Lng(M)-1
        for i in range(2):
            if not hasParent(M,i,j1): continue
            p=parent(M,i,j1)
            if p>=off: continue  # in-block; not our case
            crosstot+=1
            if i==0:
                nrow0+=1
                want_p = Joints(M)[Jstar]
                ok_p = (p==want_p)
                ok_e = (entry(M,0,j1)==entry(M,0,p)+1)
                if not (ok_p and ok_e):
                    fail0+=1
                    if len(examples0)<5: examples0.append((M,p,want_p,entry(M,0,j1),entry(M,0,p)))
            else:
                nrow1+=1
                ok_tr = (p<=TrMax(M))
                ok_ep = (entry(M,1,p)==p) if ok_tr else False
                ok_e = (entry(M,1,j1)==npJ(M,Jstar)) and (npJ(M,Jstar)==p+1)
                if not (ok_tr and ok_ep and ok_e):
                    fail1+=1
                    if len(examples1)<5: examples1.append((M,p,TrMax(M),entry(M,1,p),entry(M,1,j1),npJ(M,Jstar)))
    print(f"cross-block total: {crosstot}")
    print(f"row0 cross: {nrow0}  fail: {fail0}")
    print(f"row1 cross: {nrow1}  fail: {fail1}")
    if examples0: print("row0 fails:", examples0)
    if examples1: print("row1 fails:", examples1)

main()
