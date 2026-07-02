import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import Lng, entry, parent, oper, fmt
from trans_model import (Trans, Mark, Pred, ZB, Dpt, addBT, bpHeadV, bpHeadT,
                         flatBT, unflatBT, scb_decomps, Adm, condIII, condV, monoT)

def funpow(f,k,x):
    for _ in range(k): x=f(x)
    return x

for M in [[(0,0),(1,1),(2,1)], [(0,0),(1,1),(2,2),(2,2)]]:
    print('==== host', fmt(M))
    j1=Lng(M)-1; P=Pred(M); t1=Trans(P)
    jp=parent(M,0,j1); jm1=Adm(M,jp); c1=Mark(P,jm1)
    v=entry(M,1,Lng(M)-1); t2=bpHeadT(c1); u=entry(M,1,jm1)
    print('u',u,'v',v,'t2',t2)
    print('t1=Trans(Pred)=',t1)
    print('c1=',c1)
    ds1=scb_decomps(t1,flatBT(c1)); print('ds1 count',len(ds1))
    body=addBT(t2,Dpt(v,ZB))
    ds0=scb_decomps(body,flatBT(Dpt(v,ZB))); print('ds0 count',len(ds0))
    print('Trans(M[2])=',Trans(oper(M,2)))
    for i1,(s1,b1) in enumerate(ds1):
        for i0,(s0,b0) in enumerate(ds0):
            OW=lambda x,s1=s1,b1=b1: unflatBT(s1+[('D',u)]+flatBT(x)+b1)
            C=lambda x,s0=s0,b0=b0: unflatBT(s0+[('D',v-1)]+flatBT(x)+b0)
            for k in (1,2,3):
                try:
                    if OW(funpow(C,k,t2))==Trans(oper(M,2)):
                        print('  MATCH ds1[%d] ds0[%d] k=%d'%(i1,i0,k))
                except Exception as e:
                    pass
