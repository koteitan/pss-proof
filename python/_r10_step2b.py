import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import Lng, entry, parent, oper, fmt
from trans_model import (Trans, Mark, Pred, ZB, Dpt, addBT, bpHeadV, bpHeadT,
                         flatBT, unflatBT, scb_decomps, Adm, condIII, condV, monoT)

HOSTS = [
 [(0,0),(1,1),(2,1)],            # condIII k=1
 [(0,0),(1,1),(2,2),(2,2)],      # condV k=2 (D_v leaf nesting)
 [(0,0),(1,1),(2,2)],            # condV-ish
 [(0,0),(1,1),(1,1),(2,2)],
 [(0,0),(1,1),(2,1),(2,1)],      # condV width2
 [(0,0),(1,1),(2,2),(3,1)],
 [(0,0),(1,1),(2,2),(3,3),(3,1)],
 [(0,0),(1,1),(2,2),(3,2)],
]

def acc(M):
    j1=Lng(M)-1
    if j1<=0 or not monoT(M): return None
    P=Pred(M); t1=Trans(P)
    if t1==ZB: return None
    jp=parent(M,0,j1); jm1=Adm(M,jp); c1=Mark(P,jm1)
    return dict(t1=t1,c1=c1,v=bpHeadV(c1),t2=bpHeadT(c1),u=entry(M,1,jm1))

def funpow(f,k,x):
    for _ in range(k): x=f(x)
    return x

for M in HOSTS:
    a=acc(M)
    cond='V' if condV(M) else ('III' if condIII(M) else '?')
    if a is None:
        print(fmt(M), cond, 'skip(no acc)'); continue
    u,v,t2,t1,c1=a['u'],a['v'],a['t2'],a['t1'],a['c1']
    ds1=scb_decomps(t1,flatBT(c1))
    body=addBT(t2,Dpt(v,ZB))
    ds0=scb_decomps(body,flatBT(Dpt(v,ZB)))
    if not ds1 or not ds0:
        print(fmt(M),cond,'skip(no scb)'); continue
    s1,b1=ds1[0]; s0,b0=ds0[0]
    OW=lambda x: unflatBT(s1+[('D',u)]+flatBT(x)+b1)
    C=lambda x: unflatBT(s0+[('D',v-1)]+flatBT(x)+b0)
    n1 = (Trans(oper(M,1))==OW(t2))
    T2=Trans(oper(M,2)); k=None
    for kk in (1,2,3):
        if OW(funpow(C,kk,t2))==T2: k=kk; break
    steps=[]
    if k is not None:
        for p in range(2,5):
            b=funpow(C,k+(p-2),t2)
            ok = (OW(b)==Trans(oper(M,p))) and (OW(C(b))==Trans(oper(M,p+1)))
            steps.append(ok)
    print(fmt(M),'cond',cond,'u',u,'v',v,'n1',n1,'k',k,'steps',steps)
