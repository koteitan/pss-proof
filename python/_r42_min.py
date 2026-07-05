#!/usr/bin/env python3
"""r42 MINIMAL validation: 2 small r32-seed tuples, non-admeq condIV hosts,
structure split + exchange triple. Fast."""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _r28_c4dx_producer as V
from red_model import Lng, entry, monoT, zeroT, hasParent, parent, fmt, reduced, oper
from trans_model import Adm
from _r15_vx_lib import Trans, operB, numBT, lessBT, guarded, SKIP
def pr(*a): print(*a, flush=True)
def jm2f(M): return parent(M,1,Lng(M)-1)
def j0f(M): return parent(M,0,Lng(M)-1)
def G(f,*a,b=25): return guarded(f,*a,budget=b)
t0=time.time()
pool=[]
for seed,mlen,cap,ns,um,vx in ((11,11,1200,(1,2,3),4,8),(37,12,1200,(1,2,3),5,9),(29,13,1200,(1,2),6,10)):
    pool += V.gen_oper(mlen,cap,seed,ns,um,vx)
pr(f'pool {len(pool)} gen_t={time.time()-t0:.0f}s')
nonad=[]; adm_n=0; nseen=set(); hosts=0
for M in pool:
    L=Lng(M); j1=L-1
    if not(1<j1) or not monoT(M) or zeroT(M): continue
    if not hasParent(M,1,j1) or not reduced(M) or not V.condIV(M): continue
    jm2=jm2f(M); j0=j0f(M)
    if jm2 is None: continue
    jm3=Adm(M,jm2); jm1=Adm(M,j0); hosts+=1
    if jm3==jm1: adm_n+=1
    else:
        t=tuple(M)
        if t not in nseen: nseen.add(t); nonad.append(M)
pr(f'condIV hosts {hosts} admeq {adm_n} nonadmeq {len(nonad)} t={time.time()-t0:.0f}s')
eqv=lt=gtv=0
for M in nonad:
    j1=Lng(M)-1; jm1=Adm(M,j0f(M)); v1=entry(M,1,j1); e=entry(M,1,jm1)
    if e==v1: eqv+=1
    elif e<v1: lt+=1
    else: gtv+=1
pr(f'e1[transJm1] vs v1: ==v1 {eqv} <v1 {lt} >v1 {gtv}')
for M in sorted(nonad,key=lambda x:Lng(x))[:10]:
    j1=Lng(M)-1; jm2=jm2f(M); j0=j0f(M); jm3=Adm(M,jm2); jm1=Adm(M,j0)
    pr(f'  {fmt(M)}|v1={entry(M,1,j1)} jm2={jm2} j0={j0} jm3={jm3} jm1={jm1} e1jm1={entry(M,1,jm1)}')
C=[[0,0],[0,0],[0,0]]; cex=[None,None,None]; sk=0
for M in nonad:
    TM=G(Trans,M,b=20)
    if TM is SKIP: sk+=1; continue
    for n in (1,2,3):
        Mn=G(oper,M,n,b=10); Mn1=G(oper,M,n+1,b=10)
        if Mn is SKIP or Mn1 is SKIP: sk+=1; continue
        TMn=G(Trans,Mn,b=20); TMn1=G(Trans,Mn1,b=20)
        if TMn is SKIP or TMn1 is SKIP: sk+=1; continue
        oN=G(operB,TM,numBT(n),b=10); oNm1=G(operB,TM,numBT(n-1),b=10)
        if oN is SKIP or oNm1 is SKIP: sk+=1; continue
        cc=[lessBT(TMn,oN),lessBT(TMn,TM),lessBT(oNm1,TMn1)]
        for i in range(3):
            C[i][0]+=cc[i]; C[i][1]+=1
            if not cc[i] and cex[i] is None: cex[i]=(fmt(M),n)
pr(f'CONJ1 {C[0][0]}/{C[0][1]} CONJ2 {C[1][0]}/{C[1][1]} CONJ3 {C[2][0]}/{C[2][1]} skip {sk}')
pr(f'CEX {cex}  total {time.time()-t0:.0f}s')
