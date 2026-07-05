#!/usr/bin/env python3
"""r42 LEAN validation: direct oper closure (no SIGALRM in gen), focused diagonal
seeds, collect non-admeq condIV hosts, structure split (e1jm1 vs v1), exchange triple."""
import sys, os, time, signal
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, monoT, zeroT, hasParent, parent, seg, fmt,
                       reduced, oper, diagSeq)
from trans_model import Adm, adm
from _r15_vx_lib import Trans, operB, numBT, lessBT, condIV

def pr(*a): print(*a, flush=True)
def s84x_jm2(M): return parent(M, 1, Lng(M) - 1)
def transJ0(M): return parent(M, 0, Lng(M) - 1)

class TO(Exception): pass
def _al(s,f): raise TO()
signal.signal(signal.SIGALRM, _al)
def G(f,*a,b=20):
    signal.alarm(b)
    try: r=f(*a); signal.alarm(0); return r
    except (TO,RecursionError,RuntimeError): signal.alarm(0); return None
    finally: signal.alarm(0)

def main():
    t0=time.time()
    seen=set(); pool=[]
    for u in range(9):
        for v in range(u, u+4):
            M=tuple(diagSeq(u,v))
            if M not in seen: seen.add(M); pool.append(list(M))
    # 3 levels of direct oper closure (small hosts -> fast)
    maxlen=15
    for _ in range(3):
        new=[]
        for M in list(pool):
            if Lng(M)<=1 or Lng(M)>maxlen: continue
            for n in (1,2,3):
                try: N=oper(M,n)
                except Exception: continue
                if Lng(N)>maxlen: continue
                t=tuple(N)
                if t not in seen: seen.add(t); new.append(N)
        pool+=new
    pr(f'pool {len(pool)} gen_t={time.time()-t0:.0f}s')

    nonad=[]; adm_n=0; nseen=set()
    for M in pool:
        L=Lng(M); j1=L-1
        if not(1<j1) or not monoT(M) or zeroT(M): continue
        if not hasParent(M,1,j1) or not reduced(M) or not condIV(M): continue
        jm2=s84x_jm2(M); j0=transJ0(M)
        if jm2 is None: continue
        jm3=Adm(M,jm2); jm1=Adm(M,j0)
        if jm3==jm1: adm_n+=1
        else:
            t=tuple(M)
            if t not in nseen: nseen.add(t); nonad.append(M)
    pr(f'condIV: admeq {adm_n} nonadmeq {len(nonad)} t={time.time()-t0:.0f}s')

    eqv=lt=gt=0; jm2ltj0=0; jm3ltjm1=0; jm2_eq_jm3=0
    for M in nonad:
        L=Lng(M); j1=L-1
        jm2=s84x_jm2(M); j0=transJ0(M); jm3=Adm(M,jm2); jm1=Adm(M,j0)
        v1=entry(M,1,j1); e=entry(M,1,jm1)
        if e==v1: eqv+=1
        elif e<v1: lt+=1
        else: gt+=1
        if jm2<j0: jm2ltj0+=1
        if jm3<jm1: jm3ltjm1+=1
        if jm2==jm3: jm2_eq_jm3+=1
    pr(f'struct: jm2<j0 {jm2ltj0}/{len(nonad)} jm3<jm1 {jm3ltjm1}/{len(nonad)} jm2==jm3 {jm2_eq_jm3}/{len(nonad)}')
    pr(f'e1[transJm1] vs v1: ==v1 {eqv}  <v1 {lt}  >v1 {gt}')
    for M in sorted(nonad,key=lambda x:Lng(x))[:15]:
        L=Lng(M); j1=L-1
        jm2=s84x_jm2(M); j0=transJ0(M); jm3=Adm(M,jm2); jm1=Adm(M,j0)
        pr(f'  {fmt(M)} | v1={entry(M,1,j1)} jm2={jm2} j0={j0} jm3={jm3} jm1={jm1} '
           f'e1jm1={entry(M,1,jm1)} e1jm2={entry(M,1,jm2)}')

    C=[[0,0],[0,0],[0,0]]; cex=[None,None,None]; sk=0
    for M in nonad:
        TM=G(Trans,M,b=25)
        if TM is None: sk+=1; continue
        for n in (1,2,3):
            try: Mn=oper(M,n); Mn1=oper(M,n+1)
            except Exception: sk+=1; continue
            TMn=G(Trans,Mn,b=25); TMn1=G(Trans,Mn1,b=25)
            if TMn is None or TMn1 is None: sk+=1; continue
            oN=G(operB,TM,numBT(n),b=15); oNm1=G(operB,TM,numBT(n-1),b=15)
            if oN is None or oNm1 is None: sk+=1; continue
            cc=[lessBT(TMn,oN), lessBT(TMn,TM), lessBT(oNm1,TMn1)]
            for i in range(3):
                C[i][0]+=cc[i]; C[i][1]+=1
                if not cc[i] and cex[i] is None: cex[i]=(fmt(M),n)
    pr(f'CONJ1(Trans M[n]<operB(TM,n)) {C[0][0]}/{C[0][1]}')
    pr(f'CONJ2(Trans M[n]<Trans M)     {C[1][0]}/{C[1][1]}')
    pr(f'CONJ3(operB(TM,n-1)<Trans M[n+1]) {C[2][0]}/{C[2][1]}')
    pr(f'CEX {cex} skip {sk}')
    pr(f'total {time.time()-t0:.0f}s')

if __name__=='__main__': main()
