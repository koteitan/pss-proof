#!/usr/bin/env python3
"""r16b-E5: focused non-adm condV exchange-shape harness (streams output).
Mines genuine ST_PS non-adm condV hosts (Lng>=9) and answers, per n:
  E2  : lessBT(Trans(M[n]), Trans M)                 (descent (2))
  minK: least k with leBT(Trans(M[n]), operB(Trans M)(numBT k))
  s@k : lessBT(Trans(M[n]), operB(Trans M)(numBT k)) STRICT at k=minK, k=n+1, k=n
  jm1 : transJm1 (=Adm(M,j0)) vs j0
Also dumps c1/c2/Trans(M[1]) scb-string shapes for the first few hosts.
"""
import sys, time, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt2/python')
from _r15_vx_lib import (Trans, Mark, operB, numBT, lessBT, leBT, guarded, SKIP,
                         internals, ZB, Dpt, PB, flatBT)
from red_model import Lng, entry, parent, oper, diagSeq, monoT
import red_model as rm
import trans_model as tm
from trans_model import adm, Adm, condV, Pred

def mine(tmax, rng, want=30):
    t0 = time.time(); seen=set(); out=[]
    while time.time()-t0 < tmax and len(out) < want:
        u = rng.randrange(0,6); vv=u+rng.randrange(1,7); M=diagSeq(u,vv)
        for _ in range(rng.randrange(6,34)):
            if time.time()-t0>tmax: break
            n=rng.choice((1,1,1,2,2,2,2,3,4))
            M2=guarded(oper,M,n,budget=2)
            if M2 is SKIP or M2 is None or M2==M or Lng(M2)>24: break
            M=M2; key=tuple(M)
            if key in seen: continue
            seen.add(key)
            j1=Lng(M)-1
            if j1<=1 or not monoT(M) or not condV(M): continue
            j0=parent(M,0,j1)
            if not adm(M,j0) and Lng(M)>=9:
                out.append(list(M))
    return [list(t) for t in dict.fromkeys(tuple(m) for m in out)]

def main():
    tmine=float(sys.argv[1]) if len(sys.argv)>1 else 90
    seed=int(sys.argv[2]) if len(sys.argv)>2 else 777
    rng=random.Random(seed)
    hosts=mine(tmine,rng)
    print('mined non-adm condV (Lng>=9):', len(hosts), flush=True)
    stat={}
    def add(k,ok):
        p,t=stat.get(k,(0,0)); stat[k]=(p+(1 if ok else 0),t+1)
    minKhist={}
    dumped=0
    for M in hosts:
        j1=Lng(M)-1; j0=parent(M,0,j1); jm1=Adm(M,j0)
        TM=guarded(Trans,M,budget=25)
        if TM is SKIP or TM is None: continue
        ii=internals(M)
        if dumped<4 and ii is not None:
            print('HOST', M, 'j0=%d jm1=%d j1=%d'%(j0,jm1,j1),
                  'M1: j0=%d jm1=%d j1=%d'%(entry(M,1,j0),entry(M,1,jm1),entry(M,1,j1)),
                  flush=True)
            print('  t2=',ii['t2'],' v=',ii['v'],' c2=',ii['c2'],flush=True)
            T1=guarded(Trans,Pred(M),budget=25)
            print('  Trans(M[1])=Trans(Pred M)=',T1,flush=True)
            print('  Trans M=',TM,flush=True)
            dumped+=1
        add('jm1<j0', jm1<j0)
        for n in (1,2,3,4):
            Mn=guarded(oper,M,n,budget=2)
            if Mn is SKIP or Mn is None: break
            TMn=guarded(Trans,Mn,budget=25)
            if TMn is SKIP or TMn is None: break
            add('E2 desc n=%d'%n, lessBT(TMn,TM))
            mink=None
            FScache={}
            for k in range(0,n+5):
                FSk=guarded(operB,TM,numBT(k),budget=15)
                FScache[k]=FSk
                if FSk is SKIP or FSk is None: break
                if leBT(TMn,FSk): mink=k; break
            if mink is None:
                add('minK<=n+4 n=%d'%n,False); continue
            add('minK<=n+4 n=%d'%n,True)
            minKhist[(n,mink)]=minKhist.get((n,mink),0)+1
            add('minK==n+1 n=%d'%n, mink==n+1)
            # strictness at minK
            FSmk=FScache.get(mink)
            if FSmk is not None and FSmk is not SKIP:
                add('strict@minK n=%d'%n, lessBT(TMn,FSmk))
            # at k=n+1
            FSn1=guarded(operB,TM,numBT(n+1),budget=15)
            if FSn1 is not None and FSn1 is not SKIP:
                add('le@n+1 n=%d'%n, leBT(TMn,FSn1))
                add('strict@n+1 n=%d'%n, lessBT(TMn,FSn1))
            # at k=n
            FSn=guarded(operB,TM,numBT(n),budget=15)
            if FSn is not None and FSn is not SKIP:
                add('le@n n=%d'%n, leBT(TMn,FSn))
    print('--- tally (non-adm condV, Lng>=9) ---',flush=True)
    for k in sorted(stat):
        p,t=stat[k]; print('  %-20s %d/%d%s'%(k,p,t,'' if p==t else '  <== NOT ALL'),flush=True)
    print('  minK histogram {(n,minK):count}:',minKhist,flush=True)

if __name__=='__main__':
    main()
