#!/usr/bin/env python3
"""r44 explore2: dump EVERY multi-principal-body monoT host and hunt branch-prefix.
Generators: (a) length-BFS for breadth, (b) deep single-chain orbits (repeated
oper n=1..3) which reach high Lng cheaply for depth.
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import Lng, entry, monoT, multiT, Br, diagSeq, oper
import red_model as rm
from trans_model import Trans, Pred
import buchholz as bu
from collections import deque

class TO(Exception): pass
def h(s,f): raise TO()
signal.signal(signal.SIGALRM,h)
def safe(f,*a,budget=6):
    signal.alarm(budget)
    try:
        r=f(*a); signal.alarm(0); return r
    except (TO,RecursionError,AssertionError,ValueError,IndexError,KeyError,RuntimeError):
        signal.alarm(0); return None

def bucOf(t): return [('D',p[1],bucOf(p[2])) for p in t[1]]

def hosts_bfs(maxlen,tmax,umax=7,dmax=8):
    seen=set(); dq=deque(); t0=time.time()
    for u in range(umax):
        for d in range(1,dmax):
            s=diagSeq(u,u+d); k=tuple(s)
            if k not in seen: seen.add(k); dq.append(s); yield s
    while dq and time.time()-t0<tmax:
        M=dq.popleft()
        for nn in range(1,4):
            M2=safe(oper,M,nn,budget=2)
            if M2 is None or M2==M or Lng(M2)>maxlen: continue
            k=tuple(M2)
            if k not in seen: seen.add(k); dq.append(M2); yield M2

def hosts_deepchain(maxlen,tmax,seeds):
    seen=set(); t0=time.time()
    for sd in seeds:
        rng=random.Random(sd)
        for u in range(0,7):
            for d in range(1,8):
                M=diagSeq(u,u+d)
                for _ in range(60):
                    if time.time()-t0>tmax: return
                    nn=rng.randrange(1,4)
                    M2=safe(oper,M,nn,budget=2)
                    if M2 is None or M2==M or Lng(M2)>maxlen: break
                    M=M2; k=tuple(M)
                    if k not in seen: seen.add(k); yield M

def scan(gen, tag, stats, mbex, brex):
    for M in gen:
        stats['pool']+=1
        if not monoT(M): continue
        if Br(M)==[]: continue
        if not (Lng(M)-1>1): continue
        TM=safe(Trans,M,budget=6)
        if TM is None or len(TM[1])!=1: continue
        if TM[1][0][1]!=entry(M,1,0): continue
        body=bucOf(TM[1][0][2])
        if len(body)>=2:
            stats['multibody']+=1
            if len(mbex)<25:
                mbex.append((tag,list(M),Lng(M),bu.fmt(body)))
            x,q=body[-1][1],body[-1][2]; hdv,qb=body[-2][1],body[-2][2]
            if qb!=[]:
                stats['branch2ndlast']+=1
                if x==hdv:
                    stats['branch_eqhead']+=1
                    leq=bu.le_term(q,qb)
                    brex.append((tag,list(M),Lng(M),bu.fmt(q),bu.fmt(qb),leq))
                    if not leq: stats['st_fail']+=1

def main():
    maxlen=int(sys.argv[1]) if len(sys.argv)>1 else 30
    tmax=int(sys.argv[2]) if len(sys.argv)>2 else 200
    stats={'pool':0,'multibody':0,'branch2ndlast':0,'branch_eqhead':0,'st_fail':0}
    mbex=[]; brex=[]
    half=tmax//2
    scan(hosts_bfs(maxlen,half), 'bfs', stats, mbex, brex)
    scan(hosts_deepchain(maxlen,tmax-half,[1,2,3,4,5,6,7,8,9,10]), 'chain', stats, mbex, brex)
    print('maxlen',maxlen,'stats:',stats)
    print('\nMULTIBODY hosts (tag,M,Lng,Trans-body):')
    for e in mbex: print('  ',e)
    print('\nBRANCH+EQUALHEAD (tag,M,Lng,q,qb,leBT):')
    for e in brex[:30]: print('  ',e)
    if stats['st_fail']==0:
        print('\nNO slotTail failure in equal-head branch-prefix cases.')

if __name__=='__main__': main()
