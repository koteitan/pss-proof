#!/usr/bin/env python3
"""r44 widebody: dump EVERY monoT ST_PS host whose Trans M has a WIDE outer
body (>=2 principals directly under D_v0) -- these are the ONLY hosts where
slotTail (ps != []) fires.  Classify each: last-two heads equal? 2nd-last
nested (branch-prefix)?  Check leBT q qb.  Broad generators: length-BFS +
deep oper-chains from diagSeq(u,v) AND the condV/III/IV SEED_HOSTS.
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import Lng, entry, monoT, Br, diagSeq, oper
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

SEED_HOSTS=[
 [(0,0),(1,1),(2,2),(3,1),(4,2),(4,2)],
 [(0,0),(1,1),(2,2),(3,1),(4,0),(5,1),(6,2),(7,0),(6,2)],
 [(0,0),(1,1),(2,2),(3,3),(4,1),(5,2)],
 [(0,0),(1,1),(2,2),(3,2),(4,1),(5,2)],
 [(0,0),(1,1),(2,2),(3,1),(4,3)],
 [(0,0),(1,0),(1,0),(1,0)],
 [(0,0),(1,1),(2,1),(3,1)],
 [(0,0),(1,1),(2,0),(1,0)],
 [(0,0),(1,1),(2,2),(3,0),(1,0)],
]
def gen(maxlen,tmax,seeds):
    seen=set(); t0=time.time()
    # length-BFS
    dq=deque()
    starts=[diagSeq(u,u+d) for u in range(0,7) for d in range(1,8)]+[list(x) for x in SEED_HOSTS]
    for s in starts:
        k=tuple(s)
        if k not in seen: seen.add(k); dq.append(s); yield s
    tb=t0+tmax*0.5
    while dq and time.time()<tb:
        M=dq.popleft()
        for nn in range(1,4):
            M2=safe(oper,M,nn,budget=2)
            if M2 is None or M2==M or Lng(M2)>maxlen: continue
            k=tuple(M2)
            if k not in seen: seen.add(k); dq.append(M2); yield M2
    # deep chains
    for sd in seeds:
        if time.time()-t0>tmax: return
        rng=random.Random(sd)
        for s in starts:
            M=list(s)
            for _ in range(80):
                if time.time()-t0>tmax: return
                nn=rng.randrange(1,4)
                M2=safe(oper,M,nn,budget=2)
                if M2 is None or M2==M or Lng(M2)>maxlen: break
                M=M2; k=tuple(M)
                if k not in seen: seen.add(k); yield M

def main():
    maxlen=int(sys.argv[1]) if len(sys.argv)>1 else 24
    tmax=int(sys.argv[2]) if len(sys.argv)>2 else 200
    stats={'pool':0,'monoDeep':0,'wide':0,'wide_eqhead':0,'wide_eqhead_branch':0,
           'st_fail':0,'wide_deep':0}
    wideex=[]; branchex=[]; failex=[]
    for M in gen(maxlen,tmax,[1,2,3,4,5,6,7,8,9,10,11,12]):
        stats['pool']+=1
        if not monoT(M) or Br(M)==[] or not(Lng(M)-1>1): continue
        stats['monoDeep']+=1
        TM=safe(Trans,M,budget=6)
        if TM is None or len(TM[1])!=1 or TM[1][0][1]!=entry(M,1,0): continue
        body=bucOf(TM[1][0][2])
        if len(body)<2: continue
        stats['wide']+=1
        if Lng(M)>=14: stats['wide_deep']+=1
        if len(wideex)<40: wideex.append((list(M),Lng(M),bu.fmt(body)))
        x,q=body[-1][1],body[-1][2]; hdv,qb=body[-2][1],body[-2][2]
        if x==hdv:
            stats['wide_eqhead']+=1
            leq=bu.le_term(q,qb)
            if qb!=[]:
                stats['wide_eqhead_branch']+=1
                if len(branchex)<30: branchex.append((list(M),Lng(M),bu.fmt(q),bu.fmt(qb),leq))
            if not leq:
                stats['st_fail']+=1
                failex.append((list(M),Lng(M),bu.fmt(q),bu.fmt(qb),qb!=[]))
    print('maxlen',maxlen,'stats:',stats)
    print('\nWIDE outer-body hosts (M,Lng,body)  [first 40]:')
    for e in wideex: print('  ',e)
    print('\nWIDE + EQUAL-HEAD + BRANCH-PREFIX (M,Lng,q,qb,leBT):')
    for e in branchex: print('  ',e)
    if failex:
        print('\n*** SLOTTAIL FAILURES (leBT q qb FALSE): ***')
        for e in failex[:20]: print('  ',e)
    else:
        print('\nNO slotTail failures (leBT q qb held in all wide equal-head cases).')

if __name__=='__main__': main()
