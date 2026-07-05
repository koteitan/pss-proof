#!/usr/bin/env python3
"""r44 explore: characterize which ST_PS hosts give Trans M a multi-principal
body, and specifically hunt for the BRANCH-PREFIX config (second-to-last body
principal is a nested branch, qb != 0_B), equal-head or not.
"""
import sys, time, signal
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

def bfs(maxlen, tmax, umax=7, dmax=8):
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

def main():
    maxlen=int(sys.argv[1]) if len(sys.argv)>1 else 26
    tmax=int(sys.argv[2]) if len(sys.argv)>2 else 180
    stats={'pool':0,'multibody':0,'branch2ndlast':0,'branch_eqhead':0,
           'branch_eqhead_deep':0,'body3plus':0,'st_fail':0}
    examples=[]      # branch 2nd-last (any head)
    eqbr=[]          # branch + equal head
    maxbody=0
    for M in bfs(maxlen,tmax):
        stats['pool']+=1
        if not monoT(M): continue
        if Br(M)==[]: continue
        if not (Lng(M)-1>1): continue
        TM=safe(Trans,M,budget=6)
        if TM is None or len(TM[1])!=1: continue
        v0=entry(M,1,0)
        if TM[1][0][1]!=v0: continue
        body=bucOf(TM[1][0][2])
        maxbody=max(maxbody,len(body))
        if len(body)>=2:
            stats['multibody']+=1
            if len(body)>=3: stats['body3plus']+=1
            x,q=body[-1][1],body[-1][2]
            hdv,qb=body[-2][1],body[-2][2]
            if qb!=[]:                       # nested branch second-to-last
                stats['branch2ndlast']+=1
                if len(examples)<12: examples.append((list(M),Lng(M),bu.fmt([body[-2]]),bu.fmt([body[-1]])))
                if x==hdv:
                    stats['branch_eqhead']+=1
                    if Lng(M)>=14: stats['branch_eqhead_deep']+=1
                    leq=bu.le_term(q,qb)
                    if len(eqbr)<20: eqbr.append((list(M),Lng(M),bu.fmt(q),bu.fmt(qb),leq))
                    if not leq: stats['st_fail']+=1
    print('maxlen',maxlen,'stats:',stats,'maxbody',maxbody)
    print('\nbranch 2nd-last examples (M,Lng,2ndlast,last):')
    for e in examples: print('  ',e)
    print('\nBRANCH + EQUAL-HEAD (M,Lng,q,qb,leBT q qb):')
    for e in eqbr: print('  ',e)

if __name__=='__main__': main()
