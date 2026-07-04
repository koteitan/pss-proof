#!/usr/bin/env python3
"""r35-OTDEEP focused validation: find witnesses of EACH leg via BFS, then check
Trans(N[m]) in OT_B for m in 2..NMAX on each witness + its oper orbit.  Streams
results (flush) so partial output survives a kill; prints a COUNT per leg."""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import (Lng, entry, parent, oper, seg, diagSeq, monoT, P)
from trans_model import (Trans, Pred, adm, condIII, condV, ZB)
import buchholz as bu

class TO(Exception): pass
def _h(s,f): raise TO()
signal.signal(signal.SIGALRM,_h)
def safe(f,*a,budget=5):
    signal.alarm(budget)
    try:
        r=f(*a); signal.alarm(0); return r
    except (TO,RecursionError,AssertionError,ValueError,IndexError,KeyError):
        signal.alarm(0); return None
def _b(t): return [('D',p[1],_b(p[2])) for p in t[1]]
def isOT(t):
    b=_b(t); return bu.in_OT(b) and bu.in_TB(b)
def condII(M):
    j1=Lng(M)-1; jp=parent(M,0,j1); return entry(M,1,j1)==0 and not adm(M,jp)
def condIV(M):
    j1=Lng(M)-1; jp=parent(M,0,j1)
    return entry(M,1,j1)>0 and entry(M,1,jp)>=entry(M,1,j1) and not adm(M,jp)
def leg_of(M):
    if not monoT(M): return None
    j1=Lng(M)-1
    if j1<=1: return None
    jp=parent(M,0,j1)
    if condIII(M): return 'otIII'
    if condIV(M): return 'otIV'
    if condV(M):
        if not adm(M,jp): return 'otVnadm'
        return 'otVadmDeep' if entry(M,1,jp)!=0 else 'otVadm_e0'
    return None

def bfs_hosts(tmax, maxlen=24):
    """BFS oper from many diag seeds, collect hosts per leg."""
    from collections import deque, defaultdict
    seen=set(); pools=defaultdict(list)
    seeds=[diagSeq(u,u+d) for u in range(0,6) for d in range(1,7)]
    seeds+= [[(0,0),(1,1),(2,2),(3,1),(4,2),(4,2)],
             [(0,0),(1,1),(2,2),(3,1),(4,0),(5,1),(6,2),(7,0),(6,2)]]
    dq=deque(seeds); t0=time.time()
    while dq and time.time()-t0<tmax:
        M=dq.popleft(); key=tuple(M)
        if key in seen or Lng(M)>maxlen: continue
        seen.add(key)
        lg=leg_of(M)
        if lg and lg!='otVadm_e0' and len(pools[lg])<60:
            pools[lg].append(M)
        for n in range(1,5):
            M2=safe(oper,M,n,budget=1)
            if M2 and M2!=M and tuple(M2) not in seen and Lng(M2)<=maxlen:
                dq.append(M2)
    return pools

def main():
    tmax=int(sys.argv[1]) if len(sys.argv)>1 else 180
    NMAX=int(sys.argv[2]) if len(sys.argv)>2 else 6
    print('BFS collecting witnesses...',flush=True)
    pools=bfs_hosts(tmax*0.5)
    for lg in ['otIII','otIV','otVnadm','otVadmDeep']:
        print('  found %-11s hosts: %d' % (lg,len(pools.get(lg,[]))),flush=True)
    from collections import defaultdict
    stat=defaultdict(lambda:[0,0,0,0])  # tot,pass,deep_tot,deep_pass
    fails=[]
    for lg in ['otIII','otIV','otVnadm','otVadmDeep']:
        for M in pools.get(lg,[]):
            TM=safe(Trans,M,budget=6)
            if TM is None: continue
            deep=Lng(M)>=10
            for m in range(2,NMAX+1):
                Mn=safe(oper,M,m,budget=3)
                if Mn is None or Mn==M or Lng(Mn)==Lng(M): continue
                TMn=safe(Trans,Mn,budget=8)
                if TMn is None: continue
                ok=safe(isOT,TMn,budget=5)
                if ok is None: continue
                s=stat[lg]; s[0]+=1
                if ok: s[1]+=1
                else: fails.append((lg,list(M),m,Lng(M)))
                if deep:
                    s[2]+=1
                    if ok: s[3]+=1
        s=stat[lg]
        print('  %-11s %4d/%-4d pass  deep %d/%d' % (lg,s[1],s[0],s[3],s[2]),flush=True)
    print('TOTAL FAILURES:',len(fails),flush=True)
    for f in fails[:10]: print('  CEX',f,flush=True)

if __name__=='__main__':
    main()
