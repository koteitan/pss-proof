#!/usr/bin/env python3
"""r33-OTLOCAL nadm: brute-force straddle to FIND condV-nadm and condIV hosts
(rare under random oper-BFS) and test the op0-tower-of-whole shape for them.
Uses a deep oper-BFS from many diagSeq seeds + explicit non-adm targeting.
"""
import sys, time, signal, random, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import (Lng, entry, parent, hasParent, oper, seg, diagSeq,
                       monoT, zeroT, P)
import red_model as rm
from trans_model import (Trans, Mark, Pred, adm, Adm, condI, condIII, condV,
                         condVI, Dpt, addBT, PB, bpHeadV, bpHeadT, flatBT,
                         scb_decomps, ZB, reduced)
import buchholz as bu

INF = float('inf')
class TimeoutErr(Exception): pass
def _handler(s,f): raise TimeoutErr()
signal.signal(signal.SIGALRM,_handler)
def safe(f,*a,budget=4):
    signal.alarm(budget)
    try:
        r=f(*a); signal.alarm(0); return r
    except (TimeoutErr,RecursionError,AssertionError,ValueError,IndexError):
        signal.alarm(0); return None

def numBT(n): return ('T',[('D',0,ZB)]*n)
def numNat(z): return len(z[1])
def multBT(a,n):
    o=ZB
    for _ in range(n): o=addBT(o,a)
    return o
def domB(a):
    ps=a[1]
    if not ps: return 'EMPTY'
    if len(ps)==1:
        _,v,b=ps[0]
        if b==ZB:
            if v==0: return 'ZERO'
            if v==INF: return 'NAT'
            return ('TB',v-1)
        db=domB(b)
        if db=='ZERO': return 'NAT'
        if isinstance(db,tuple) and db[0]=='TB' and v<=db[1]: return 'NAT'
        return db
    return domB(('T',[ps[-1]]))
def operB(a,z):
    ps=a[1]
    if not ps: return ZB
    if len(ps)==1:
        _,v,b=ps[0]
        if b==ZB:
            if v==0: return ZB
            if v==INF: return Dpt(numNat(z)+1,ZB)
            return z
        db=domB(b)
        if db=='ZERO': return multBT(Dpt(v,operB(b,ZB)),numNat(z)+1)
        if isinstance(db,tuple) and db[0]=='TB' and v<=db[1]:
            return Dpt(v,xseq(b,db[1],numNat(z)))
        return Dpt(v,operB(b,z))
    return addBT(('T',ps[:-1]),operB(('T',[ps[-1]]),z))
def xseq(b,u,i):
    if i==0: return Dpt(u,ZB)
    return operB(b,Dpt(u,xseq(b,u,i-1)))
def op0(a): return operB(a,numBT(0))
def bucOf(t): return [('D',p[1],bucOf(p[2])) for p in t[1]]
def isOT(t): return bu.in_OT(bucOf(t))

def condIV(M):
    j1=Lng(M)-1; jp=parent(M,0,j1)
    return entry(M,1,j1)>0 and entry(M,1,jp)>=entry(M,1,j1) and not adm(M,jp)
def condVnadm(M):
    j1=Lng(M)-1; jp=parent(M,0,j1)
    return condV(M) and not adm(M,jp)

def op0tower_hit(TM,TMn,n,mmax=8,KMAX=16):
    for m in range(0,n+mmax+1):
        t=safe(operB,TM,numBT(m))
        if t is None: continue
        for k in range(KMAX+1):
            if t==TMn: return (m-n,k)
            t=safe(op0,t)
            if t is None: break
    return None

def bfs_hosts(seeds_lim=5, maxlen=18, steps=14, nmax=5, budget_s=200):
    t0=time.time()
    seen=set()
    stack=[]
    for u in range(0,seeds_lim):
        for dv in range(1,seeds_lim+1):
            stack.append(diagSeq(u,u+dv))
    rng=random.Random(99)
    frontier=list(stack)
    while frontier and time.time()-t0<budget_s:
        M=frontier.pop()
        key=tuple(M)
        if key in seen: continue
        seen.add(key)
        if 1<Lng(M)<=maxlen:
            yield M
        if Lng(M)>maxlen: continue
        for nn in range(1,nmax+1):
            M2=safe(oper,M,nn,budget=1)
            if M2 is not None and tuple(M2) not in seen and Lng(M2)<=maxlen+3:
                frontier.append(M2)
        rng.shuffle(frontier)

def main():
    budget=int(sys.argv[1]) if len(sys.argv)>1 else 200
    res={'condIV':{'hit':{},'none':0,'tot':0},
         'condVnadm':{'hit':{},'none':0,'tot':0}}
    examples={'condIV':[], 'condVnadm':[]}
    for M in bfs_hosts(budget_s=budget):
        if not monoT(M): continue
        j1=Lng(M)-1
        if j1<=1: continue
        for tag,c in (('condIV',condIV),('condVnadm',condVnadm)):
            if not c(M): continue
            if safe(reduced,M) is not True: continue
            TM=safe(Trans,M,budget=5)
            if TM is None: continue
            if len(examples[tag])<3: examples[tag].append(list(M))
            for n in (1,2,3,4):
                Mn=safe(oper,M,n,budget=2)
                if Mn is None or Mn==M: continue
                TMn=safe(Trans,Mn,budget=6)
                if TMn is None: continue
                res[tag]['tot']+=1
                h=op0tower_hit(TM,TMn,n)
                if h is None: res[tag]['none']+=1
                else: res[tag]['hit'][h]=res[tag]['hit'].get(h,0)+1
    for tag in res:
        r=res[tag]
        top=sorted(r['hit'].items(),key=lambda x:-x[1])[:8]
        print('%-12s tot=%3d none=%3d  %s' % (tag,r['tot'],r['none'],top))
        print('   examples:', examples[tag][:3])

if __name__=='__main__':
    main()
