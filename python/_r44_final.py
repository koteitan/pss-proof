#!/usr/bin/env python3
"""r44 FINAL slotTail falseness check.  Corpus SPECIFICALLY seeded to reach the
BRANCH-PREFIX equal-head config: (0,0) + k copies of a root-attached nested
block U, plus diagSeq(u,v) + the condV SEED_HOSTS, all closed under oper.
For every monoT host with Br!=[], Lng-1>1 whose Trans M has a WIDE outer body
(>=2 principals under D_v0), read off the tail decomposition and, in the
EQUAL-HEAD case (x==hdv), check leBT q qb (= slotTail conclusion).
Equal-head-branch (qb!=0) hits are yaBMS-verified to be genuine ST_PS.
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import Lng, entry, monoT, Br, diagSeq, oper, is_standard, fmt
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

# root-attached nested "unit" blocks U (each, as a root child, -> a nested principal)
UNITS = [
 [(1,1),(2,1)],
 [(1,1),(2,2),(2,1)],
 [(1,1),(2,2),(3,1),(4,2)],
 [(1,1),(2,2),(3,1),(4,2),(4,2)],
 [(1,1),(2,2),(3,3),(4,1),(5,2)],
 [(1,1),(2,1),(3,1)],
 [(1,1),(2,2),(2,1),(3,1)],
 [(1,1),(2,2),(3,2)],
 [(1,1),(2,2),(3,1),(4,3)],
]
def repeat_seed(U,k): return [(0,0)]+U*k
SEED_HOSTS=[
 [(0,0),(1,1),(2,2),(3,1),(4,2),(4,2)],
 [(0,0),(1,1),(2,2),(3,1),(4,0),(5,1),(6,2),(7,0),(6,2)],
]

def gen(maxlen,tmax,seeds):
    seen=set(); t0=time.time()
    starts=[diagSeq(u,u+d) for u in range(0,7) for d in range(1,7)]
    starts+=[list(x) for x in SEED_HOSTS]
    for U in UNITS:
        for k in (2,3,4):
            s=repeat_seed(U,k)
            if Lng(s)<=maxlen: starts.append(s)
    # BFS
    dq=deque()
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
            for _ in range(90):
                if time.time()-t0>tmax: return
                nn=rng.randrange(1,4)
                M2=safe(oper,M,nn,budget=2)
                if M2 is None or M2==M or Lng(M2)>maxlen: break
                M=M2; k=tuple(M)
                if k not in seen: seen.add(k); yield M

def main():
    maxlen=int(sys.argv[1]) if len(sys.argv)>1 else 22
    tmax=int(sys.argv[2]) if len(sys.argv)>2 else 200
    S={'pool':0,'monoDeep':0,'wide':0,'wide_deep':0,'eqhead':0,'eqhead_deep':0,
       'eqhead_branch':0,'eqhead_branch_deep':0,'eqhead_leaf':0,
       'st_pass':0,'st_fail':0,'std_checked':0,'std_ok':0}
    branchex=[]; failex=[]; std_samples=[]
    for M in gen(maxlen,tmax,list(range(1,16))):
        S['pool']+=1
        if not monoT(M) or Br(M)==[] or not(Lng(M)-1>1): continue
        S['monoDeep']+=1
        TM=safe(Trans,M,budget=6)
        if TM is None or len(TM[1])!=1 or TM[1][0][1]!=entry(M,1,0): continue
        body=bucOf(TM[1][0][2])
        if len(body)<2: continue
        S['wide']+=1
        deep=Lng(M)>=14
        if deep: S['wide_deep']+=1
        x,q=body[-1][1],body[-1][2]; hdv,qb=body[-2][1],body[-2][2]
        if x!=hdv: continue
        S['eqhead']+=1
        if deep: S['eqhead_deep']+=1
        branch=(qb!=[])
        if branch:
            S['eqhead_branch']+=1
            if deep: S['eqhead_branch_deep']+=1
        else:
            S['eqhead_leaf']+=1
        leq=bu.le_term(q,qb)
        if leq: S['st_pass']+=1
        else:
            S['st_fail']+=1
            failex.append((list(M),Lng(M),bu.fmt(q),bu.fmt(qb),branch))
        if branch and len(branchex)<40:
            branchex.append((list(M),Lng(M),bu.fmt(q),bu.fmt(qb),leq))
        # yaBMS-verify a sample of equal-head-branch hosts
        if branch and S['std_checked']<60:
            st=is_standard(M); S['std_checked']+=1
            if st: S['std_ok']+=1
            else: std_samples.append(('NONSTD',list(M)))
    print('maxlen',maxlen,'tmax',tmax)
    for k in ['pool','monoDeep','wide','wide_deep','eqhead','eqhead_deep',
              'eqhead_branch','eqhead_branch_deep','eqhead_leaf',
              'st_pass','st_fail','std_checked','std_ok']:
        print('  %-20s = %d'%(k,S[k]))
    print('\nEQUAL-HEAD BRANCH-PREFIX hosts (M,Lng,q,qb,leBT q qb)  [first 40]:')
    for e in branchex: print('  ',e)
    if failex:
        print('\n*** SLOTTAIL FAILURES (leBT q qb FALSE): ***')
        for e in failex[:25]: print('  ',e)
    else:
        print('\nNO SLOTTAIL FAILURES: leBT q qb held in EVERY equal-head instance.')
    if std_samples:
        print('\nNON-STANDARD hosts among branch sample (should be none):')
        for e in std_samples: print('  ',e)

if __name__=='__main__': main()
