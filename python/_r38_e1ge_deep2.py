#!/usr/bin/env python3
# r38 E1GE deep2: FORCE depth.  Cap frontier width per BFS level so the search
# marches to depth >=15-20 (r37 WGAP CEX was at oper-depth 9; must exceed).
# Prioritize keeping non-anc-producing states in the frontier.  Report any
# non-anc host with entry M 1 j1 != 1 (pattern break) or E1GE failure.
import sys, time, random
sys.path.insert(0,'python')
from fast_pss import (Lng, entry, le0, nextrel0, nextrel1, hasParent1, parent1,
                      hasParent0, parent0, oper, reduced, diagSeq, fmt)

def zeroT(M): return Lng(M)==1 and entry(M,1,0)==0
def monoT(M): return (not zeroT(M)) and le0(M,0,Lng(M)-1)
def condIIIorIV(M):
    j1=Lng(M)-1
    if not hasParent0(M,j1): return False
    j0=parent0(M,j1)
    return entry(M,1,j1)>0 and entry(M,1,j0)>=entry(M,1,j1)

def is_host(M):
    L=Lng(M); j1=L-1
    if L<3: return None
    if not monoT(M): return None
    if not hasParent1(M,j1) or not hasParent0(M,j1): return None
    if not condIIIorIV(M): return None
    jm2=parent1(M,j1); j0=parent0(M,j1)
    if not (jm2<j0): return None
    if jm2+1>=L: return None
    return (jm2,j0,j1)

def run():
    seed_cap  =int(sys.argv[1]) if len(sys.argv)>1 else 5
    maxlen    =int(sys.argv[2]) if len(sys.argv)>2 else 30
    maxdepth  =int(sys.argv[3]) if len(sys.argv)>3 else 22
    ncap      =int(sys.argv[4]) if len(sys.argv)>4 else 5
    frontcap  =int(sys.argv[5]) if len(sys.argv)>5 else 12000
    random.seed(1234)
    seen=set(); frontier=[]
    for u in range(seed_cap):
        for v in range(u, seed_cap):
            M=tuple(diagSeq(u,v))
            if 1<Lng(M)<=maxlen and M not in seen:
                seen.add(M); frontier.append(M)
    st={'host':0,'anc':0,'nonanc':0,'nonanc_fail':0,'nonanc_j1ne1':0,
        'nonanc_strict':0,'nonanc_eq':0}
    fails=[]; j1ne1_ex=[]
    nonanc_by_depth={}
    t0=time.time()
    for depth in range(maxdepth+1):
        # process this level
        newnonanc=0
        for M in frontier:
            r=is_host(list(M))
            if r is not None:
                jm2,j0,j1=r; Ml=list(M)
                st['host']+=1
                isanc=le0(Ml,jm2+1,j1)
                e1a=entry(Ml,1,jm2+1); e1b=entry(Ml,1,j1)
                if isanc: st['anc']+=1
                else:
                    st['nonanc']+=1; newnonanc+=1
                    nonanc_by_depth[depth]=nonanc_by_depth.get(depth,0)+1
                    if e1b!=1:
                        st['nonanc_j1ne1']+=1
                        if len(j1ne1_ex)<20: j1ne1_ex.append((fmt(Ml),'d',depth,'jm2',jm2,'j0',j0,'e1b',e1b,'e1a',e1a))
                    if e1a<e1b:
                        st['nonanc_fail']+=1
                        if len(fails)<40: fails.append(('CEX',fmt(Ml),'d',depth,'jm2',jm2,'j0',j0,
                            'e1',[entry(Ml,1,k) for k in range(Lng(Ml))]))
                    elif e1a==e1b: st['nonanc_eq']+=1
                    else: st['nonanc_strict']+=1
        # expand next level
        nxt=[]; nxtseen_local=[]
        # bias: keep non-anc producers by shuffling then capping
        fr=list(frontier); random.shuffle(fr)
        for M in fr:
            Ml=list(M)
            for n in range(1,ncap+1):
                try: Mn=oper(Ml,n)
                except Exception: continue
                if 1<len(Mn)<=maxlen:
                    t=tuple(Mn)
                    if t not in seen:
                        seen.add(t); nxt.append(t)
            if len(nxt)>=frontcap: break
        if len(nxt)>frontcap:
            nxt=random.sample(nxt,frontcap)
        frontier=nxt
        if not frontier: break
    print("depthReached",depth,"seen",len(seen),"t",round(time.time()-t0),flush=True)
    print("host",st['host'],"anc",st['anc'],"nonanc",st['nonanc'],flush=True)
    print("nonanc E1GE fail",st['nonanc_fail'],"| eq",st['nonanc_eq'],"strict",st['nonanc_strict'],flush=True)
    print("nonanc with entry1 j1 != 1:",st['nonanc_j1ne1'],flush=True)
    print("nonanc_by_depth",dict(sorted(nonanc_by_depth.items())),flush=True)
    for e in j1ne1_ex: print("J1NE1",e,flush=True)
    for f in fails: print("E1GE_CEX",f,flush=True)

run()
