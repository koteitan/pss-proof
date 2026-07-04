#!/usr/bin/env python3
# r38 E1GE deep validation.  ST_PS = oper-orbit of diagSeq seeds (inductive def
# pss_defs 439).  So BFS from diagSeq(u,v) under oper(.,n>=1) gives GENUINE ST_PS
# members (all reduced+standard by m_6_7).  Target host predicate:
#   monoT, hasParent1(j1), hasParent0(j1), condIII/IV, jm2<j0, jm2+1<L.
# E1GE: entry M 1 j1 <= entry M 1 (jm2+1).
# Ancestor branch le0(jm2+1,j1) is FREE; hunt the NON-ancestor branch DEEP.
# Track oper-DEPTH (# oper apps from a diag seed) and length; report non-anc
# counts by depth/length, esp. depth>=10 and length>=10.
import sys, time
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

def gen(seed_cap, maxlen, maxdepth, ncap, total_cap):
    # BFS keeping depth; returns list of (M_tuple, depth)
    seen=set(); out=[]
    frontier=[]
    for u in range(seed_cap):
        for v in range(u, seed_cap):
            M=tuple(diagSeq(u,v))
            if 1<Lng(M)<=maxlen and M not in seen:
                seen.add(M); frontier.append((M,0)); out.append((M,0))
    depth=0
    while frontier and depth<maxdepth and len(seen)<total_cap:
        nf=[]
        for (M,d) in frontier:
            Ml=list(M)
            for n in range(1,ncap+1):
                try: Mn=oper(Ml,n)
                except Exception: continue
                if 1<len(Mn)<=maxlen:
                    t=tuple(Mn)
                    if t not in seen:
                        seen.add(t); nf.append((t,d+1)); out.append((t,d+1))
                        if len(seen)>=total_cap: break
            if len(seen)>=total_cap: break
        frontier=nf; depth+=1
    return out

def run():
    seed_cap=int(sys.argv[1]) if len(sys.argv)>1 else 5
    maxlen  =int(sys.argv[2]) if len(sys.argv)>2 else 24
    maxdepth=int(sys.argv[3]) if len(sys.argv)>3 else 16
    ncap    =int(sys.argv[4]) if len(sys.argv)>4 else 6
    total_cap=int(sys.argv[5]) if len(sys.argv)>5 else 300000
    t0=time.time()
    corpus=gen(seed_cap,maxlen,maxdepth,ncap,total_cap)
    print("corpus",len(corpus),"t",round(time.time()-t0),"maxdepthReached",
          max(d for _,d in corpus),"maxlen",max(Lng(list(M)) for M,_ in corpus),flush=True)
    st={'host':0,'anc':0,'nonanc':0,'e1ge_pass':0,'e1ge_fail':0,
        'nonanc_pass':0,'nonanc_fail':0,'nonanc_deepD':0,'nonanc_deepL':0,
        'notreduced':0,'nonanc_examples':[]}
    fails=[]
    # track non-anc distribution
    nonanc_by_depth={}; nonanc_by_len={}
    for (Mt,d) in corpus:
        M=list(Mt); L=Lng(M); j1=L-1
        if L<3 or not (1<j1): continue
        if not monoT(M): continue
        if not reduced(M): st['notreduced']+=1; continue  # sanity: should be 0
        if not hasParent1(M,j1) or not hasParent0(M,j1): continue
        if not condIIIorIV(M): continue
        jm2=parent1(M,j1); j0=parent0(M,j1)
        if not (jm2<j0): continue
        if jm2+1>=L: continue
        st['host']+=1
        isanc=le0(M,jm2+1,j1)
        e1ge = entry(M,1,j1) <= entry(M,1,jm2+1)
        if isanc: st['anc']+=1
        else:
            st['nonanc']+=1
            nonanc_by_depth[d]=nonanc_by_depth.get(d,0)+1
            nonanc_by_len[L]=nonanc_by_len.get(L,0)+1
            if d>=10: st['nonanc_deepD']+=1
            if L>=10: st['nonanc_deepL']+=1
            if e1ge: st['nonanc_pass']+=1
            else:
                st['nonanc_fail']+=1
                if len(fails)<40: fails.append(('NONANC',fmt(M),'d',d,'jm2',jm2,'j0',j0,'j1',j1,
                    'e1',[entry(M,1,k) for k in range(L)]))
            if len(st['nonanc_examples'])<25:
                st['nonanc_examples'].append((fmt(M),'d',d,'L',L,'jm2',jm2,'j0',j0,
                    'e1_jm2+1',entry(M,1,jm2+1),'e1_j1',entry(M,1,j1),'e1ge',e1ge))
        if e1ge: st['e1ge_pass']+=1
        else: st['e1ge_fail']+=1
    print("host",st['host'],"anc",st['anc'],"nonanc",st['nonanc'],flush=True)
    print("E1GE overall pass",st['e1ge_pass'],"fail",st['e1ge_fail'],flush=True)
    print("E1GE NONANC pass",st['nonanc_pass'],"fail",st['nonanc_fail'],flush=True)
    print("nonanc deepD(>=10)",st['nonanc_deepD'],"deepL(len>=10)",st['nonanc_deepL'],flush=True)
    print("notreduced(sanity=0)",st['notreduced'],flush=True)
    print("nonanc_by_depth",dict(sorted(nonanc_by_depth.items())),flush=True)
    print("nonanc_by_len",dict(sorted(nonanc_by_len.items())),flush=True)
    for ex in st['nonanc_examples']: print("NONANC_EX",ex,flush=True)
    for f in fails: print("E1GE_CEX",f,flush=True)

run()
