#!/usr/bin/env python3
# r29a-ATOMS: U2 refined variants.
#  (U2a) any two FAR children c<c' of the SAME p (any p): entry M 1 c == entry M 1 c'
#  (U2b) same but only for non-adm p
#  (U2c) full column equality for far children of same p: M!c == M!c'
#  (U2d) far child of non-adm p: entry M 1 c >= entry M 1 p  (lower bound probe)
#  (U2e) far child c of non-adm p: entry M 1 c in {entry M 1 p, entry M 1 p + 1}
import sys, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-f7/python')
from red_model import (Lng, entry, monoT, zeroT, seg, adm, oper, diagSeq, parent,
                       Adm, Pred, fmt, hasParent)

def gen(ml,mn,ms,cap):
    seen=set();fr=[];pool=[]
    for u in range(ms):
        for v in range(u,u+ms+4):
            M=tuple(diagSeq(u,v))
            if M not in seen: seen.add(M);fr.append(list(M));pool.append(list(M))
    while fr and len(pool)<cap:
        nx=[]
        for M in fr:
            if Lng(M)<=1: continue
            for n in range(1,mn+1):
                N=oper(M,n)
                if Lng(N)>ml: continue
                t=tuple(N)
                if t not in seen: seen.add(t);nx.append(N);pool.append(N)
                if len(pool)>=cap: break
            if len(pool)>=cap: break
        fr=nx
    return pool

def run(ml,cap,budget,mn):
    pool=gen(ml,mn,4,cap)
    print(f"pool {len(pool)} mn {mn} maxLng {ml}",flush=True)
    t0=time.time()
    stats={'U2a':0,'U2b':0,'U2c':0,'U2d':0,'U2e':0,'U1':0}
    fails={k:[] for k in stats}
    pairs=0; farnadm=0; nh=0
    for M in pool:
        if time.time()-t0>budget:
            print("BUDGET HIT",flush=True); break
        nh+=1
        L=Lng(M)
        kids={}  # p -> list of far children
        for c in range(1,L):
            if not hasParent(M,0,c): continue
            p=parent(M,0,c)
            if p+1>=c: continue
            kids.setdefault(p,[]).append(c)
            if not adm(M,p+1):
                stats['U1']+=1; fails['U1'].append((fmt(M),c,p))
            if not adm(M,p):
                farnadm+=1
                if not (entry(M,1,c)>=entry(M,1,p)):
                    stats['U2d']+=1; fails['U2d'].append((fmt(M),c,p))
                if entry(M,1,c) not in (entry(M,1,p),entry(M,1,p)+1):
                    stats['U2e']+=1; fails['U2e'].append((fmt(M),c,p,entry(M,1,c),entry(M,1,p)))
        for p,cs in kids.items():
            if len(cs)<2: continue
            for i in range(len(cs)-1):
                c,c2=cs[i],cs[i+1]
                pairs+=1
                if entry(M,1,c)!=entry(M,1,c2):
                    stats['U2a']+=1; fails['U2a'].append((fmt(M),p,c,c2))
                    if not adm(M,p):
                        stats['U2b']+=1; fails['U2b'].append((fmt(M),p,c,c2))
                if M[c]!=M[c2]:
                    stats['U2c']+=1; fails['U2c'].append((fmt(M),p,c,c2,M[c],M[c2]))
    print(f"hosts {nh}; far-sibling pairs {pairs}; far@nadm {farnadm}")
    for k in stats:
        print(f"  {k}: fails={stats[k]}")
        for f in fails[k][:5]: print("     CEX",f)

if __name__=='__main__':
    run(int(sys.argv[1]) if len(sys.argv)>1 else 13,
        int(sys.argv[2]) if len(sys.argv)>2 else 30000,
        int(sys.argv[3]) if len(sys.argv)>3 else 480,
        int(sys.argv[4]) if len(sys.argv)>4 else 9)
