#!/usr/bin/env python3
# FAST structural checks for the W2 WLOG-r=1 reduction (no Trans calls).
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s5/python')
from red_model import (Lng, entry, monoT, reduced, seg, parent, leR, Adm, adm,
                       nadm, oper, diagSeq, marked, nextR, nextrel1, le0)
import red_model as rm

def gen_pool(maxlen, maxn, maxseed, cap):
    seen=set(); frontier=[]
    for u in range(maxseed):
        for v in range(u,u+maxseed+2):
            M=tuple(diagSeq(u,v))
            if M not in seen: seen.add(M); frontier.append(list(M))
    pool=list(frontier)
    while frontier and len(pool)<cap:
        nxt=[]
        for M in frontier:
            if Lng(M)<=1: continue
            for n in range(1,maxn+1):
                N=oper(M,n)
                if Lng(N)>maxlen: continue
                t=tuple(N)
                if t not in seen: seen.add(t); nxt.append(N); pool.append(N)
                if len(pool)>=cap: break
            if len(pool)>=cap: break
        frontier=nxt
    return pool

def probe(hosts):
    segc=0; full=0; nadmloc=0; leR1=0; redmono=0
    admG1_bad=0    # in G=seg H (r-1) c, Adm G 1 should be 0 (since nadm G 1)
    entryloc=0     # nadm(M,j) == entry-local form (adjacency) sanity
    cases=0
    for H in hosts:
        if not (reduced(H) and monoT(H)): continue
        n=Lng(H)
        # entry-local form of nadm sanity check over all interior j
        for j in range(1,n-1):
            loc = (entry(H,1,j-1)<entry(H,1,j) and entry(H,0,j-1)<entry(H,0,j)
                   and entry(H,1,j)<entry(H,1,j+1) and entry(H,0,j)<entry(H,0,j+1))
            if loc != nadm(H,j): entryloc+=1
        for r in range(1,n-1):
            if adm(H,r): continue
            for c in range(r+1,n):
                cases+=1
                G=seg(H,r-1,c)
                k=Lng(G)-1
                if seg(G,1,k)!=seg(H,r,c): segc+=1
                if seg(G,0,k)!=G: full+=1
                if not nadm(G,1): nadmloc+=1
                if Adm(G,1)!=0: admG1_bad+=1
                if not (reduced(G) and monoT(G)): redmono+=1
                # leR H 0 r c (W1 needs it) -- check auto-implied
                if not leR(H,0,r,c): leR1+=1
    print(f"cases={cases}")
    print(f"seg-compose bad={segc}  full-slice bad={full}")
    print(f"nadm(G,1) fails={nadmloc}  Adm(G,1)!=0 ={admG1_bad}")
    print(f"seg H (r-1) c not reduced/mono={redmono}")
    print(f"leR H 0 r c fails (W1 leR auto)={leR1}")
    print(f"nadm entry-local mismatch (all interior j)={entryloc}")

if __name__=='__main__':
    pool=gen_pool(8,3,3,300)
    print("pool",len(pool))
    probe(pool)
