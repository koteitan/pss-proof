#!/usr/bin/env python3
# r29a-ATOMS: validate the unified invariant INV-U on the FULL standard corpus.
# INV-U(M): for every c < Lng M with a row-0 parent p = parent M 0 c and p+1 < c
#   (FAR attach):
#   (U1) adm M (p+1)
#   (U2) if not adm M p then entry M 1 c = entry M 1 p + 1
# Also derive: INV-U + guards ==> atomA & atomB (re-check the derivation on the
# genuine hosts), and brute-force RT straddle (expect U1/U2 failures off ST).
import sys, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-f7/python')
from red_model import (Lng, entry, monoT, zeroT, seg, adm, oper, diagSeq, parent,
                       Adm, Pred, fmt, hasParent, Red)
from trans_model import reduced, condV, Trans, Mark, bpHeadT, ZB

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

def check_invu(M):
    """return list of (tag, c, p) violations"""
    L=Lng(M); errs=[]
    for c in range(1,L):
        if not hasParent(M,0,c): continue
        p=parent(M,0,c)
        if p+1>=c: continue
        # far attach
        if not adm(M,p+1):
            errs.append(('U1',c,p))
        if not adm(M,p):
            if entry(M,1,c)!=entry(M,1,p)+1:
                errs.append(('U2',c,p,entry(M,1,c),entry(M,1,p)))
    return errs

def genuine(M):
    if not (reduced(M) and monoT(M)): return None
    if Lng(M)<3: return None
    j1=Lng(M)-1
    if not hasParent(M,0,j1): return None
    jp=parent(M,0,j1)
    if not condV(M): return None
    if adm(M,jp): return None
    if Trans(Pred(M))==ZB: return None
    jm1=Adm(M,jp)
    c1=Mark(Pred(M),jm1)
    if bpHeadT(c1)==ZB: return None
    return (jm1,jp,j1)

def run(ml,cap,budget,mn):
    pool=gen(ml,mn,4,cap)
    print(f"pool {len(pool)} mn {mn} maxLng {ml}",flush=True)
    t0=time.time()
    nfar=0; nfarnadm=0; bad=[]; nhosts=0; deep=0; gen_hosts=0; atom_bad=[]
    for M in pool:
        if time.time()-t0>budget:
            print("BUDGET HIT",flush=True); break
        nhosts+=1
        if Lng(M)>=10: deep+=1
        errs=check_invu(M)
        if errs: bad.append((fmt(M),errs))
        # far-attach instance counting
        L=Lng(M)
        for c in range(1,L):
            if hasParent(M,0,c):
                p=parent(M,0,c)
                if p+1<c:
                    nfar+=1
                    if not adm(M,p): nfarnadm+=1
        # atomA/atomB direct re-check on genuine hosts (derivation sanity)
        g=genuine(M)
        if g is not None:
            gen_hosts+=1
            jm1,j0,j1=g
            if not adm(M,j0+1): atom_bad.append(('A',fmt(M)))
            for c in range(j0+1,L):
                if not hasParent(M,0,c): continue
                pj=parent(M,0,c)
                if jm1<=pj<=j0:
                    if not (pj==j0 and entry(M,1,c)==entry(M,1,j0)+1):
                        atom_bad.append(('B',fmt(M),c,pj))
    print(f"hosts checked {nhosts} (deep Lng>=10: {deep}); far-attach instances {nfar} (at non-adm p: {nfarnadm})")
    print(f"genuine hosts {gen_hosts}; atom violations {len(atom_bad)}")
    for a in atom_bad[:5]: print("  ATOM CEX",a)
    print(f"INV-U violations: {len(bad)}")
    for b in bad[:10]: print("  CEX",b)
    return len(bad)==0

def brute_rt(maxL,maxE):
    """brute-force RT hosts (all entries<=maxE, Lng<=maxL), count INV-U failures
       and whether the failing hosts are outside the ST pool (straddle check)."""
    import itertools
    stpool={tuple(x) for x in gen(maxL+1,6,4,20000)}
    nrt=0; nfail=0; fails=[]
    cols=[(a,b) for a in range(maxE+1) for b in range(maxE+1)]
    for L in range(3,maxL+1):
        for Mt in itertools.product(cols,repeat=L):
            M=list(Mt)
            if not reduced(M): continue
            nrt+=1
            errs=check_invu(M)
            if errs:
                nfail+=1
                if len(fails)<8: fails.append((fmt(M),errs[:2],tuple(Mt) in stpool))
    print(f"brute RT hosts {nrt}, INV-U failures {nfail}")
    for f in fails: print("  RTfail",f,"(in ST pool?" ,f[2],")")

if __name__=='__main__':
    mode=sys.argv[1] if len(sys.argv)>1 else 'st'
    if mode=='st':
        run(int(sys.argv[2]) if len(sys.argv)>2 else 13,
            int(sys.argv[3]) if len(sys.argv)>3 else 30000,
            int(sys.argv[4]) if len(sys.argv)>4 else 480,
            int(sys.argv[5]) if len(sys.argv)>5 else 9)
    else:
        brute_rt(int(sys.argv[2]) if len(sys.argv)>2 else 5,
                 int(sys.argv[3]) if len(sys.argv)>3 else 3)
