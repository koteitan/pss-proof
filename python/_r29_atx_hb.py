#!/usr/bin/env python3
# r29a-ATOMS: article-faithful notLD route for the NON-adm condV case.
# Validate on genuine hosts (ST∩PT, condV, ~adm j0; t2 != 0 automatic):
#  (H1) pin: Trans(seg M jm1 j1) == transC2 M == Dpt(e1jm1, t2 + Dpt(e1j1) 0)
#  (H2) HB : every c in PB(t2) satisfies Dpt(e1j1) 0 <=_B c
#  (H3) notLD: bpHeadV(last PB(t2)) != e1j0   (head >= e1j1 = e1j0+1)
#  (H4) slice basics: Br(RN) nonempty, FirstNodes!last = Lng RN - 1, DIAG there
# plus straddle: (H2) fails on RT\ST hosts? (sanity: standardness load-bearing)
import sys, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-f7/python')
from red_model import (Lng, entry, monoT, zeroT, seg, adm, oper, diagSeq, parent,
                       Adm, Pred, fmt, hasParent, Red, Br, FirstNodes, Joints, TrMax)
from trans_model import (reduced, condV, Trans, Mark, bpHeadT, bpHeadV, ZB, PB, Dpt,
                         addBT)

def lessBT(a,b):
    pa,pb=a[1],b[1]
    if not pa: return bool(pb)
    if not pb: return False
    if lessBP(pa[0],pb[0]): return True
    if pa[0]==pb[0]: return lessBT(('T',pa[1:]),('T',pb[1:]))
    return False
def lessBP(p,q):
    (_,u,a),(_,v,b)=p,q
    return u<v or (u==v and lessBT(a,b))
def leBT(a,b): return lessBT(a,b) or a==b

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

def genuine(M):
    if not (reduced(M) and monoT(M)): return None
    if Lng(M)<3: return None
    j1=Lng(M)-1
    if not hasParent(M,0,j1): return None
    jp=parent(M,0,j1)
    if not condV(M): return None
    if adm(M,jp): return None
    return (Adm(M,jp),jp,j1)

def run(ml,cap,budget,mn):
    pool=gen(ml,mn,4,cap)
    print(f"pool {len(pool)} mn {mn} maxLng {ml}",flush=True)
    t0=time.time()
    tot=0;deep=0;errs=[];t2z=0
    for M in pool:
        if time.time()-t0>budget:
            print("BUDGET HIT",flush=True); break
        g=genuine(M)
        if g is None: continue
        jm1,j0,j1=g; tot+=1
        if Lng(M)>=9: deep+=1
        c1=Mark(Pred(M),jm1)
        t2=bpHeadT(c1)
        if t2==ZB:
            t2z+=1; errs.append(('T2Z',fmt(M))); continue
        e1jm1=entry(M,1,jm1); e1j0=entry(M,1,j0); e1j1=entry(M,1,j1)
        c2exp=Dpt(e1jm1, addBT(t2, Dpt(e1j1,ZB)))
        N=seg(M,jm1,j1); RN=Red(N)
        # H1
        if Trans(RN)!=c2exp: errs.append(('H1a',fmt(M)))
        if Trans(N)!=c2exp: errs.append(('H1b',fmt(M)))
        if Mark(M,jm1)!=c2exp: errs.append(('H1c',fmt(M)))
        # H2
        thr=Dpt(e1j1,ZB)
        for c in PB(t2):
            if not leBT(thr,c): errs.append(('H2',fmt(M),c)); break
        # H3
        lastp=PB(t2)[-1]
        if bpHeadV(lastp)==e1j0: errs.append(('H3',fmt(M)))
        if not bpHeadV(lastp)>=e1j1: errs.append(('H3b',fmt(M),bpHeadV(lastp),e1j1))
        # H4
        br=Br(RN); fn=FirstNodes(RN)
        if not br: errs.append(('H4a',fmt(M)))
        else:
            fl=fn[len(br)-1]
            if fl!=Lng(RN)-1: errs.append(('H4b',fmt(M),fl))
            if entry(RN,0,fl)!=entry(RN,1,fl): errs.append(('H4c',fmt(M)))
            jl=Joints(RN)[len(br)-1]
            if jl!=j0-jm1: errs.append(('H4d',fmt(M),jl,j0-jm1))
            if not (0<j0-jm1<TrMax(RN)): errs.append(('H4e',fmt(M)))
    print(f"genuine {tot} (deep {deep}), t2zero {t2z}, errors {len(errs)}")
    for e in errs[:10]: print("  ERR",e)

if __name__=='__main__':
    run(int(sys.argv[1]) if len(sys.argv)>1 else 13,
        int(sys.argv[2]) if len(sys.argv)>2 else 30000,
        int(sys.argv[3]) if len(sys.argv)>3 else 480,
        int(sys.argv[4]) if len(sys.argv)>4 else 9)
