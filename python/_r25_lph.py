#!/usr/bin/env python3
# r25-LPH: validate lph = "last principal head of transT2 M = entry M 1 (transJ1 M)"
# under condV, plus the intermediate algebraic chain via terminal slice S / RightAnces.
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-f7/python')
from red_model import (Lng, entry, monoT, reduced, seg, adm, oper, diagSeq,
                       parent, Adm, Pred, zeroT, P)
import red_model as rm
from trans_model import (Trans, Mark, bpHeadT, bpHeadV, Dpt, PB, ZB, flatBT)

def transJ1(M): return Lng(M)-1
def transJ0(M): return parent(M,0,transJ1(M))
def transJm1(M): return Adm(M, transJ0(M))
def transC1(M): return Mark(Pred(M), transJm1(M))
def transT2(M): return bpHeadT(transC1(M))

def RightNodes(t):
    xs = t[1]
    if not xs: return []
    u = xs[-1][1]; a = xs[-1][2]
    return [u] + RightNodes(a)

def RightAnces(M, depth=0):
    if depth>200: raise RecursionError
    if not reduced(M): return RightAnces(rm.Red(M), depth+1)
    j1 = Lng(M)-1
    if j1==0:
        return [] if M[0]==(0,0) else [entry(M,1,0)]
    if monoT(M):
        if zeroT(Pred(M)): return [0, entry(M,1,j1)]
        jp = parent(M,0,j1); jm1 = Adm(M,jp)
        a = [0] if zeroT(seg(M,0,jm1)) else RightAnces(seg(M,0,jm1), depth+1)
        from trans_model import condI, condIII, condV, condVI
        if condI(M) or condIII(M) or condV(M) or condVI(M):
            return a + [entry(M,1,j1)]
        return a + [entry(M,1,jp), entry(M,1,j1)]
    J1 = len(P(M))-1; PJ = P(M)[J1]
    if PJ==[(0,0)]: return [0]
    return RightAnces(PJ, depth+1)

from trans_model import condV as condVfun

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

from functools import lru_cache
@lru_cache(maxsize=None)
def _red_cached(t): return reduced(list(t))
def redM(M): return _red_cached(tuple(M))

def run(pool, budget=280, maxhosts=300):
    t0=time.time()
    tot=0; lph_ok=0; lph_bad=[]
    t2zero=0
    # chain checks
    c1_single=0; c1_eq_TransS=0; c1_neq=[]
    ra_ok=0; ra_bad=[]
    rn_shift_ok=0
    sharp_ok=0; sharp_bad=[]
    for M in pool:
        if time.time()-t0>budget or tot>=maxhosts: break
        if not (monoT(M) and redM(M)): continue
        if parent(M,0,Lng(M)-1) is None: continue
        try:
            if not condVfun(M): continue
        except Exception:
            continue
        # need t1 != 0 branch to be the surgery case
        try:
            if Trans(Pred(M))==ZB: continue
        except Exception:
            continue
        try:
            c1 = transC1(M); t2 = bpHeadT(c1)
        except Exception:
            continue
        if t2==ZB:
            t2zero+=1; continue
        tot+=1
        j1 = transJ1(M); j0 = transJ0(M); jm1 = transJm1(M)
        RHS = entry(M,1,j1)
        # LHS: last principal head of t2
        Pt2 = PB(t2)
        LHS = bpHeadV(Pt2[len(Pt2)-1])
        if LHS==RHS: lph_ok+=1
        else: lph_bad.append((M, LHS, RHS))
        # chain: c1 single principal?
        if len(c1[1])==1: c1_single+=1
        # RightNodes shift: RN(c1)[1]==RN(t2)[0]==LHS
        rnc1 = RightNodes(c1); rnt2 = RightNodes(t2)
        if len(rnc1)>=2 and len(rnt2)>=1 and rnc1[1]==rnt2[0]==LHS: rn_shift_ok+=1
        # terminal slice S
        S = seg(M, jm1, Lng(M)-2)
        try:
            TS = Trans(S)
        except Exception:
            TS = None
        if TS is not None and TS==c1: c1_eq_TransS+=1
        else: c1_neq.append((M, jm1))
        try:
            raS = RightAnces(S)
        except Exception:
            raS = None
        if raS is not None and len(raS)>=2 and raS[1]==RHS: ra_ok+=1
        elif raS is not None: ra_bad.append((M, raS, RHS))
        # sharpened: LHS == entry M 1 (j0+1)
        if j0+1 <= Lng(M)-1:
            if LHS==entry(M,1,j0+1): sharp_ok+=1
            else: sharp_bad.append((M, LHS, entry(M,1,j0+1)))
    print(f"condV surgery hosts (t2!=0): tot={tot}  (t2==0 skipped={t2zero})")
    print(f"  lph LHS==RHS : {lph_ok}/{tot}   bad={len(lph_bad)}")
    for b in lph_bad[:5]: print("    LPH CEX", b)
    print(f"  c1 single principal : {c1_single}/{tot}")
    print(f"  RN shift RN(c1)[1]==RN(t2)[0]==LHS : {rn_shift_ok}/{tot}")
    print(f"  c1 == Trans(S) [S terminal slice] : {c1_eq_TransS}/{tot}  neq={len(c1_neq)}")
    for b in c1_neq[:5]: print("    c1!=TransS", b)
    print(f"  RightAnces(S)[1]==RHS : {ra_ok}/{tot}  bad={len(ra_bad)}")
    for b in ra_bad[:5]: print("    RA CEX", b)
    print(f"  sharp LHS==entry M 1 (j0+1) : {sharp_ok}/{tot}  bad={len(sharp_bad)}")
    for b in sharp_bad[:5]: print("    SHARP CEX", b)

if __name__=='__main__':
    ml = int(sys.argv[1]) if len(sys.argv)>1 else 12
    cap = int(sys.argv[2]) if len(sys.argv)>2 else 6000
    seed = int(sys.argv[3]) if len(sys.argv)>3 else 2
    pool = gen_pool(ml, 6, seed, cap)
    print("pool", len(pool), flush=True)
    run(pool, budget=520, maxhosts=1000)
