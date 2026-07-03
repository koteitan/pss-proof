#!/usr/bin/env python3
r"""r21-BPSTEPB: explore the BASE case j1'=j1 of the cfbx back-peel.
For regime hosts with FirstNodes!(Lng(Br)-1) == Lng-1 (last branch single
column), inspect Trans(N), Trans(seg N m j1), their bpHeadT, and whether VE'
is seen via a NON-inductive relation (slice vs N structure)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm, trans_model as tm
from red_model import (Lng, entry, monoT, zeroT, diagSeq, parent, oper, seg,
                       Br, Joints, FirstNodes, TrMax, Red, fmt)
from trans_model import Trans, Mark, Pred, bpHeadT, bpHeadV, reduced, adm

def pr(*a): print(*a, flush=True)

def descending(br):
    n = len(br)
    for J0 in range(n):
        for J1 in range(J0, n):
            a0,a1 = entry(br[J0],0,0), entry(br[J0],1,0)
            b0,b1 = entry(br[J1],0,0), entry(br[J1],1,0)
            if not (a0>=b0 and (a0!=b0 or a1>=b1)): return False
    return True

def regime(M, m):
    br = Br(M)
    if not br: return False
    j1=Lng(M)-1; J1=len(br)-1
    j0p=Joints(M)[J1]; j1p=FirstNodes(M)[J1]
    if m > j1-1: return False
    if m < j0p: return True
    return (m==j0p and entry(M,0,j1p)==entry(M,1,j1p) and descending(br))

def host(M):
    if Lng(M)<3 or zeroT(M) or not monoT(M): return False
    if not reduced(M): return False
    return Br(M)!=[]

def gen_pool(maxlen, maxn, maxseed, cap):
    seen=set(); fr=[]
    for u in range(maxseed):
        for v in range(u,u+maxseed+2):
            M=tuple(diagSeq(u,v))
            if M not in seen: seen.add(M); fr.append(list(M))
    pool=list(fr)
    while fr and len(pool)<cap:
        nx=[]
        for M in fr:
            if Lng(M)<=1: continue
            for n in range(1,maxn+1):
                try: N=oper(M,n)
                except (ValueError,IndexError): continue
                if Lng(N)>maxlen: continue
                t=tuple(N)
                if t not in seen: seen.add(t); nx.append(N); pool.append(N)
                if len(pool)>=cap: break
            if len(pool)>=cap: break
        fr=nx
    return pool

def fmtBT(t):
    ps=t[1]
    if not ps: return '0'
    def fbp(p):
        v,sub=p[1],p[2]
        s=fmtBT(sub)
        return f"D{v}[{s}]" if s!='0' else f"D{v}"
    if len(ps)==1: return fbp(ps[0])
    return "("+"+".join(fbp(p) for p in ps)+")"

def main():
    pool=gen_pool(7,3,5,900)+gen_pool(9,2,6,900)
    seen=set(); nbase=0; nbad=0; shown=0
    # count how BASE splits by number of branches / m relative to j0'
    stats={'1br':0,'multibr':0,'m_eq_j0':0,'m_lt_j0':0,'m0':0,'slice_eq_lastcol_diag':0}
    for M in pool:
        t=tuple(M)
        if t in seen: continue
        seen.add(t)
        if not host(M): continue
        j1=Lng(M)-1; br=Br(M); J1=len(br)-1
        j0p=Joints(M)[J1]; j1p=FirstNodes(M)[J1]
        if j1p != j1: continue  # BASE: j1'=j1
        for m in range(0, min(j0p,j1-1)+1):
            if not regime(M,m): continue
            nbase+=1
            stats['1br']+= (len(br)==1)
            stats['multibr']+= (len(br)>1)
            stats['m_eq_j0']+= (m==j0p)
            stats['m_lt_j0']+= (m<j0p)
            stats['m0']+= (m==0)
            try:
                TN=Trans(list(M)); Tp=Trans(seg(M,m,j1))
                tN=bpHeadT(TN); tp=bpHeadT(Tp)
            except Exception: continue
            ve=(tN==tp)
            if not ve: nbad+=1
            # Is the deep tail of N equal to the deep tail of the slice down to j1-1?
            # explore: relate Trans(seg N m (j1-1)) i.e. drop last column
            if shown<14 and m>0 and len(br)>1:
                shown+=1
                pr("M=",fmt(M)," m=",m," j0'=",j0p," j1'=j1=",j1," #br=",len(br))
                pr("   TransN =",fmtBT(TN))
                pr("   TransM'=",fmtBT(Tp))
                pr("   bpHeadT eq?",ve)
    pr("BASE cases:",nbase," VE fails:",nbad)
    pr("stats:",stats)

if __name__=='__main__':
    main()
