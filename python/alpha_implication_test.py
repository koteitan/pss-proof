#!/usr/bin/env python3
"""ROUTE-ALPHA: is the implication non-vacuous, and what exactly forces le0?

The reachable N are always reduced+core+condAB, so 'antecedent->le0' is vacuously
344/344. To break the circle we must show le0 N m10 jN follows from properties of
N PROVABLE without Red_le. Test on a BROAD class of pairseqs P (not just reachable
N) whether:

  candidate antecedent  =>  le0 P m10 jN   (for the relevant m10, jN=Lng-1)

so we learn which property is the genuine sufficient condition, and whether it can
fail (counterexample => that property alone is NOT enough; need more).

We enumerate all T_PS pairseqs (len<=L, val<=V) as candidate 'N', pick m10 = the
N10... but reachable N have N10=0. The article's monoT_Red wants le0 N m10 jN where
m10 = M_{1,0} of the ORIGINAL M, an arbitrary positive value. We sweep m10 over
1..Lng-1 and ask: for which (P,m10) does each antecedent hold, and does le0 hold?
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, zeroT, multiT, monoT, seg, fmt,
                       le0, le1, Red, hasParent, parent)

def all_pairseqs(maxlen, maxval):
    from itertools import product
    out=[]
    for n in range(1,maxlen+1):
        for cells in product(product(range(maxval+1),repeat=2),repeat=n):
            out.append([tuple(c) for c in cells])
    return out

def is_TPS(M):
    # faithful: nonempty, M_0=(0,0), and well-formed per red_model's T_PS check if present
    if len(M)==0: return False
    return M[0]==(0,0)

def RedCondA(M):
    n=Lng(M)
    for i in (0,1):
        for j in range(n):
            if hasParent(M,i,j) and entry(M,i,parent(M,i,j))+1!=entry(M,i,j):
                return False
    return True

def RedCondB(M):
    n=Lng(M)
    for j in range(n):
        if (not hasParent(M,0,j)) and entry(M,0,j)!=entry(M,1,j):
            return False
    return True

def coeff_r0lej(N):
    return all(entry(N,0,j)<=j for j in range(Lng(N)))

# Test: for a sequence N with entry N 0 0 ==0, entry N 1 0==0, monoT(N) (the whole N
# is mono - article: N's m10..jN slice; but the article actually has N possibly multi?)
# We restrict to the structurally relevant case the article uses.

cnt={}
def b(k): cnt[k]=cnt.get(k,0)+1
ex={}

if __name__=='__main__':
    L,V=(int(sys.argv[1]),int(sys.argv[2])) if len(sys.argv)>2 else (4,2)
    Ns=[N for N in all_pairseqs(L,V) if is_TPS(N)]
    print(f"# candidate N (len<=%d val<=%d, M0=(0,0)): {len(Ns)}"%(L,V))
    for N in Ns:
        n=Lng(N)
        if n<2: continue
        jN=n-1
        for m10 in range(1,n):  # the shift; reachable case m10<=jN
            le=le0(N,m10,jN)
            cA=RedCondA(N); cB=RedCondB(N)
            n00=(entry(N,0,0)==0); n10=(entry(N,1,0)==0)
            red=(Red(N)==N); r0=coeff_r0lej(N)
            sg=seg(N,m10,jN); mono_sg=monoT(sg) if len(sg)>0 else False
            b('total')
            if mono_sg==le: b('monoT_eq_le0')
            else: ex.setdefault('monoT!=le0',[]).append((fmt(N),m10,jN))
            # the article's TRUE precondition: (0,m10)<=_N(0,jN) <- monoT M with index shift.
            # Here we probe pure-N antecedents:
            for nm,pred in [('condA',cA),('condAB',cA and cB),
                            ('reduced',red),('core',n00 and n10),
                            ('coreA',n00 and n10 and cA),
                            ('coreAB',n00 and n10 and cA and cB),
                            ('r0lej',r0),('coreABr0',n00 and n10 and cA and cB and r0)]:
                if pred:
                    b(nm+'_h')
                    if le: b(nm+'_le')
                    else: ex.setdefault(nm+'_NOTle',[]).append((fmt(N),m10,jN))
    tot=cnt.get('total',0)
    print(f"# (N,m10) pairs: {tot}")
    print(f"monoT(seg)==le0 N m10 jN: {cnt.get('monoT_eq_le0',0)}/{tot}")
    print("antecedent: holds / of-which-le0 / FAIL(holds & not le0)")
    for nm in ['condA','condAB','reduced','core','coreA','coreAB','r0lej','coreABr0']:
        h=cnt.get(nm+'_h',0); le=cnt.get(nm+'_le',0)
        print(f"  {nm:9s}: holds={h:5d}  le0={le:5d}  FAIL={h-le}")
    print("=== FAIL examples (antecedent true but le0 false) ===")
    for k,v in ex.items():
        if k=='monoT!=le0': continue
        print(f"  {k}: {len(v)}")
        for e in v[:5]: print("     ",e)
    if 'monoT!=le0' in ex:
        print("  monoT!=le0 examples:", ex['monoT!=le0'][:5])
