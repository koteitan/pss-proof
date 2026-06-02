#!/usr/bin/env python3
"""ROUTE-ALPHA empirical test: can monoT(seg N m10 jN) (dead-branch[20]
unreachability) be derived A4-independently from coefficient structure of N,
WITHOUT Red_le?

At every m10>0 Red sub-call, with N = Red(diagSeq 0 (m10-1) @ IncrFirst^m10 M),
jN = Lng N -1, sg = seg N m10 jN, we test a chain of candidate implications:

  H_monoT  : monoT(sg)                    (= the goal p_6_5_monoT_Red)
  H_le0    : le0 N m10 jN                 (monoT(sg) reduces to this via adm_le0_seg)
  H_condA  : RedCondA N
  H_condB  : RedCondB N
  H_N00    : entry N 0 0 == 0
  H_N10    : entry N 1 0 == 0  (N's left end - is N core-anchored?)
  H_reduced: Red(N) == N

We want to know: does (some A4-independent property of N provable from green
facts: RedCondA, condAB_coeff bounds, geometry) IMPLY H_le0/H_monoT?
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, zeroT, multiT, monoT, P, TrMax, Br,
                       FirstNodes, Joints, THE_nextR, diagSeq, IncrFirst,
                       funpow, seg, fmt, le0, le1, leR, nextR, Red,
                       hasParent, parent)
from d1pos_j0j1red_search import gen_std

def RedCondA(M):
    n=Lng(M)
    for i in (0,1):
        for j in range(n):
            if hasParent(M,i,j):
                if entry(M,i,parent(M,i,j))+1 != entry(M,i,j):
                    return False
    return True

def RedCondB(M):
    n=Lng(M)
    for j in range(n):
        if (not hasParent(M,0,j)) and j<=n-1:
            if entry(M,0,j)!=entry(M,1,j):
                return False
    return True

# coefficient-bound predicates from m_6_6_condAB_coeff applied to N
def coeff_row0_le_j(N):
    n=Lng(N)
    return all(entry(N,0,j)<=j for j in range(n))

def coeff_row0_ge_row1(N):
    n=Lng(N)
    return all(entry(N,0,j)>=entry(N,1,j) for j in range(n))

counters={}
def bump(k): counters[k]=counters.get(k,0)+1
examples={}

def record(M,N,m10,jN):
    sg=seg(N,m10,jN)
    if m10>jN or len(sg)==0: return
    H={}
    H['monoT']  = monoT(sg)
    H['le0']    = le0(N,m10,jN)
    H['condA']  = RedCondA(N)
    H['condB']  = RedCondB(N)
    H['N00']    = (entry(N,0,0)==0)
    H['N10']    = (entry(N,1,0)==0)
    H['reduced']= (Red(N)==N)
    H['r0lej']  = coeff_row0_le_j(N)
    H['r0ger1'] = coeff_row0_ge_row1(N)
    # the equivalence the article uses: monoT(sg) <-> le0 N m10 jN
    bump('total')
    if H['monoT']==H['le0']: bump('monoT_eq_le0')
    else:
        examples.setdefault('monoT!=le0',[]).append((fmt(M),fmt(N),m10,jN))
    # candidate antecedents -> H_le0
    for ant in ['condA','reduced','N00','N10','r0lej','r0ger1']:
        if H[ant]:
            bump(ant+'_holds')
            if H['le0']: bump(ant+'_implies_le0')
            else: examples.setdefault(ant+'!->le0',[]).append((fmt(M),fmt(N),m10,jN))
    # combos
    if H['condA'] and H['condB']:
        bump('condAB_holds')
        if H['le0']: bump('condAB_implies_le0')
        else: examples.setdefault('condAB!->le0',[]).append((fmt(M),fmt(N),m10,jN))
    if H['N00'] and H['N10'] and H['condA']:
        bump('coreA_holds')
        if H['le0']: bump('coreA_implies_le0')
    # is N always reduced / condA / core?
    for k in ['monoT','le0','condA','condB','N00','N10','reduced','r0lej','r0ger1']:
        if H[k]: bump('hold_'+k)

def Red_inst(M, depth=0):
    if depth>300: raise RuntimeError("deep "+fmt(M))
    if zeroT(M): return [(0,0)]
    if multiT(M):
        out=[]
        for blk in P(M): out+=Red_inst(blk,depth+1)
        return out
    j1=Lng(M)-1; j1p=TrMax(M); m00=entry(M,0,0); m10=entry(M,1,0)
    if m00==0 and m10==0:
        if j1p==j1: return diagSeq(m10,m10+j1)
        out=diagSeq(0,j1p); b=Br(M); fn=FirstNodes(M); jn=Joints(M)
        for J in range(len(b)):
            br10=entry(b[J],1,0)
            np=0 if br10==0 else THE_nextR(M,1,fn[J])+1
            eJ=jn[J]+1-np
            NJ=[(m00+jn[J]+1, m10+np)]+b[J][1:]
            out+=funpow(IncrFirst,eJ,Red_inst(NJ,depth+1))
        return out
    if m10==0:
        core=[(entry(M,0,j)-m00, entry(M,1,j)) for j in range(j1+1)]
        return Red_inst(core,depth+1)
    N=Red_inst(diagSeq(0,m10-1)+funpow(IncrFirst,m10,M),depth+1)
    jN=Lng(N)-1; sg=seg(N,m10,jN)
    record(M,N,m10,jN)
    if m10<=jN and len(sg)>0 and monoT(sg):
        return [(entry(N,0,j)-entry(N,0,m10)+entry(N,1,m10), entry(N,1,j)) for j in range(m10,jN+1)]
    return M

if __name__=='__main__':
    maxlen,maxval,KMAX=(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])) if len(sys.argv)>3 else (12,5,7)
    Ms=gen_std(maxlen,maxval,KMAX)
    for M in Ms:
        try: Red_inst(M)
        except RuntimeError as e: print("DEEP",fmt(M),e)
    print(f"# gen_std maxlen={maxlen} maxval={maxval} KMAX={KMAX}; standard inputs={len(Ms)}")
    tot=counters.get('total',0)
    print(f"# m10>0 evaluations recorded: {tot}")
    print("=== how often each property of N holds (out of total) ===")
    for k in ['monoT','le0','condA','condB','N00','N10','reduced','r0lej','r0ger1']:
        print(f"  hold_{k:8s}: {counters.get('hold_'+k,0)}/{tot}")
    print("=== monoT(sg) == le0 N m10 jN ? ===")
    print(f"  monoT_eq_le0: {counters.get('monoT_eq_le0',0)}/{tot}")
    print("=== candidate antecedent -> le0 N m10 jN (implies/holds) ===")
    for ant in ['condA','reduced','N00','N10','r0lej','r0ger1','condAB','coreA']:
        h=counters.get(ant+'_holds',0); im=counters.get(ant+'_implies_le0',0)
        print(f"  {ant:8s}: holds {h}/{tot}, implies_le0 {im}/{h if h else 1}")
    print("=== counterexamples (antecedent holds but le0 fails) ===")
    for k,v in examples.items():
        print(f"  {k}: {len(v)}")
        for e in v[:4]: print("     ",e)
