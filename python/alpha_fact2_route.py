#!/usr/bin/env python3
"""ROUTE-ALPHA decisive: does the route via fact2a (PRE-Red index shift) +
M mono close le0 N m10 jN WITHOUT Red_le?

fact2a (GREEN, m_6_5_monoT_Red_fact2a_leR_shift) is about the PRE-Red arg
A := diagSeq 0 (m10-1) @ IncrFirst^m10 M, NOT about N=Red(A). It states:
  leR M i j j' <-> leR A i (j+m10) (j'+m10).
So (0,0)<=_M(0,jM)  <-> (0,m10) <=_A (0, jM+m10) = (0,m10)<=_A(0,jN_A).

BUT the slice we need monoT for is seg N m10 jN with N = Red(A), jN=Lng N-1.
le0 N m10 jN is about N=Red(A), and to pass from A to N we need Red_le
( (0,m10)<=_A(0,jA) <-> (0,m10)<=_N(0,jN) ). THAT is the circular step.

This script measures, separately:
  (1) le0 A m10 (Lng A -1)  -- provable from fact2a + M mono   [A4-INDEPENDENT]
  (2) le0 N m10 (Lng N -1)  -- the actual goal                  [needs Red_le?]
  (3) does (1) <-> (2) hold? i.e. does Red preserve THIS specific le0 ?
      If (1)<->(2) is itself just Red_le restricted to this anchor, the route
      is circular. If (1)==(2) always but provable by a WEAKER green fact
      (e.g. Lng_Red + monoT preservation of the left-anchor only), maybe not.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, zeroT, multiT, monoT, P, TrMax, Br,
                       FirstNodes, Joints, THE_nextR, diagSeq, IncrFirst,
                       funpow, seg, fmt, le0, le1, leR, nextR, Red)
from d1pos_j0j1red_search import gen_std

cnt={}
def b(k): cnt[k]=cnt.get(k,0)+1
ex={}

def record(M,m10):
    A=diagSeq(0,m10-1)+funpow(IncrFirst,m10,M)
    N=Red(A)
    jA=Lng(A)-1; jN=Lng(N)-1
    jM=Lng(M)-1
    b('total')
    # (article eqv) M mono = (0,0)<=_M(0,jM):
    Mmono = monoT(M)
    le_A = le0(A,m10,jA)          # provable A4-indep via fact2a from Mmono
    le_N = le0(N,m10,jN)          # the goal
    if Mmono: b('Mmono')
    # fact2a:  (0,0)<=_M(0,jM)  <->  (0,m10)<=_A(0,jM+m10).  jM+m10 == jA.
    if (jM+m10)==jA: b('jA_eq_jMshift')
    f2a_ok = ( le0(M,0,jM) == le0(A,m10,jM+m10) ) if jM+m10<Lng(A) else None
    if f2a_ok: b('fact2a_holds')
    # step that would close goal A4-indep: le_A == le_N ?
    if le_A==le_N: b('leA_eq_leN')
    else: ex.setdefault('leA!=leN',[]).append((fmt(M),fmt(A),fmt(N),m10))
    # is leA==leN just because both true (vacuous) or genuinely tracking?
    if Mmono:
        b('Mmono_total')
        if le_N: b('Mmono_leN')
        else: ex.setdefault('Mmono_NOTleN',[]).append((fmt(M),fmt(N),m10))
        if le_A: b('Mmono_leA')

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
        out=diagSeq(0,j1p); bb=Br(M); fn=FirstNodes(M); jn=Joints(M)
        for J in range(len(bb)):
            br10=entry(bb[J],1,0)
            np=0 if br10==0 else THE_nextR(M,1,fn[J])+1
            eJ=jn[J]+1-np
            NJ=[(m00+jn[J]+1, m10+np)]+bb[J][1:]
            out+=funpow(IncrFirst,eJ,Red_inst(NJ,depth+1))
        return out
    if m10==0:
        core=[(entry(M,0,j)-m00, entry(M,1,j)) for j in range(j1+1)]
        return Red_inst(core,depth+1)
    record(M,m10)
    N=Red_inst(diagSeq(0,m10-1)+funpow(IncrFirst,m10,M),depth+1)
    jN=Lng(N)-1; sg=seg(N,m10,jN)
    if m10<=jN and len(sg)>0 and monoT(sg):
        return [(entry(N,0,j)-entry(N,0,m10)+entry(N,1,m10), entry(N,1,j)) for j in range(m10,jN+1)]
    return M

if __name__=='__main__':
    maxlen,maxval,KMAX=(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])) if len(sys.argv)>3 else (12,5,7)
    Ms=gen_std(maxlen,maxval,KMAX)
    for M in Ms:
        try: Red_inst(M)
        except RuntimeError as e: print("DEEP",fmt(M),e)
    tot=cnt.get('total',0)
    print(f"# gen_std L={maxlen} V={maxval} K={KMAX}; m10>0 evals: {tot}")
    print(f"M (the local sub-call arg) mono : {cnt.get('Mmono',0)}/{tot}")
    print(f"jA == jM+m10                    : {cnt.get('jA_eq_jMshift',0)}/{tot}")
    print(f"fact2a equality holds           : {cnt.get('fact2a_holds',0)}/{tot}")
    print(f"le0 A m10 jA  ==  le0 N m10 jN  : {cnt.get('leA_eq_leN',0)}/{tot}   <== Red preserves THIS anchor?")
    print(f"  Mmono total {cnt.get('Mmono_total',0)}: -> le_A {cnt.get('Mmono_leA',0)}, -> le_N {cnt.get('Mmono_leN',0)}")
    for k,v in ex.items():
        print(f"  EX {k}: {len(v)}")
        for e in v[:5]: print("     ",e)
