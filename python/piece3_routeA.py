#!/usr/bin/env python3
"""PIECE3 ROUTE-A empirical test.

PIECE3: M in PT_PS, monoT M, entry M 0 0=0, entry M 1 0=0, TrMax M != Lng M-1 (branch-3b),
  Red M = diagSeq 0 (TrMax M) @ concat(map (lambda J. IncrFirst^eJ (Red (NJ M J))) [0..<Lng(Br M)]).
  Claim: for every J < Lng(Br M):  le0 (Red M) 0 bs_J,
    where bs_J = (TrMax M+1) + sum_{K<J} Lng(block_K).

ROUTE-A: le0 (Red M) 0 bs_J follows from idxsum_leftend_lmin applied to Red M:
  (A1) Red M in T_PS.
  (A2) bs_J is a P-component leftend of Red M, i.e. bs_J = IdxSum (P (Red M)) ! someJ'.
  (A3) bs_J is a row-0 left-minimum of Red M (the lmin characterization).
  (A4) 0 is the root (global row-0 minimum) and the left-min spine connects 0 to bs_J,
       giving le0 (Red M) 0 bs_J.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, zeroT, multiT, monoT, seg, le0, leR, nextrel0,
                       Red, diagSeq, IncrFirst, funpow, TrMax, Br, FirstNodes, Joints, P,
                       nextR_THE)
from itertools import product

def IdxSum(Q):
    out=[0]
    for blk in Q: out.append(out[-1]+Lng(blk))
    return out

def is_TPS(M):
    return Lng(M)>=1  # T_PS in this project = nonempty (entries nat). adequately models.

def all_mono_anchored(maxlen,maxval):
    out=[]
    for n in range(1,maxlen+1):
        for cells in product(product(range(maxval+1),repeat=2),repeat=n):
            M=[tuple(c) for c in cells]
            if zeroT(M) or not monoT(M): continue
            if entry(M,0,0)!=0 or entry(M,1,0)!=0: continue
            out.append(M)
    return out

def NJ_of(M,J):
    m00=entry(M,0,0); m10=entry(M,1,0)
    b=Br(M); fn=FirstNodes(M); jn=Joints(M)
    br10=entry(b[J],1,0)
    np=0 if br10==0 else nextR_THE(M,1,fn[J])+1
    return [(m00+jn[J]+1, m10+np)]+b[J][1:], (jn[J]+1-np)

def red_M_branch3b(M):
    j1=Lng(M)-1; j1p=TrMax(M)
    out=diagSeq(0,j1p); b=Br(M)
    blocks=[]
    for J in range(len(b)):
        NJ,eJ=NJ_of(M,J)
        blk=funpow(IncrFirst,eJ,Red(NJ))
        blocks.append(blk); out+=blk
    return out, blocks

if __name__=='__main__':
    L,V=(int(sys.argv[1]),int(sys.argv[2])) if len(sys.argv)>2 else (5,3)
    Ms=all_mono_anchored(L,V)
    cases=0; piece3_ok=0; piece3_total=0
    a1=0; a2=0; a3=0; redM_TPS=0
    fails=[]
    a2fail=[]; a3fail=[]
    for M in Ms:
        j1=Lng(M)-1; j1p=TrMax(M)
        if j1p==j1: continue  # need branch-3b (nontrunk)
        cases+=1
        RM, blocks = red_M_branch3b(M)
        # verify Red M matches the model
        assert RM==Red(M), (M,RM,Red(M))
        nblk=len(blocks)
        # bs_J
        bs=[ (j1p+1) ]
        for J in range(nblk): bs.append(bs[-1]+Lng(blocks[J]))
        # A1: Red M in T_PS (nonempty)
        if is_TPS(RM): a1+=1
        # P-components of Red M and their leftends
        PRM=P(RM); leftends=IdxSum(PRM)[:-1]  # leftend index of each P-component
        for J in range(nblk):
            piece3_total+=1
            b_J=bs[J]
            # PIECE3 claim
            ok=le0(RM,0,b_J)
            if ok: piece3_ok+=1
            else: fails.append((M,J,b_J))
            # A2: bs_J is a P-component leftend of Red M
            if b_J in leftends: a2+=1
            else: a2fail.append((M,J,b_J,leftends))
            # A3: bs_J is a row-0 left-minimum of Red M
            islmin = all(entry(RM,0,j)>=entry(RM,0,b_J) for j in range(b_J))
            if islmin: a3+=1
            else: a3fail.append((M,J,b_J))
    print(f"# branch-3b anchored mono cases (len<={L} val<={V}): {cases}")
    print(f"# Red M in T_PS (A1): {a1}/{cases}")
    print(f"# PIECE3 le0(Red M) 0 bs_J: {piece3_ok}/{piece3_total}")
    print(f"# A2 bs_J is P-component leftend of Red M: {a2}/{piece3_total}")
    print(f"# A3 bs_J is row-0 left-minimum of Red M: {a3}/{piece3_total}")
    for e in fails[:6]: print("  P3FAIL:",e)
    for e in a2fail[:6]: print("  A2FAIL:",e)
    for e in a3fail[:6]: print("  A3FAIL:",e)
