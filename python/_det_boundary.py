#!/usr/bin/env python3
"""Focused boundary probe for det case-4 exclusion.
Regime: Admpos (transJm1>0), j1'=L-1, j0'=TrMax. Want RN(Trans(Pred M))!1 = e1(L-1).
Split by det (e1 j0' < e1 j1'). Report what RN(Trans(Pred M))!1 equals, and which
predecessor quantity it matches.
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
import red_model as rm
from red_model import (Lng, entry, monoT, TrMax, Br, FirstNodes, Joints,
                       parent, Adm, adm)
from trans_model import reduced, Trans

def RN(t):
    ps = t[1]
    if not ps: return []
    p = ps[-1]
    return [p[1]] + RN(p[2])

def e(M,r,j): return entry(M,r,j)

def cdom(a,b):
    a00,a10=a[0]; b00,b10=b[0]
    return (a00>b00) or (a00==b00 and a10>=b10)
def descending(brs): return all(cdom(brs[i],brs[i+1]) for i in range(len(brs)-1))

def transJ0(M): return parent(M,0,Lng(M)-1)
def transJm1(M):
    tj0=transJ0(M)
    return Adm(M,tj0) if tj0 is not None else 0

def gen(maxlen,maxval):
    res=[]
    for n in range(3,maxlen+1):
        for seq in itertools.product([(a,b) for a in range(maxval+1) for b in range(maxval+1)],repeat=n):
            M=list(seq)
            if M[0] not in [(0,0),(1,1)]: continue
            try:
                if not (monoT(M) and reduced(M)): continue
                if Br(M)==[]: continue
                if not descending(Br(M)): continue
            except: continue
            res.append(M)
    return res

seqs = gen(6,3)
print("total:", len(seqs))

# regime: Admpos, j1'=L-1, j0'=TrMax
n_regime=0
n_regime_det=0       # det: e1 j0' < e1 j1'
predRN_eq_e1Lm1_det = 0   # under det, RN(Trans(Pred))!1 == e1(L-1)
predRN_eq_e1Lm1_all = 0
det_predRN_fail=[]
match_prevfn=0; match_prevjoint=0; match_other=0
# also: is the regime under det nonempty? det no-violation says BAD never under det.
det_bad=0
for M in seqs:
    L=Lng(M)
    if L-1<=1: continue
    J1=len(Br(M))-1
    j1p=FirstNodes(M)[J1]
    j0p=Joints(M)[J1]
    if j1p != L-1: continue          # boundary
    if transJm1(M)<=0: continue      # Admpos
    if j0p != TrMax(M): continue     # j0'=TrMax
    n_regime+=1
    e1j1=e(M,1,j1p); e1j0=e(M,1,j0p)
    PM=M[:-1]
    rnP=RN(Trans(PM))
    if len(rnP)<2: continue
    rnP1=rnP[1]
    e1Lm1=e(M,1,L-1)   # = e1j1 since j1p=L-1
    det = (e1j0 < e1j1)
    if det:
        n_regime_det+=1
        if rnP1==e1Lm1: predRN_eq_e1Lm1_det+=1
        else: det_predRN_fail.append((M, rnP1, e1Lm1, e1j0))
    if rnP1==e1Lm1: predRN_eq_e1Lm1_all+=1
    # what does rnP1 match among Pred's last-branch quantities?
    if J1>=1:
        prevfn=FirstNodes(M)[J1-1]; prevjoint=Joints(M)[J1-1]
        if rnP1==e(M,1,prevfn): match_prevfn+=1
        elif rnP1==e(M,1,prevjoint): match_prevjoint+=1
        else: match_other+=1

print("regime (Admpos,j1'=L-1,j0'=TrMax):", n_regime)
print("  of which det (e1j0<e1j1):", n_regime_det)
print("  under det, RN(Trans(Pred))!1==e1(L-1):", predRN_eq_e1Lm1_det, "/", n_regime_det)
print("  all-regime RN(Trans(Pred))!1==e1(L-1):", predRN_eq_e1Lm1_all, "/", n_regime)
print("  match prevfn:", match_prevfn, " prevjoint:", match_prevjoint, " other:", match_other)
for f in det_predRN_fail[:12]:
    print("   DET-FAIL", f)
