#!/usr/bin/env python3
"""Validate the det (widH) recursive proof route.
det: e1 j0' < e1 j1' ==> RightNodes(Trans M)!1 = e1 j1'   (j1'=FN!J1, j0'=Joints!J1, J1=Lng(Br)-1)
Equivalently widH: e1 j1' <= RN(Trans M)!1.
Route: induction; Admpos uses wid_step (RN(M)!1 = RN(Pred M)!1); Adm0 uses keystone.
Key residual: keystone case (4) (RN = e1 j0') exclusion under e1 j0' < e1 j1'.
Sub-claim A: in 'BAD' (RN=e1 j0') situations with j1ne, IH+ft gives contradiction.
Sub-claim B (j1eq crux): e1(Lng M-1) <= e1(FirstNodes M!(J1-1)).
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

def transJm1(M):
    # Adm M (transJ0 M) ; transJm1 = Adm(...)-1? Use definition via Adm at transJ0
    tj0 = parent(M,0,Lng(M)-1)
    return Adm(M, tj0) if tj0 is not None else 0
    # NOTE: actual transJm1_def = Adm M (transJ0 M) - 1 form; we use Adm>... below

seqs = gen(6,3)
print("total reduced-monoT M (Br!=[], Lng3..6):", len(seqs))

def transJ0(M): return parent(M,0,Lng(M)-1)
def transJm1(M):
    tj0=transJ0(M)
    return Adm(M,tj0) if tj0 is not None else 0

det_viol=0
bad_total=0
bad_j1eq=0; bad_j1ne=0
crux_total=0; crux_viol=[]
# Adm0-BAD analysis: is e0 j1' > e1 j1' (case-2 cond) always true? i.e. is Adm0-case4-under-C empty?
adm0_bad=0; adm0_bad_case2cond=0; adm0_bad_notcase2=[]
admpos_bad=0
adm0_bad_j1ne=0
for M in seqs:
    try:
        L=Lng(M)
        if L-1<=1: continue
        J1=len(Br(M))-1
        j1p=FirstNodes(M)[J1]
        j0p=Joints(M)[J1]
        rn=RN(Trans(M))
        if len(rn)<2: continue
        rn1=rn[1]
        e1j1=e(M,1,j1p); e1j0=e(M,1,j0p)
        BAD = (rn1==e1j0 and rn1!=e1j1)
        GOOD = (rn1==e1j1)
        # det sanity: under e1j0<e1j1, must be GOOD
        if e1j0<e1j1 and not GOOD:
            det_viol+=1
            if det_viol<=8: print("DET VIOL", M, "e1j0",e1j0,"e1j1",e1j1,"rn1",rn1)
        if BAD:
            bad_total+=1
            j1eq = (j1p==L-1)
            if j1eq: bad_j1eq+=1
            else: bad_j1ne+=1
            adm0 = (transJm1(M)==0)
            e0j1 = e(M,0,j1p)
            if adm0:
                adm0_bad+=1
                if not j1eq: adm0_bad_j1ne+=1
                if e0j1 > e1j1: adm0_bad_case2cond+=1
                else: adm0_bad_notcase2.append((M, "j1eq" if j1eq else "j1ne", e0j1, e1j1, e1j0))
            else:
                admpos_bad+=1
        # j1eq crux: e1(L-1) <= e1(FirstNodes!(J1-1)), needs J1>=1 and Br(Pred)!=[]
        if j1p==L-1 and J1>=1:
            prevfn = FirstNodes(M)[J1-1]
            crux_total+=1
            if not (e(M,1,L-1) <= e(M,1,prevfn)):
                crux_viol.append((M, e(M,1,L-1), e(M,1,prevfn)))
    except Exception as ex:
        continue

print("det violations:", det_viol)
print("BAD total:", bad_total, " BAD&j1eq:", bad_j1eq, " BAD&j1ne:", bad_j1ne)
print("Adm0-BAD:", adm0_bad, " (j1ne:", adm0_bad_j1ne, ") case2cond(e0>e1):", adm0_bad_case2cond,
      " NOTcase2:", len(adm0_bad_notcase2))
print("Admpos-BAD:", admpos_bad)
for v in adm0_bad_notcase2[:12]: print("  ADM0-BAD-notcase2", v)
print("j1eq-crux tested:", crux_total, " violations:", len(crux_viol))
