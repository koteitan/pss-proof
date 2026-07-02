#!/usr/bin/env python3
"""Test structural claims for det case-4 exclusion (NON-recursive).
Claim S1: j1'=L-1 ==> e1 j0' >= e1 j1'  (no Admpos needed?)
Claim S2: BAD (RN=e1 j0' != e1 j1') ==> e1 j0' > e1 j1'  (=det, contrapositive)
Claim S3: among BAD, is j1'=L-1 always? (Admpos-BAD vs Adm0-BAD)
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
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

seqs=gen(6,3)
print("total:",len(seqs))

# S1: j1'=L-1 ==> e1 j0' >= e1 j1' ; with and without Admpos
s1_tot=0; s1_viol=[]
s1_admpos_tot=0; s1_admpos_viol=[]
# S3: BAD breakdown
bad_tot=0; bad_j1eq=0; bad_j1ne=0
bad_j1ne_admpos=0; bad_j1ne_adm0=0
for M in seqs:
    L=Lng(M)
    if L-1<=1: continue
    J1=len(Br(M))-1
    j1p=FirstNodes(M)[J1]; j0p=Joints(M)[J1]
    e1j1=e(M,1,j1p); e1j0=e(M,1,j0p)
    ap=(transJm1(M)>0)
    if j1p==L-1:
        s1_tot+=1
        if not (e1j0>=e1j1): s1_viol.append((M,e1j0,e1j1))
        if ap:
            s1_admpos_tot+=1
            if not (e1j0>=e1j1): s1_admpos_viol.append((M,e1j0,e1j1))
    rn=RN(Trans(M))
    if len(rn)<2: continue
    rn1=rn[1]
    BAD=(rn1==e1j0 and rn1!=e1j1)
    if BAD:
        bad_tot+=1
        if j1p==L-1: bad_j1eq+=1
        else:
            bad_j1ne+=1
            if ap: bad_j1ne_admpos+=1
            else: bad_j1ne_adm0+=1

print("S1 j1'=L-1 ==> e1j0>=e1j1 :", s1_tot-len(s1_viol),"/",s1_tot," viol:",len(s1_viol))
for v in s1_viol[:10]: print("   S1VIOL",v)
print("S1 (Admpos) :", s1_admpos_tot-len(s1_admpos_viol),"/",s1_admpos_tot," viol:",len(s1_admpos_viol))
print("BAD total:",bad_tot," j1eq(=L-1):",bad_j1eq," j1ne:",bad_j1ne,
      " [j1ne&admpos:",bad_j1ne_admpos," j1ne&adm0:",bad_j1ne_adm0,"]")
