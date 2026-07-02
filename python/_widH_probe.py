#!/usr/bin/env python3
"""Probe DT_PS ∩ C ∩ j1eq ∩ Admpos: resolve the chainOK/widTrM tension.
transJ0 M = parent(M,0,Lng-1); transJm1 = Adm(M,transJ0); Admpos = transJm1>0."""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
import red_model as rm
from red_model import (Lng, entry, monoT, TrMax, Br, FirstNodes, Joints,
                       parent, Adm, adm)
from trans_model import Trans, reduced

def RightNodes(t):
    ps=t[1]
    if not ps: return []
    return [ps[-1][1]]+RightNodes(ps[-1][2])
def cdom(a,b):
    a00,a10=a[0]; b00,b10=b[0]
    return (a00>b00) or (a00==b00 and a10>=b10)
def descending(brs): return all(cdom(brs[i],brs[i+1]) for i in range(len(brs)-1))
def is_DT(M):
    try: return monoT(M) and reduced(M) and descending(Br(M))
    except: return False
def Pred(M): return M[:-1] if Lng(M)>1 else M
def transJ0(M): return parent(M,0,Lng(M)-1)
def Admpos(M):
    tj0=transJ0(M)
    if tj0 is None: return False
    return Adm(M,tj0)>0

def gen_dt(maxlen,maxval):
    res=[]
    for n in range(4,maxlen+1):
        for seq in itertools.product([(a,b) for a in range(maxval+1) for b in range(maxval+1)],repeat=n):
            M=list(seq)
            if M[0] not in [(0,0),(1,1)]: continue
            if is_DT(M): res.append(M)
    return res

dt=gen_dt(6,3)
# C ∩ j1eq ∩ Admpos cases
sel=[]
for M in dt:
    try:
        if Br(M)==[] or Lng(M)-1<=1: continue
        J1=Lng(Br(M))-1; j0p=Joints(M)[J1]; j1p=FirstNodes(M)[J1]
        e1j1=entry(M,1,j1p); e1j0=entry(M,1,j0p); e0j1=entry(M,0,j1p)
        C=(j0p==0) or (e0j1==e1j1)
        j1eq=(j1p==Lng(M)-1)
        if C and j1eq and Admpos(M):
            rn=RightNodes(Trans(M))
            rn1=rn[1] if len(rn)>1 else None
            sel.append((M, TrMax(M), j0p, j1p, e1j1, e1j0,
                        entry(M,1,TrMax(M)), rn1, Br(Pred(M))==[], C))
    except Exception as ex: continue
print("DT ∩ C ∩ j1eq ∩ Admpos:", len(sel))
from collections import Counter
print("  Br(Pred M)=[] (base) dist:", Counter(s[8] for s in sel))
print("  rn1==e1j1 dist:", Counter(s[7]==s[4] for s in sel))
print("  rn1==e1(TrMax) dist:", Counter(s[7]==s[6] for s in sel))
print("  TrMax==j0p dist:", Counter(s[1]==s[2] for s in sel))
for s in sel[:25]:
    print("  M",s[0],"TrMax",s[1],"j0p",s[2],"j1p",s[3],"e1j1",s[4],"e1j0",s[5],
          "e1Tr",s[6],"rn1",s[7],"BrPred=[]",s[8])
