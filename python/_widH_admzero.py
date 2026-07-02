#!/usr/bin/env python3
"""Test: on DT_PS, does C ⟹ transJm1 M = 0 (Adm0)?  And in ¬j1eq∩C, what fires?"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
import red_model as rm
from red_model import (Lng, entry, monoT, TrMax, Br, FirstNodes, Joints,
                       parent, Adm, adm)
from trans_model import Trans, reduced
from collections import Counter

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
def transJ0(M): return parent(M,0,Lng(M)-1)
def transJm1(M):
    tj0=transJ0(M)
    return Adm(M,tj0) if tj0 is not None else 0

def gen_dt(maxlen,maxval):
    res=[]
    for n in range(4,maxlen+1):
        for seq in itertools.product([(a,b) for a in range(maxval+1) for b in range(maxval+1)],repeat=n):
            M=list(seq)
            if M[0] not in [(0,0),(1,1)]: continue
            if is_DT(M): res.append(M)
    return res

dt=gen_dt(6,3)
C_adm0=0; C_admpos=0; admpos_cases=[]
nj_C=0; nj_C_pin=0
for M in dt:
    try:
        if Br(M)==[] or Lng(M)-1<=1: continue
        J1=Lng(Br(M))-1; j0p=Joints(M)[J1]; j1p=FirstNodes(M)[J1]
        e1j1=entry(M,1,j1p); e1j0=entry(M,1,j0p); e0j1=entry(M,0,j1p)
        C=(j0p==0) or (e0j1==e1j1)
        if not C: continue
        a0 = (transJm1(M)==0)
        if a0: C_adm0+=1
        else:
            C_admpos+=1
            admpos_cases.append((M,j1p,Lng(M)-1,transJ0(M),transJm1(M),j0p,e1j1,e1j0))
        j1eq=(j1p==Lng(M)-1)
        if not j1eq:
            nj_C+=1
            rn=RightNodes(Trans(M))
            if len(rn)>1 and rn[1]==e1j1: nj_C_pin+=1
    except Exception: continue
print("DT∩C: Adm0=%d Admpos=%d"%(C_adm0,C_admpos))
print("¬j1eq∩C total=%d  pinned(rn1=e1j1)=%d"%(nj_C,nj_C_pin))
print("--- C∩Admpos cases (the ones not Adm0): ---")
for c in admpos_cases[:30]:
    print("  M",c[0],"j1p",c[1],"lastcol",c[2],"tJ0",c[3],"tJm1",c[4],"j0p",c[5],"e1j1",c[6],"e1j0",c[7])
