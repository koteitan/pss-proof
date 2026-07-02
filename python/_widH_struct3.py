#!/usr/bin/env python3
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

def gen_dt(maxlen,maxval):
    res=[]
    for n in range(4,maxlen+1):
        for seq in itertools.product([(a,b) for a in range(maxval+1) for b in range(maxval+1)],repeat=n):
            M=list(seq)
            if M[0] not in [(0,0),(1,1)]: continue
            if is_DT(M): res.append(M)
    return res

dt=gen_dt(6,3)
land=Counter(); pin_under_C=0; relax_under_C=0; total_C=0
# also: does j0p-landing EVER happen on DT_PS at all (regardless of C)?
j0_any=0; j0_underC=0
for M in dt:
    try:
        if Br(M)==[] or Lng(M)-1<=1: continue
        J1=Lng(Br(M))-1; j0p=Joints(M)[J1]; j1p=FirstNodes(M)[J1]
        e1j1=entry(M,1,j1p); e1j0=entry(M,1,j0p); e0j1=entry(M,0,j1p)
        rn=RightNodes(Trans(M))
        if len(rn)<2: continue
        rn1=rn[1]
        lands='j1p' if rn1==e1j1 else ('j0p' if rn1==e1j0 else '?')
        if lands=='j0p': j0_any+=1
        C=(j0p==0) or (e0j1==e1j1)
        if C:
            total_C+=1
            if rn1==e1j1: pin_under_C+=1
            elif e1j1<=rn1: relax_under_C+=1
            if lands=='j0p': j0_underC+=1
    except: continue
print("DT count:",len(dt))
print("j0p-landing on DT_PS (any condition):",j0_any)
print("C-sat total:",total_C,"pinned(rn1=e1j1):",pin_under_C,"relaxed-only:",relax_under_C)
print("j0p-landing under C on DT_PS:",j0_underC)
