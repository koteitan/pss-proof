#!/usr/bin/env python3
"""Is 'j1eq ∧ Admpos ⟹ e0 j1' > e1 j1'' (i.e. ⟹¬C2) true on reduced-monoT?
Does it need descending(Br)?  Also test the recursion's well-foundedness premises."""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
import red_model as rm
from red_model import (Lng, entry, monoT, TrMax, Br, FirstNodes, Joints,
                       parent, Adm, adm)
from trans_model import reduced
from collections import Counter

def cdom(a,b):
    a00,a10=a[0]; b00,b10=b[0]
    return (a00>b00) or (a00==b00 and a10>=b10)
def descending(brs): return all(cdom(brs[i],brs[i+1]) for i in range(len(brs)-1))
def transJ0(M): return parent(M,0,Lng(M)-1)
def Admpos(M):
    tj0=transJ0(M)
    return tj0 is not None and Adm(M,tj0)>0

def gen(maxlen,maxval, need_desc):
    res=[]
    for n in range(3,maxlen+1):
        for seq in itertools.product([(a,b) for a in range(maxval+1) for b in range(maxval+1)],repeat=n):
            M=list(seq)
            if M[0] not in [(0,0),(1,1)]: continue
            try:
                if not (monoT(M) and reduced(M)): continue
                if Br(M)==[]: continue
                if need_desc and not descending(Br(M)): continue
            except: continue
            res.append(M)
    return res

for need_desc in (False, True):
    seqs=gen(6,3,need_desc)
    # j1eq ∧ Admpos cases: check e0 j1' vs e1 j1'
    viol=[]; tot=0
    for M in seqs:
        try:
            if Lng(M)-1<=1: continue
            J1=Lng(Br(M))-1; j1p=FirstNodes(M)[J1]
            j1eq=(j1p==Lng(M)-1)
            if not (j1eq and Admpos(M)): continue
            tot+=1
            e0=entry(M,0,j1p); e1=entry(M,1,j1p)
            if e0==e1:  # C2 holds -> would violate
                viol.append((M,e0,e1))
        except: continue
    print("desc=%s: j1eq∩Admpos total=%d, C2-violations(e0==e1)=%d"%(need_desc,tot,len(viol)))
    for v in viol[:8]: print("   ",v)
