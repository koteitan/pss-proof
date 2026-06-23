import itertools, sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng, entry, P, monoT, TrMax, Br, parent, FirstNodes, Joints)
from trans_model import (Trans, Mark, Pred, reduced, adm, Adm, ZB, Dpt, addBT, PB, bpHeadV, bpHeadT)
import collections

def enum(ml, me):
    cols=[(a,b) for a in range(me+1) for b in range(me+1)]
    for L in range(2,ml+1):
        for M in itertools.product(cols,repeat=L): yield list(M)
def transJ0(M): return parent(M,0,Lng(M)-1)
def transJm1(M): return Adm(M,transJ0(M))

# In Admpos: does Pred M's Trans already match clause-3/4 shape with the SAME j-index used for M?
# clause3 index = e1j1p, clause4 index = e1j0p.  For Pred M with its own indices, the IH
# would give Pred(M) in clause shape with Pred's own j1''/j0''.  But what we really want:
# Trans M and Trans(Pred M) share prefix A then D_ev then differ.  ev = entry M 1 j1p or j0p.
# Check: in Admpos, is the prefix structure of Trans M obtained from Trans(Pred M) by
# scb-surgery that REPLACES the suffix after a shared D_ev?

stats = collections.Counter()
examples3=[]; examples4=[]
for M in enum(5,3):
    if not (entry(M,0,0)==0 and entry(M,1,0)==0): continue
    if not monoT(M): continue
    if not reduced(M): continue
    if Br(M)==[]: continue
    j1=Lng(M)-1
    if not (j1>1): continue
    if transJm1(M)==0: continue   # Admpos only
    tP=Trans(Pred(M)); tM=Trans(M)
    e10=entry(M,1,0)
    J1=Lng(Br(M))-1
    j1p=FirstNodes(M)[J1]; j0p=Joints(M)[J1]
    e1j1p=entry(M,1,j1p); e1j0p=entry(M,1,j0p)
    # outer head check
    okP = tP[1] and tP[1][0][0]=='D' and tP[1][0][1]==e10 and len(tP[1])==1
    okM = tM[1] and tM[1][0][0]=='D' and tM[1][0][1]==e10 and len(tM[1])==1
    if not (okP and okM):
        stats['OUTER_FAIL']+=1; continue
    bodyP=tP[1][0][2][1]; bodyM=tM[1][0][2][1]
    # find the longest common prefix of bodyP, bodyM
    k=0
    while k<len(bodyP) and k<len(bodyM) and bodyP[k]==bodyM[k]: k+=1
    # after common prefix, the next BP in both should be D_ev with same v (the "split" head)
    if k<len(bodyP) and k<len(bodyM) and bodyP[k][0]=='D' and bodyM[k][0]=='D' and bodyP[k][1]==bodyM[k][1]:
        ev=bodyP[k][1]
        # and that's the last principal in both (clause shape: A + D_ev tail, single trailing)
        tail_single = (k==len(bodyP)-1 and k==len(bodyM)-1)
        if ev==e1j1p:
            stats[('clause3', tail_single)]+=1
            if len(examples3)<3: examples3.append((M, ev, k, len(bodyP), len(bodyM)))
        elif ev==e1j0p:
            stats[('clause4', tail_single)]+=1
            if len(examples4)<3: examples4.append((M, ev, k, len(bodyP), len(bodyM)))
        else:
            stats[('other_ev', ev, e1j1p, e1j0p)]+=1
    else:
        stats['NO_COMMON_SPLIT']+=1
for k,v in sorted(stats.items(), key=lambda x:str(x[0])): print(k, v)
print("ex3:", examples3)
print("ex4:", examples4)
