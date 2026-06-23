import itertools, sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng, entry, P, monoT, TrMax, Br, parent, FirstNodes, Joints, diagSeq, seg)
from trans_model import (Trans, Pred, reduced, adm, Adm, ZB, Dpt, addBT, PB, bpHeadV, bpHeadT)
import collections
def enum(ml, me):
    cols=[(a,b) for a in range(me+1) for b in range(me+1)]
    for L in range(2,ml+1):
        for M in itertools.product(cols,repeat=L): yield list(M)
def transJ0(M): return parent(M,0,Lng(M)-1)
def transJm1(M): return Adm(M,transJ0(M))
st=collections.Counter()
egs=[]
for M in enum(6,4):
    if not (entry(M,0,0)==0 and entry(M,1,0)==0): continue
    if not (monoT(M) and reduced(M)): continue
    if Br(M)==[]: continue
    j1=Lng(M)-1
    if not (j1>1): continue
    n=j1-TrMax(M)
    if n!=1: continue   # BASE
    # Pred M should be diagSeq 0 (j1-1)
    PM=Pred(M)
    v=j1-1
    isdiag = (PM==diagSeq(0,v))
    st[('PredIsDiag',isdiag)]+=1
    # M = diagSeq 0 v @ [last]; last column = M[-1]
    w0,w1=M[-1]
    # which of the 4 m_8_1_Pred_diagSeq_Trans cases?  u=0,v=v,w'=w0,w=w1
    u=0
    case=None
    if w0==v+1 and u<w1<=v: case=1
    elif u<w0<=v and w1==w0: case=2
    elif u+1<w0<=v and w1<w0: case=3
    elif u+1==w0 and w1<w0: case=4
    st[('case',case)]+=1
    if case is None and len(egs)<10: egs.append((M,u,v,w0,w1))
print("BASE n=1 (len<=6,e<=4):")
for k,vv in sorted(st.items(),key=lambda x:str(x[0])): print(" ",k,vv)
print("uncovered egs:",egs)
