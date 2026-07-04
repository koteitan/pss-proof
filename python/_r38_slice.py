#!/usr/bin/env python3
# r38: for non-anc hosts, test whether the anchored slice S = seg M jm2 j1 is
# reduced (RT_PS) and descending(Br S) (=> DT_PS), and locate a/j0/jm2+1 in S.
# Also confirm m_8_2_branch_row1_le_TrMax direction on the slice.
import sys, time, random
sys.path.insert(0,'python')
from fast_pss import (Lng, entry, le0, nextrel0, nextrel1, hasParent1, parent1,
                      hasParent0, parent0, oper, reduced, diagSeq, fmt)
from red_model import seg, TrMax, Br, FirstNodes, monoT as monoT_rm
import red_model as rm

def zeroT(M): return Lng(M)==1 and entry(M,1,0)==0
def monoT(M): return (not zeroT(M)) and le0(M,0,Lng(M)-1)
def descending(Q):
    L=len(Q)
    for J0 in range(L):
        for J1 in range(J0,L):
            if entry(Q[J0],0,0) < entry(Q[J1],0,0): return False
            if entry(Q[J0],0,0)==entry(Q[J1],0,0) and entry(Q[J0],1,0)<entry(Q[J1],1,0): return False
    return True
def condIIIorIV(M):
    j1=Lng(M)-1
    if not hasParent0(M,j1): return False
    j0=parent0(M,j1)
    return entry(M,1,j1)>0 and entry(M,1,j0)>=entry(M,1,j1)
def host(M):
    L=Lng(M); j1=L-1
    if L<3 or not monoT(M): return None
    if not hasParent1(M,j1) or not hasParent0(M,j1): return None
    if not condIIIorIV(M): return None
    jm2=parent1(M,j1); j0=parent0(M,j1)
    if not (jm2<j0) or jm2+1>=L: return None
    return (jm2,j0,j1)

random.seed(3)
seed_cap=5; maxlen=26; maxdepth=20; ncap=5; frontcap=9000
seen=set(); frontier=[]
for u in range(seed_cap):
    for v in range(u,seed_cap):
        M=tuple(diagSeq(u,v))
        if 1<Lng(M)<=maxlen: seen.add(M); frontier.append(M)
st={'nonanc':0,'S_reduced':0,'S_desc':0,'S_DT':0,'a_is_FN':0,'M_DT':0}
bad=[]
for depth in range(maxdepth+1):
    for M in frontier:
        r=host(list(M))
        if r is None: continue
        jm2,j0,j1=r; Ml=list(M)
        if le0(Ml,jm2+1,j1): continue
        st['nonanc']+=1
        # M in DT_PS ?
        if descending(Br(Ml)) and reduced(Ml): st['M_DT']+=1
        # slice S
        S=seg(Ml,jm2,j1)  # S index k = M index jm2+k
        Sred=reduced(S); Sdesc=descending(Br(S))
        if Sred: st['S_reduced']+=1
        if Sdesc: st['S_desc']+=1
        if Sred and Sdesc and monoT(S): st['S_DT']+=1
        # a = first row-0 child of jm2 toward j1
        kids=[c for c in range(Lng(Ml)) if nextrel0(Ml,jm2,c)]
        path=[c for c in kids if le0(Ml,c,j1)]
        a=min(path) if path else None
        # is a a FirstNode of S? S-index of a = a-jm2
        FN=[jm2+f for f in FirstNodes(S)] if monoT(S) else []
        a_is_FN = (a is not None) and (a in FN)
        if a_is_FN: st['a_is_FN']+=1
        else:
            if len(bad)<15: bad.append(('aNotFN' if a is not None else 'noA',fmt(Ml),'jm2',jm2,'a',a,'FN(M-idx)',FN,'Sred',Sred,'Sdesc',Sdesc))
        # sanity check contradiction ingredient: entry1 a vs entry1 jm2
        if a is not None and not (entry(Ml,1,a) >= entry(Ml,1,j1)):
            if len(bad)<15: bad.append(('a_lowrow1',fmt(Ml),'jm2',jm2,'a',a,'e1a',entry(Ml,1,a),'e1j1',entry(Ml,1,j1)))
    # expand
    nxt=[]; fr=list(frontier); random.shuffle(fr)
    for M in fr:
        Ml=list(M)
        for n in range(1,ncap+1):
            try: Mn=oper(Ml,n)
            except Exception: continue
            if 1<len(Mn)<=maxlen:
                t=tuple(Mn)
                if t not in seen: seen.add(t); nxt.append(t)
        if len(nxt)>=frontcap: break
    if len(nxt)>frontcap: nxt=random.sample(nxt,frontcap)
    frontier=nxt
    if not frontier: break
print(st, flush=True)
for b in bad: print("BAD",b,flush=True)
