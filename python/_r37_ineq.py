#!/usr/bin/env python3
# r37 the TRUE residual (i): entry M 1 jm2 < entry M 1 (jm2+1)  (=> M0RUN).
# Candidate proof route: entry M 1 (jm2+1) >= entry M 1 j1  (then i since
# entry M 1 jm2 < entry M 1 j1).  Split anc/non-anc; also test whether the
# route holds on non-anc.  Restrict to the M0RUN regime (adm jm2).
import sys, time
sys.path.insert(0,'python')
from red_model import (diagSeq, oper, Lng, entry, monoT, reduced, parent, adm,
                       le0, nextrel0, nextrel1, hasParent, fmt)
def pr(*a): print(*a, flush=True)
def condIIIorIV(M):
    j1=Lng(M)-1
    if not hasParent(M,0,j1): return False
    j0=parent(M,0,j1)
    return entry(M,1,j1)>0 and entry(M,1,j0)>=entry(M,1,j1)
def gen(maxlen,vcap,steps,cap):
    seen=set(); frontier=[]
    for u in range(vcap):
        for v in range(u,vcap):
            M=tuple(diagSeq(u,v))
            if 1<Lng(M)<=maxlen and M not in seen: seen.add(M); frontier.append(list(M))
    allM=list(frontier)
    for _ in range(steps):
        nf=[]
        for M in frontier:
            for n in range(1,9):
                try: Mn=oper(M,n)
                except Exception: continue
                if 1<len(Mn)<=maxlen:
                    t=tuple(Mn)
                    if t not in seen and len(seen)<cap:
                        seen.add(t); nf.append(Mn); allM.append(Mn)
        frontier=nf
        if len(seen)>=cap: break
    return allM
st={'host':0,'admjm2':0,'anc':0,'nonanc':0,'ineq':0,'e1_ge_j1':0,
    'nonanc_e1_ge_j1':0,'nonanc_ineq':0,'deep':0,'M0RUN':0}
cex=[]
def add(*a):
    if len(cex)<20: cex.append(a)
maxlen=int(sys.argv[1]); vcap=int(sys.argv[2]); steps=int(sys.argv[3]); cap=int(sys.argv[4])
t0=time.time(); corpus=gen(maxlen,vcap,steps,cap)
pr("corpus",len(corpus),"t",round(time.time()-t0))
for M in corpus:
    L=Lng(M); j1=L-1
    if L<3 or not (1<j1): continue
    if not monoT(M): continue  # ST_PS subseteq RT_PS => reduced (skip slow Red)
    if not hasParent(M,1,j1) or not hasParent(M,0,j1): continue
    if not condIIIorIV(M): continue
    jm2=parent(M,1,j1); j0=parent(M,0,j1)
    if not (jm2<j0): continue
    if jm2+1>=L: continue
    # M0RUN regime: adm jm2
    if not adm(M,jm2): continue
    st['host']+=1; st['admjm2']+=1
    if L>=10: st['deep']+=1
    isanc=le0(M,jm2+1,j1)
    st['anc' if isanc else 'nonanc']+=1
    ineq=entry(M,1,jm2)<entry(M,1,jm2+1)
    if ineq: st['ineq']+=1
    else: add("INEQ_FALSE",fmt(M),'jm2',jm2,'anc',isanc)
    ge=entry(M,1,jm2+1)>=entry(M,1,j1)
    if ge: st['e1_ge_j1']+=1
    else: add("E1GE_FALSE",fmt(M),'jm2',jm2,'anc',isanc,'e1jm2+1',entry(M,1,jm2+1),'e1j1',entry(M,1,j1),'e1',[entry(M,1,k) for k in range(L)])
    if nextrel1(M,jm2,jm2+1): st['M0RUN']+=1
    if not isanc:
        if ge: st['nonanc_e1_ge_j1']+=1
        if ineq: st['nonanc_ineq']+=1
pr(str(st))
for c in cex: pr("CEX",c)
