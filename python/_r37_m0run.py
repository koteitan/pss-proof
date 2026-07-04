#!/usr/bin/env python3
# r37 M0RUN: the CORRECT residual (r35/r36 ANC0/WGAP overshoot -> false).
# On genuine condIII/IV ST_PS hosts, test the row-1 diagonal step at jm2:
#   ineq : entry M 1 jm2 < entry M 1 (jm2+1)     (=> M0RUN via c3cx_M0RUN_of_a)
#   ramp1: entry M 1 (jm2+1) == entry M 1 jm2 + 1
#   ramp0: entry M 0 (jm2+1) == entry M 0 jm2 + 1
# Split by ancestor(le0 M (jm2+1) j1) vs NON-ancestor branch.  DEEP oper-orbit.
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

st={'host':0,'anc':0,'nonanc':0,'M0RUN':0,'ineq':0,'ramp1':0,'ramp0':0,
    'deep':0,'WGAPfalse':0,'nonanc_ineq':0,'nonanc_ramp1':0}
cex=[]
def add(*a):
    if len(cex)<20: cex.append(a)
maxlen=int(sys.argv[1]) if len(sys.argv)>1 else 14
vcap=int(sys.argv[2]) if len(sys.argv)>2 else 6
steps=int(sys.argv[3]) if len(sys.argv)>3 else 11
cap=int(sys.argv[4]) if len(sys.argv)>4 else 40000
t0=time.time()
corpus=gen(maxlen,vcap,steps,cap)
pr("corpus size",len(corpus),"t",round(time.time()-t0))
for M in corpus:
    L=Lng(M); j1=L-1
    if L<3 or not (1<j1): continue
    if not monoT(M) or not reduced(M): continue
    if not hasParent(M,1,j1) or not hasParent(M,0,j1): continue
    if not condIIIorIV(M): continue
    jm2=parent(M,1,j1); j0=parent(M,0,j1)
    if not (jm2<j0): continue
    if jm2+1>=L: continue
    st['host']+=1
    if L>=10: st['deep']+=1
    isanc = le0(M,jm2+1,j1)
    if isanc: st['anc']+=1
    else: st['nonanc']+=1
    m0 = nextrel1(M,jm2,jm2+1)
    if m0: st['M0RUN']+=1
    else: add("M0RUN_FALSE",fmt(M),'jm2',jm2,'anc',isanc)
    ineq = entry(M,1,jm2)<entry(M,1,jm2+1)
    if ineq: st['ineq']+=1
    else: add("INEQ_FALSE",fmt(M),'jm2',jm2,'anc',isanc,'e1',[entry(M,1,k) for k in range(L)])
    r1 = entry(M,1,jm2+1)==entry(M,1,jm2)+1
    if r1: st['ramp1']+=1
    else: add("RAMP1_FALSE",fmt(M),'jm2',jm2,'anc',isanc,'e1',[entry(M,1,k) for k in range(L)])
    r0 = entry(M,0,jm2+1)==entry(M,0,jm2)+1
    if r0: st['ramp0']+=1
    if not isanc:
        if ineq: st['nonanc_ineq']+=1
        if r1: st['nonanc_ramp1']+=1
    # WGAP sanity
    if not (entry(M,0,j0)==entry(M,0,jm2)+(j0-jm2)): st['WGAPfalse']+=1
pr(str(st))
for c in cex: pr("CEX",c)
