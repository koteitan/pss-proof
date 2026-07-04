#!/usr/bin/env python3
# r37 TRUNK hypothesis: is the WGAP window [jm2,j0] inside the trunk [0,TrMax]?
# If j0<=TrMax then row-0 strictly increases on the window (trunk=nextrel1 spine
# => nextrel0 consecutive), giving WGAP for free.
import sys, time, itertools
sys.path.insert(0, 'python')
import red_model as R
from red_model import (Lng, entry, monoT, reduced, parent, adm,
                       le0, nextrel0, nextrel1, Br, FirstNodes, Joints,
                       hasParent, fmt, TrMax)

def pr(*a): print(*a, flush=True)

def condIIIorIV(M):
    j1=Lng(M)-1
    if not hasParent(M,0,j1): return False
    j0=parent(M,0,j1)
    return entry(M,1,j1)>0 and entry(M,1,j0)>=entry(M,1,j1)

st={'host':0,'WGAP':0,'j0_le_TrMax':0,'jm2_le_TrMax':0,'window_nextrel1':0,
    'window_nextrel0':0}
cex=[]
def add(*a):
    if len(cex)<15: cex.append(a)

outf=open('/tmp/_r37_trunk.out','w')
def wr(*a): print(*a,file=outf,flush=True); print(*a,flush=True)

Lmax=int(sys.argv[1]) if len(sys.argv)>1 else 7
vmax=int(sys.argv[2]) if len(sys.argv)>2 else 4
t0=time.time()
cells=[(a,b) for a in range(vmax) for b in range(vmax)]
for L in range(3,Lmax+1):
    if time.time()-t0>1400: wr("[budget stop] L",L); break
    for tup in itertools.product(cells, repeat=L-1):
        if time.time()-t0>1400: break
        M=[(0,0)]+list(tup)
        if not monoT(M): continue
        if not reduced(M): continue
        j1=Lng(M)-1
        if not (1<j1): continue
        if not hasParent(M,1,j1): continue
        if not hasParent(M,0,j1): continue
        if not condIIIorIV(M): continue
        jm2=parent(M,1,j1); j0=parent(M,0,j1)
        if not (jm2<j0): continue
        st['host']+=1
        tm=TrMax(M)
        e0=[entry(M,0,j) for j in range(L)]
        wgap = e0[j0]==e0[jm2]+(j0-jm2)
        if wgap: st['WGAP']+=1
        else: add("WGAP_FALSE",fmt(M),jm2,j0,e0)
        if j0<=tm: st['j0_le_TrMax']+=1
        else: add("j0>TrMax",fmt(M),'jm2',jm2,'j0',j0,'TrMax',tm)
        if jm2<=tm: st['jm2_le_TrMax']+=1
        else: add("jm2>TrMax",fmt(M),'jm2',jm2,'j0',j0,'TrMax',tm)
        wn1=all(nextrel1(M,i,i+1) for i in range(jm2,j0))
        if wn1: st['window_nextrel1']+=1
        else: add("NOT_window_nextrel1",fmt(M),jm2,j0,tm)
        wn0=all(nextrel0(M,i,i+1) for i in range(jm2,j0))
        if wn0: st['window_nextrel0']+=1
    wr(f"[L={L}] host={st['host']} WGAP={st['WGAP']} j0<=TrMax={st['j0_le_TrMax']} "
       f"jm2<=TrMax={st['jm2_le_TrMax']} winNR1={st['window_nextrel1']} "
       f"winNR0={st['window_nextrel0']} t={time.time()-t0:.0f}s")
wr("="*60)
wr(str(st))
for c in cex: wr("CEX "+repr(c))
outf.close()
