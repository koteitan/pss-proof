#!/usr/bin/env python3
# r37 WGAP probe: brute-straddle corpus, genuine condIII/IV ST_PS members.
# Test WGAP (>=half) and candidate structural invariants for the window [jm2,j0].
import sys, time, itertools
sys.path.insert(0, 'python')
import red_model as R
from red_model import (Lng, entry, monoT, reduced, seg, parent, Adm, adm, nadm,
                       le0, nextrel0, nextrel1, Br, FirstNodes, Joints, Red,
                       hasParent, fmt, TrMax, Pred, is_standard)

def pr(*a): print(*a, flush=True)

# PT_PS = T_PS & monoT ; here we approximate T_PS membership by valid pairseq.
def transJ0(M): return parent(M,0,Lng(M)-1)

def condIII(M):
    j1=Lng(M)-1
    if not hasParent(M,0,j1): return False
    j0=parent(M,0,j1)
    return entry(M,1,j1)>0 and entry(M,1,j0)>=entry(M,1,j1) and adm(M,j0)
def condIV(M):
    j1=Lng(M)-1
    if not hasParent(M,0,j1): return False
    j0=parent(M,0,j1)
    return entry(M,1,j1)>0 and entry(M,1,j0)>=entry(M,1,j1) and not adm(M,j0)

st={'host':0,'WGAP':0,'sincr_window':0,'all_le0_i_j0':0,'all_le0_jm2_i':0,
    'window_all_anc_j1':0,'row1_nondec_window':0,'jm2_eq_blockstart':0,
    'e0_i_ge_e0j1_on_j0j1':0}
cex=[]
def add(tag,*a):
    if len(cex)<12: cex.append((tag,)+a)

Lmax=int(sys.argv[1]) if len(sys.argv)>1 else 8
vmax=int(sys.argv[2]) if len(sys.argv)>2 else 4
t0=time.time()
cells=[(a,b) for a in range(vmax) for b in range(vmax)]
for L in range(3,Lmax+1):
    if time.time()-t0>1500: pr("[budget stop] L",L); break
    for tup in itertools.product(cells, repeat=L-1):
        if time.time()-t0>1500: break
        M=[(0,0)]+list(tup)
        if not monoT(M): continue
        if not reduced(M): continue
        j1=Lng(M)-1
        if not (1<j1): continue
        if not hasParent(M,1,j1): continue
        if not hasParent(M,0,j1): continue
        if not (condIII(M) or condIV(M)): continue
        jm2=parent(M,1,j1); j0=parent(M,0,j1)
        if not (jm2<j0): continue    # condIII/IV forces this
        st['host']+=1
        e0=[entry(M,0,j) for j in range(L)]
        # WGAP
        wgap = e0[j0]==e0[jm2]+(j0-jm2)
        if wgap: st['WGAP']+=1
        else: add("WGAP_FALSE",fmt(M),'jm2',jm2,'j0',j0,'e0',e0)
        # strict increase on window
        sincr=all(e0[i]<e0[i+1] for i in range(jm2,j0))
        if sincr: st['sincr_window']+=1
        else: add("NOT_SINCR",fmt(M),jm2,j0,e0)
        # every window index reaches j0
        alle0=all(le0(M,i,j0) for i in range(jm2,j0+1))
        if alle0: st['all_le0_i_j0']+=1
        else: add("NOT_all_le0_i_j0",fmt(M),jm2,j0,[i for i in range(jm2,j0+1) if not le0(M,i,j0)])
        # every window index reachable from jm2
        allfrom=all(le0(M,jm2,i) for i in range(jm2,j0+1))
        if allfrom: st['all_le0_jm2_i']+=1
        else: add("NOT_all_le0_jm2_i",fmt(M),jm2,j0)
        # every window index anc of j1
        allanc=all(le0(M,i,j1) for i in range(jm2,j0+1))
        if allanc: st['window_all_anc_j1']+=1
        # row1 nondecreasing on window
        e1=[entry(M,1,j) for j in range(L)]
        r1nd=all(e1[i]<=e1[i+1] for i in range(jm2,j0))
        if r1nd: st['row1_nondec_window']+=1
        # e0 on (j0,j1) >= e0 j1
        okv=all(e0[j]>=e0[j1] for j in range(j0+1,j1))
        if okv: st['e0_i_ge_e0j1_on_j0j1']+=1
    pr(f"[L={L}] host={st['host']} WGAP={st['WGAP']} sincr={st['sincr_window']} "
       f"all_le0_i_j0={st['all_le0_i_j0']} t={time.time()-t0:.0f}s")
pr("="*60)
pr(st)
for c in cex: pr("CEX",c)
