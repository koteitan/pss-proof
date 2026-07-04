#!/usr/bin/env python3
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, monoT, seg, parent, Adm, adm, Br, FirstNodes,
                       Joints, Red, hasParent, fmt, TrMax, Pred, is_standard)
from trans_model import Dpt, ZB, bpHeadT, bpHeadV, PB, SigmaB, Trans, Mark

def is_reduced(M): return Red(list(M)) == list(M)
def transJ0(M): return parent(M, 0, Lng(M)-1)
def condII(M):
    n=Lng(M)
    if n<3 or not hasParent(M,0,n-1): return False
    return entry(M,1,n-1)==0 and not adm(M,transJ0(M))
def genuineII(M):
    return condII(M) and Lng(M)-1>1 and monoT(M) and is_reduced(M)
def c2sx_ldj(M):
    j0=transJ0(M); jm1=Adm(M,j0); c1=Mark(Pred(M),jm1); t2=bpHeadT(c1)
    if t2==ZB: return None
    return bpHeadV(PB(t2)[-1])==entry(M,1,j0)

def descending(bs):
    for J0 in range(len(bs)):
        for J1 in range(J0,len(bs)):
            a0,b0=bs[J0][0]; a1,b1=bs[J1][0]
            if not (a0>=a1 and (a0!=a1 or b0>=b1)): return False
    return True

def diag(M, tag):
    j1=Lng(M)-1; j0=transJ0(M); jm1=Adm(M,j0); d=j0-jm1
    R84=Red(seg(M,jm1,j1)); Rc=Red(seg(M,jm1,j1-1))
    print(f"--- {tag}: M={fmt(M)} std={is_standard(M)} ldj={c2sx_ldj(M)}")
    print(f"    j1={j1} j0={j0} jm1={jm1} d={d}")
    print(f"    seg(jm1,j1)={fmt(seg(M,jm1,j1))} R84={fmt(R84)}")
    print(f"    seg(jm1,j1-1)={fmt(seg(M,jm1,j1-1))} Rc={fmt(Rc)}")
    for nm,R in [('R84',R84),('Rc',Rc)]:
        b=Br(R)
        if b:
            J1=len(b)-1
            print(f"    {nm}: Lng={Lng(R)} TrMax={TrMax(R)} BrLen={len(b)} "
                  f"Joints={Joints(R)} FirstNodes={FirstNodes(R)} "
                  f"Joints!last={Joints(R)[J1]} FN!last={FirstNodes(R)[J1]} desc={descending(b)}")
        else:
            print(f"    {nm}: Lng={Lng(R)} TrMax={TrMax(R)} Br=[] (trunk={TrMax(R)==Lng(R)-1})")

# the standard leftDj0 CEX
diag([(0,0),(1,1),(2,2),(2,0),(2,0)], "A36 leftDj0 std")

# hunt not-leftDj0 genuine condII hosts
cells=[(a,b) for a in range(4) for b in range(4)]
cnt=0
for L in range(4,7):
    for tup in itertools.product(cells, repeat=L-1):
        M=[(0,0)]+list(tup)
        if not genuineII(M): continue
        ld=c2sx_ldj(M)
        if ld is None or ld: continue
        cnt+=1
        if cnt<=6: diag(M, f"notLDJ#{cnt} L={L}")
    if cnt>=6: break
print(f"total notLDJ found (partial)={cnt}")
