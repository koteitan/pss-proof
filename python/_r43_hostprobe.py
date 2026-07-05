import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import (Lng, entry, monoT, seg, oper, diagSeq, Br, FirstNodes, Joints, Red, TrMax)
import _r36_bridges as B
def norm(M): return [tuple(p) for p in M]
def is_reduced(M): return norm(Red(norm(M)))==norm(M)
def descending(bs):
    for J0 in range(len(bs)):
        for J1 in range(J0,len(bs)):
            a0,b0=bs[J0][0]; a1,b1=bs[J1][0]
            if not (a0>=a1 and (a0!=a1 or b0>=b1)): return False
    return True
def reg7x(M):
    if Lng(M)-1<=1: return False
    if not monoT(M): return False
    b=Br(M)
    if not b: return False
    J1=len(b)-1; fn=FirstNodes(M); jt=Joints(M)
    j1p=fn[J1]; j0p=jt[J1]
    if j1p is None or j0p is None: return False
    if not (entry(M,1,j1p)<entry(M,0,j1p)): return False
    if not (0<j0p and j0p<TrMax(M)): return False
    if not descending(b): return False
    if not is_reduced(M): return False
    return True
t0=time.time(); found=0; ok=0; fails=[]
cells=[(a,b) for a in range(4) for b in range(4)]
for L in range(4,8):
    if time.time()-t0>400: break
    for tup in itertools.product(cells, repeat=L-1):
        M=[(0,0)]+list(tup)
        if not reg7x(M): continue
        found+=1
        r=B.check_bridges(M)
        if r[0]=='ok': ok+=1
        else:
            if len(fails)<8: fails.append((r, B.LastStep(M)))
    print(f"L={L} found={found} ok={ok} t={time.time()-t0:.0f}s", flush=True)
print("TOTAL found=%d ok=%d"%(found,ok), flush=True)
for f in fails: print("FAIL", f, flush=True)
