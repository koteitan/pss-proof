from red_model import *
from _bridge_H import build_closure, gated_interior
import sys; sys.setrecursionlimit(20000)
def has_gz(N):
    for _ in gated_interior(N): return True
    return False
def gatedM(M):
    L=Lng(M)
    if L<=2: return None
    j1=L-1
    if entry(M,0,j1)==0 and entry(M,1,j1)==0: return None
    if idx1(M,j1)!=1: return None
    if not hasParent(M,1,j1): return None
    j0=parent(M,1,j1)
    if not(j0<j1): return None
    return (j0,j1)
def D(N):
    L=Lng(N)
    if L<1: return True
    return entry(N,0,L-1)==entry(N,0,0)+(L-1)
Ms,_=build_closure(depth_max=4, ubound=3, vbound=7, maxlen=14)
w1_tot=w1_fail=0; w1ex=[]
wg_tot=wg_fail=0; wgex=[]
for M in Ms:
    g=gatedM(M)
    if g is None: continue
    j0M,j1M=g; w=j1M-j0M
    if w==1:
        w1_tot+=1
        if not D(M):
            w1_fail+=1
            if len(w1ex)<8: w1ex.append((fmt(M),j0M,j1M))
    else:
        for n in range(1,4):
            try: N=oper(M,n)
            except Exception: continue
            LN=Lng(N)
            if LN<1 or LN>40: continue
            if has_gz(N):
                wg_tot+=1
                if not has_gz(M):
                    wg_fail+=1
                    if len(wgex)<8: wgex.append((fmt(M),n))
print('(W1) gated M, w=1 => D(M):',w1_tot,'fail',w1_fail)
for e in w1ex: print('  W1FAIL',e)
print('(WG) gated M, w>1, has_gz(M[n]) => has_gz(M):',wg_tot,'fail',wg_fail)
for e in wgex: print('  WGFAIL',e)
