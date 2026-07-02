import sys
from red_model import *

# Build broad ST_PS closure: diag bases + oper closure depth>=5
def build_closure(depth_max=5, ubound=3, vbound=6, maxlen=16):
    bases=[]
    for u in range(0,ubound+1):
        for v in range(u,vbound+1):
            bases.append(tuple(diagSeq(u,v)))
    seen=set(bases)
    frontier=list(bases)
    allM=set(bases)
    for d in range(depth_max):
        newf=[]
        for M in frontier:
            Ml=list(M)
            for n in range(1,4):
                try:
                    Nn=oper(Ml,n)
                except Exception:
                    continue
                if len(Nn)<1 or len(Nn)>maxlen: continue
                t=tuple(Nn)
                if t not in seen:
                    seen.add(t); allM.add(t); newf.append(t)
        frontier=newf
    return [list(M) for M in allM]

def Ez_holds(N):
    # returns (applicable, ok) over interior z with strict row-1 ancestor
    L=Lng(N)
    if L<=1: return []
    j1=L-1
    if not hasParent(N,1,j1): return []
    j0=parent(N,1,j1)
    if j0 is None or not (j0<j1): return []
    res=[]
    for z in range(0,j1):
        if not hasParent(N,1,z): continue
        pz=parent(N,1,z)
        if pz is None: continue
        # interior gating: pz > j0  and  z > j0
        if not (pz>j0 and z>j0): continue
        lhs=entry(N,0,j1)
        rhs=entry(N,0,z)+(j1-z)
        res.append((z,lhs==rhs,lhs,rhs))
    return res

if __name__=="__main__":
    Ms=build_closure()
    print("closure size", len(Ms))
    tot=0; fail=0; failex=[]
    for N in Ms:
        for (z,ok,lhs,rhs) in Ez_holds(N):
            tot+=1
            if not ok:
                fail+=1
                if len(failex)<8: failex.append((fmt(N),z,lhs,rhs))
    print("Ez applicable", tot, "fail", fail)
    for e in failex: print("FAIL",e)
