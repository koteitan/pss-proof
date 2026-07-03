from red_model import *
def build_closure(depth_max=5, ubound=3, vbound=6, maxlen=16):
    bases=[]
    for u in range(0,ubound+1):
        for v in range(u,vbound+1):
            bases.append(tuple(diagSeq(u,v)))
    seen=set(bases); frontier=list(bases); allM=set(bases)
    for d in range(depth_max):
        newf=[]
        for M in frontier:
            Ml=list(M)
            for n in range(1,4):
                try: Nn=oper(Ml,n)
                except Exception: continue
                if len(Nn)<1 or len(Nn)>maxlen: continue
                t=tuple(Nn)
                if t not in seen:
                    seen.add(t); allM.add(t); newf.append(t)
        frontier=newf
    return [list(M) for M in allM]

# fullramp(N): N has strict interior row-1 ancestor (j0<j1, parent N 1 j1 = j0, j0 interior)
#   => for j0<=x<j1: entry N 0 (x+1) = entry N 0 x + 1
def fullramp_applicable(N):
    L=Lng(N)
    if L<=1: return None
    j1=L-1
    if not hasParent(N,1,j1): return None
    j0=parent(N,1,j1)
    if j0 is None or not (j0<j1): return None
    return (j0,j1)

Ms=build_closure()
tot=0; fail=0; ex=[]
for N in Ms:
    r=fullramp_applicable(N)
    if r is None: continue
    j0,j1=r
    tot+=1
    ok=all(entry(N,0,x+1)==entry(N,0,x)+1 for x in range(j0,j1))
    if not ok:
        fail+=1
        if len(ex)<8: ex.append((fmt(N),j0,j1))
print("fullramp applicable",tot,"fail",fail)
for e in ex: print("  FAIL",e)

print("=== restricted: N where some interior z is Ez-gated (pz>j0 and z>j0) ===")
tot2=0; fail2=0; ex2=[]
for N in Ms:
    r=fullramp_applicable(N)
    if r is None: continue
    j0,j1=r
    # require: exists interior z with hasParent N 1 z, parent N 1 z > j0, z>j0
    gated=[]
    for z in range(j0+1,j1):
        if hasParent(N,1,z) and parent(N,1,z) is not None and parent(N,1,z)>j0:
            gated.append(z)
    if not gated: continue
    tot2+=1
    ok=all(entry(N,0,x+1)==entry(N,0,x)+1 for x in range(j0,j1))
    if not ok:
        fail2+=1
        if len(ex2)<8: ex2.append((fmt(N),j0,j1,gated))
print("restricted fullramp applicable",tot2,"fail",fail2)
for e in ex2: print("  FAIL",e)
