from red_model import *
def build_closure(depth_max=5, ubound=3, vbound=6, maxlen=16):
    bases=[]
    for u in range(0,ubound+1):
        for v in range(u,vbound+1):
            bases.append(tuple(diagSeq(u,v)))
    seen=set(bases); frontier=list(bases); allM=set(bases); po={}
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
                    seen.add(t); allM.add(t); newf.append(t); po.setdefault(t,(M,n))
        frontier=newf
    return po
po=build_closure()
# For oper N=M[n]: endpoint jN = j0M+(n-1)*w + (w-1) = j0M + n*w -1.
# parent N 1 jN = ?  relate to parent M 1 (j0M+(w-1)) + (n-1)*w  via readback (s=w-1,q=n-1)
tot=0; bad=0
for tN,(M,n) in po.items():
    N=list(tN); M=list(M); L=Lng(M)
    if L<=1: continue
    j1M=L-1
    if entry(M,0,j1M)==0 and entry(M,1,j1M)==0: continue
    if idx1(M,j1M)!=1: continue
    if not hasParent(M,1,j1M): continue
    j0M=parent(M,1,j1M)
    if not(j0M<j1M): continue
    w=j1M-j0M
    jN=Lng(N)-1
    if not hasParent(N,1,jN): continue
    j0N=parent(N,1,jN)
    tot+=1
    # readback at s=w-1, q=n-1:  parent N 1 (j0M+(n-1)w+(w-1)) = parent M 1 (j0M+(w-1)) + (n-1)w
    if w>=1 and hasParent(M,1,j0M+(w-1)):
        pred = parent(M,1,j0M+(w-1)) + (n-1)*w
        if pred!=j0N:
            bad+=1
            if bad<6: print("ENDPT mismatch j0N",j0N,"pred",pred,"w",w,"n",n,fmt(M))
print("tot",tot,"endpoint readback bad",bad)
