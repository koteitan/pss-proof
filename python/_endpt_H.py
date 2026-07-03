from red_model import *
def build_closure(depth_max=5, ubound=3, vbound=6, maxlen=16):
    bases=[]
    for u in range(0,ubound+1):
        for v in range(u,vbound+1):
            bases.append(tuple(diagSeq(u,v)))
    seen=set(bases); frontier=list(bases); allM=set(bases); parentof={}
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
                    seen.add(t); allM.add(t); newf.append(t); parentof.setdefault(t,(M,n))
        frontier=newf
    return parentof
po=build_closure()
bad=0; tot=0
for tN,(M,n) in po.items():
    N=list(tN); M=list(M); L=Lng(M)
    if L<=1: continue
    j1M=L-1
    if entry(M,0,j1M)==0 and entry(M,1,j1M)==0: continue
    if idx1(M,j1M)!=1: continue
    if not hasParent(M,1,j1M): continue
    j0M=parent(M,1,j1M)
    if not(j0M<j1M): continue
    LN=Lng(N); jN=LN-1
    if jN<1: continue
    if not hasParent(N,1,jN): continue
    j0N=parent(N,1,jN)
    tot+=1
    # claim: j0N == j0M + (n-1)*w  (last block start parent) ? check vs j0M
    w=j1M-j0M
    if j0N != j0M+(n-1)*w:
        bad+=1
        if bad<8: print("MISMATCH j0N",j0N,"j0M",j0M,"n",n,"w",w,fmt(M))
print("tot",tot,"j0N!=j0M+(n-1)w bad",bad)
