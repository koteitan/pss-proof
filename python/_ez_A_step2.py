import sys
from red_model import diagSeq, oper, fmt
from _ez_A_fast import (Lng,entry,nextrel1,le0reach,hasParent1,parent1,idx1,build_closure)

# For N=M[n], the interior z with strict row-1 ancestor (pz>j0N). Decompose z and
# check it lands in the tiled blocks (z>=j0M) and that its M-side preimage z0=j0M+(z-j0M)%w
# has a strict M-side row-1 ancestor too. Also verify the row-0 ramp lift:
# entry N 0 j1N - entry N 0 z == (j1N - z)  AND  it equals M-side total over its tail.

def analyze(M,n):
    N=oper(M,n)
    LN=Lng(N)
    if LN<=1: return []
    LM=Lng(M); j1M=LM-1
    if j1M==0: return []
    if entry(M,0,j1M)==0 and entry(M,1,j1M)==0: return []
    if idx1(M,j1M)!=1: return []
    if not hasParent1(M,j1M): return []
    j0M=parent1(M,j1M)
    if j0M is None or not (j0M<j1M): return []
    w=j1M-j0M
    j1N=LN-1
    if not hasParent1(N,j1N): return []
    j0N=parent1(N,j1N)
    if j0N is None: return []
    out=[]
    for z in range(1,j1N):
        if not hasParent1(N,z): continue
        pz=parent1(N,z)
        if pz is None: continue
        if not (pz>j0N and z>j0N): continue
        # decompose
        if z<j0M:
            loc=("prefix",z)
            Mside=None
        else:
            q=(z-j0M)//w; s=(z-j0M)%w
            loc=("block",q,s)
            z0=j0M+s
            # M-side ancestor of z0
            Manc = parent1(M,z0) if hasParent1(M,z0) else None
            Mside=(z0,s,Manc)
        ez_ok = (entry(N,0,j1N)==entry(N,0,z)+(j1N-z))
        out.append((z,loc,Mside,ez_ok))
    return out

if __name__=="__main__":
    Ms=build_closure()
    tot=0; prefix=0; block=0; ez_fail=0
    # for block case: does M-side preimage z0 have strict ancestor (Manc>j0M)?
    block_Manc_strict=0; block_Manc_notstrict=0; block_s0=0
    ex=[]
    for M in Ms:
        for n in range(1,4):
            for (z,loc,Mside,ez_ok) in analyze(M,n):
                tot+=1
                if not ez_ok:
                    ez_fail+=1
                    if len(ex)<6: ex.append((fmt(M),n,z,loc,Mside))
                if loc[0]=="prefix":
                    prefix+=1
                else:
                    block+=1
                    q,s=loc[1],loc[2]
                    if s==0:
                        block_s0+=1
                    else:
                        z0,ss,Manc=Mside
                        if Manc is not None and Manc>parent1(M,Lng(M)-1):
                            block_Manc_strict+=1
                        else:
                            block_Manc_notstrict+=1
    print("interior strict-anc z total",tot,"ez_fail",ez_fail)
    print("loc: prefix",prefix,"block",block,"(s0",block_s0,")")
    print("block s>0: Manc strict",block_Manc_strict,"Manc not-strict",block_Manc_notstrict)
    for e in ex: print("EZFAIL",e)
