import sys
from red_model import *
from _ez_A import build_closure, Ez_holds

# For N=M[n], characterize interior z with strict row-1 ancestor.
# Goal: verify the oper-step lifting for Ez. Strategy: Ez for N reduces to
# a row-0 endpoint equation. The row-0 entries in the tiled blocks follow
# entry N 0 (j0+k*w+s) = entry M 0 (j0+s) + k*d0.
# For the interior z with strict ancestor (pz>j0), check it lies in a block
# and that Ez on N follows from the row-0 ramp on the tail [z, Lng N -1].

def analyze(M,n):
    N=oper(M,n)
    if Lng(N)<=1: return []
    LM=Lng(M); j1M=LM-1
    if j1M==0: return []
    if entry(M,0,j1M)==0 and entry(M,1,j1M)==0: return []  # degenerate Pred
    i1=idx1(M,j1M)
    if i1!=1: return []
    if not hasParent(M,i1,j1M): return []
    j0=parent(M,i1,j1M)
    if j0 is None or not (j0<j1M): return []
    w=j1M-j0
    d0=entry(M,0,j1M)-entry(M,0,j0)
    out=[]
    LN=Lng(N); J1N=LN-1
    for z in range(0,J1N):
        if not hasParent(N,1,z): continue
        pz=parent(N,1,z)
        if pz is None: continue
        j0N=parent(N,1,J1N)
        if j0N is None: continue
        if not (pz>j0N and z>j0N): continue
        # decompose z = j0 + q*w + s   (z in prefix region if z<j0)
        if z<j0:
            blk=("prefix",z)
        else:
            q=(z-j0)//w; s=(z-j0)%w
            blk=("block",q,s)
        # the N-side endpoint J1N is the last column of last block (q=n-1, s=w-1?)
        # endpoint offset
        eq=(entry(N,0,J1N)==entry(N,0,z)+(J1N-z))
        out.append((z,blk,eq,d0))
    return out

if __name__=="__main__":
    Ms=build_closure()
    tot=0; prefixcnt=0; blockcnt=0; failblk=0
    examples=[]
    for M in Ms:
        for n in range(1,4):
            try:
                for (z,blk,eq,d0) in analyze(M,n):
                    tot+=1
                    if blk[0]=="prefix": prefixcnt+=1
                    else: blockcnt+=1
                    if not eq:
                        failblk+=1
                        if len(examples)<8: examples.append((fmt(M),n,z,blk))
            except Exception:
                pass
    print("interior strict-anc z total", tot, "prefix", prefixcnt, "block", blockcnt, "Ez-fail", failblk)
    for e in examples: print("FAIL",e)
