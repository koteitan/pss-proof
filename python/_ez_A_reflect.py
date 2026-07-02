from red_model import oper, fmt, diagSeq
from _ez_A_fast import (Lng,entry,nextrel1,le0reach,hasParent1,parent1,idx1,build_closure)

# Hypothesis to pin: for N=M[n] with gated interior z,
#  (A) block case z=j0M+q*w+s (s>0): Ez_N(z) follows from Ez_M(z0) where z0=j0M+s,
#      via row-0 tile arithmetic.  entry N 0 j1N = entry M 0 j1M + (n-1)*d0  (last block endpoint)
#      entry N 0 z = entry M 0 z0 + q*d0
#      so Ez_N: entry M0 j1M + (n-1)d0 = entry M0 z0 + q*d0 + (j1N - z)
#      j1N - z = (n-1-q)*w + (w-1 - (s-1))? compute. Want this to match Ez_M(z0): entry M0 j1M = entry M0 z0 + (j1M - z0) = entry M0 z0 + (w-s).
#  (B) prefix case z<j0M: relate to M-side endpoint via Ez_M(z) directly? z<j0M so z0=z.
# Just verify (A) and (B) reductions hold as identities given Ez_M.

def check(M,n):
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
    d0=entry(M,0,j1M)-entry(M,0,j0M)
    j1N=LN-1
    if not hasParent1(N,j1N): return []
    j0N=parent1(N,j1N)
    if j0N is None: return []
    out=[]
    for z in range(1,j1N):
        if not hasParent1(N,z): continue
        pz=parent1(N,z)
        if pz is None or not (pz>j0N and z>j0N): continue
        # Ez_M holds? compute M-side endpoint fact relevant
        if z>=j0M:
            q=(z-j0M)//w; s=(z-j0M)%w
            z0=j0M+s
            # Ez_M at z0 (M-side): does entry M0 j1M == entry M0 z0 + (j1M - z0)?
            ez_M = (entry(M,0,j1M)==entry(M,0,z0)+(j1M-z0))
            # endpoint of N row0:
            eNj1 = entry(N,0,j1N)
            # last column: block n-1, offset w-1 -> preimage j0M+(w-1)=j1M-1
            pred_eNj1 = entry(M,0,j1M-1)+(n-1)*d0
            eNz = entry(N,0,z)
            pred_eNz = entry(M,0,z0)+q*d0
            kind="block"
            ok = (eNj1==pred_eNj1) and (eNz==pred_eNz) and ez_M
            out.append((z,kind,ez_M,eNj1==pred_eNj1,eNz==pred_eNz))
        else:
            kind="prefix"
            # z verbatim: entry N 0 z == entry M 0 z
            eNz_pref = (entry(N,0,z)==entry(M,0,z))
            out.append((z,kind,eNz_pref,None,None))
    return out

if __name__=="__main__":
    Ms=build_closure()
    block=0; block_ezM_fail=0; block_endpt_fail=0; block_z_fail=0
    prefix=0; prefix_fail=0
    ex=[]
    for M in Ms:
        for n in range(1,4):
            for r in check(M,n):
                if r[1]=="block":
                    block+=1
                    z,kind,ezM,endpt,zf=r
                    if not ezM: block_ezM_fail+=1
                    if not endpt: block_endpt_fail+=1
                    if not zf: block_z_fail+=1
                    if (not ezM or not endpt or not zf) and len(ex)<6: ex.append((fmt(M),n,r))
                else:
                    prefix+=1
                    if not r[2]: prefix_fail+=1
    print("block",block,"ezM_fail",block_ezM_fail,"endpt_fail",block_endpt_fail,"z_fail",block_z_fail)
    print("prefix",prefix,"verbatim_fail",prefix_fail)
    for e in ex: print("EX",e)
