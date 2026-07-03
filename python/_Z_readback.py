import itertools, sys
from red_model import *
from _Z_closure import build_closure

# We are in the oper readback setting of oper_parent1_readback_interior.
# M base; N = M[n] = oper(M,n).
# Preconditions of the lemma:
#   1 < Lng M
#   not (entry M 0 (Lng M -1)=0 and entry M 1 (Lng M -1)=0)
#   hasParent M (idx1 M (Lng M-1)) (Lng M-1)
#   idx1 M (Lng M -1) = 1
#   j0lt: parent M 1 (Lng M-1) < Lng M -1
# Then j0 = parent M 1 (Lng M-1), w = (Lng M-1) - j0.
# N = oper(M,n): N = M[:j0] ++ n copies of block [j0,j1) with d0,d1 increments.
# Here i1=1 so d0=0, d1=0 (entry-wise unchanged copies! per oper code i1>0 => d0 set, i1>1 => d1=0).
# Actually code: d0 = entry diff if i1>0 else 0; d1 = entry diff if i1>1 else 0.
# i1=1 => d0 = entry M 0 j1 - entry M 0 j0, d1=0.

def setup(M,n):
    j1=Lng(M)-1
    if j1<1: return None
    if entry(M,0,j1)==0 and entry(M,1,j1)==0: return None
    i1=idx1(M,j1)
    if i1!=1: return None
    if not hasParent(M,i1,j1): return None
    j0=parent(M,i1,j1)
    if not (j0<j1): return None
    w=j1-j0
    if w<=0: return None
    N=oper(M,n)
    return j0,j1,w,N,i1

# TASK 2: boundary s=0.  z = j0 + q*w  (block start of block q, q in 0..n-1)
# Claim: parent N 1 z lands in the PREFIX x < j0.  q=0 -> parent M 1 j0 ; q>=1 distinct prefix.
def task2_boundary():
    Pcl=build_closure(depth=5, maxlen=16)
    tot=0; prefix_ok=0; rows=[]
    formula_q0=0; formula_q0_tot=0
    for M in Pcl:
        for n in range(2,5):
            s=setup(M,n)
            if s is None: continue
            j0,j1,w,N,i1=s
            Ln=Lng(N)
            for q in range(0,n):
                z=j0+q*w
                if z>=Ln: continue
                if not hasParent(N,1,z): continue
                p=parent(N,1,z)
                tot+=1
                if p<j0:
                    prefix_ok+=1
                # q=0 formula check: parent N 1 j0 == parent M 1 j0 ?
                if q==0:
                    formula_q0_tot+=1
                    if hasParent(M,1,j0) and p==parent(M,1,j0):
                        formula_q0+=1
                rows.append((q,z,p,j0))
    print("TASK2 boundary s=0: total", tot, "parent-in-prefix(p<j0):", prefix_ok)
    print("  q=0: parent N 1 j0 == parent M 1 j0 :", formula_q0, "/", formula_q0_tot)
    # show a few q>=1 rows
    print("  sample (q,z,parent,j0):", rows[:15])

if __name__=="__main__":
    task2_boundary()
