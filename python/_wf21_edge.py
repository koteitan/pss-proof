import itertools
from red_model import *

def is_core_nontrunk(M):
    if not monoT(M): return False
    if entry(M,0,0)!=0 or entry(M,1,0)!=0: return False
    if Red(M)!=M: return False
    if TrMax(M)==Lng(M)-1: return False
    return True

# r1cross domain: row-1 cross-block kk>0
checked=0; r1=0; fails=[]
for L in range(2,6):
  for cols in itertools.product(itertools.product(range(4),range(4)),repeat=L-1):
    M=[(0,0)]+list(cols)
    if not is_core_nontrunk(M): continue
    checked+=1
    Brs=Br(M); 
    if len(Brs)==0: continue
    Jstar=len(Brs)-1
    kk=Lng(NJ(M,Jstar))-1 if 'NJ' in dir() else None
    # NJ length = Lng(Br[Jstar]) since head#tl
    B=Brs[Jstar]
    kk=Lng(B)-1
    if not kk>0: continue
    j1=Lng(M)-1
    if not hasParent(M,1,j1): continue
    p=parent(M,1,j1)
    off=FirstNodes(M)[Jstar]
    if not (p<off): continue   # cross-block
    r1+=1
    # raw N route
    m=Lng(M)-Lng(B)   # = off
    assert m==off, (M,m,off)
    m1m=entry(M,1,m)
    RB=Red(B)
    N=diagSeq(0,m1m-1)+RB if m1m>0 else RB
    # goal: entry M 1 p + 1 = entry M 1 j1
    goal = entry(M,1,p)+1==entry(M,1,j1)
    # witness edge in N: parent maps p (trunk, p<=TrMax<m, on diagonal) -> p ; j1 -> Lng N-1
    lastN=Lng(N)-1
    # N at column p: trunk diagonal => entry N 1 p = p
    # the parent of lastN in N should be p
    edge = hasParent(N,1,lastN) and parent(N,1,lastN)==p
    # entry transfer
    et1 = entry(N,1,p)==entry(M,1,p)
    et2 = entry(N,1,lastN)==entry(M,1,j1)
    Nred = Red(N)==N and monoT(N) and entry(N,0,0)==0 and entry(N,1,0)==0
    Nshort = lastN<j1
    if not (goal and edge and et1 and et2 and Nred and Nshort):
      fails.append((M,dict(goal=goal,edge=edge,et1=et1,et2=et2,Nred=Nred,Nshort=Nshort,p=p,m=m,m1m=m1m,lastN=lastN,j1=j1)))
print("checked cores",checked,"r1cross cases",r1,"fails",len(fails))
for f in fails[:15]:
  print("FAIL",fmt(f[0]),f[1])
