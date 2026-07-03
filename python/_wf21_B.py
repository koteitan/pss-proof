import itertools
from red_model import *
def is_core_nontrunk(M):
    return monoT(M) and entry(M,0,0)==0 and entry(M,1,0)==0 and Red(M)==M and TrMax(M)!=Lng(M)-1
r1=0; bmono=0; bzero=0; fail=[]
for L in range(2,6):
  for cols in itertools.product(itertools.product(range(4),range(4)),repeat=L-1):
    M=[(0,0)]+list(cols)
    if not is_core_nontrunk(M): continue
    Brs=Br(M)
    if len(Brs)==0: continue
    Jstar=len(Brs)-1; B=Brs[Jstar]; kk=Lng(B)-1
    if not kk>0: continue
    j1=Lng(M)-1
    if not hasParent(M,1,j1): continue
    p=parent(M,1,j1); off=FirstNodes(M)[Jstar]
    if not p<off: continue
    r1+=1
    if monoT(B): bmono+=1
    elif zeroT(B): bzero+=1
    # m1m = entry M 1 m  vs entry B 1 0
    m=off
    if entry(M,1,m)!=entry(B,1,0): fail.append(("m1m",M))
    # B reduced? B = seg, is it reduced? we need Red B reduced - always true. is B itself reduced?
    # raw N route uses Red B, B need not be reduced
print("r1",r1,"B mono",bmono,"B zero",bzero,"fails",len(fail))
for f in fail[:10]: print(f[0],fmt(f[1]))
