import itertools
from red_model import *
def core(M): return monoT(M) and entry(M,0,0)==0 and entry(M,1,0)==0 and Red(M)==M and TrMax(M)!=Lng(M)-1
r1=0; zeroM1m=0
for L in range(2,6):
  for cols in itertools.product(itertools.product(range(4),range(4)),repeat=L-1):
    M=[(0,0)]+list(cols)
    if not core(M): continue
    Brs=Br(M)
    if not Brs: continue
    Jstar=len(Brs)-1; B=Brs[Jstar]; kk=Lng(B)-1
    if not kk>0: continue
    j1=Lng(M)-1
    if not hasParent(M,1,j1): continue
    p=parent(M,1,j1); off=FirstNodes(M)[Jstar]
    if not p<off: continue
    r1+=1
    if entry(Red(B),1,0)==0: zeroM1m+=1
print("r1cross",r1,"with entry(RedB,1,0)==0:",zeroM1m)
