import itertools
from red_model import *
def is_core_nontrunk(M):
    return monoT(M) and entry(M,0,0)==0 and entry(M,1,0)==0 and Red(M)==M and TrMax(M)!=Lng(M)-1
r1=0; f=[]
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
    RB=Red(B)
    # Red B in RT_PS and PT_PS?
    checks=dict(
      B_mono=monoT(B),
      RB_reduced=Red(RB)==RB,
      RB_mono=monoT(RB),
      RB_e00=entry(RB,0,0),  # leftend row0
      RB_e10=entry(RB,1,0),  # leftend row1 = m1m?
      m1m=entry(M,1,off),
      Bm1m=entry(B,1,0),
    )
    if not(checks['B_mono'] and checks['RB_reduced'] and checks['RB_mono'] and checks['RB_e10']==checks['m1m']):
      f.append((M,checks))
print("r1",r1,"fails",len(f))
for x in f[:10]: print(fmt(x[0]),x[1])
