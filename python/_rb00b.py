import itertools
from red_model import *
fail=[]; chk=0
for L in range(1,5):
  for cols in itertools.product(itertools.product(range(4),range(4)),repeat=L):
    M=list(cols)
    if not monoT(M) or Red(M)!=M: continue
    chk+=1
    if entry(M,1,0)==0 and entry(M,0,0)!=0: fail.append(M)
print("reduced monoT checked",chk,"fails(e10=0,e00!=0)",len(fail))
