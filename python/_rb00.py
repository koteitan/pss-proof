import itertools
from red_model import *
# For reduced monoT M: does entry M 1 0 = 0 imply entry M 0 0 = 0?
fail=[]; chk=0
for L in range(1,6):
  for cols in itertools.product(itertools.product(range(4),range(4)),repeat=L):
    M=list(cols)
    if not monoT(M): continue
    if Red(M)!=M: continue
    chk+=1
    if entry(M,1,0)==0 and entry(M,0,0)!=0:
      fail.append(M)
print("reduced monoT checked",chk,"fails(e10=0,e00!=0)",len(fail))
for f in fail[:8]: print(fmt(f))
# also: is e00<=e10 for reduced monoT? (i.e. row0<=row1 at col0)
f2=[]
for L in range(1,5):
  for cols in itertools.product(itertools.product(range(4),range(4)),repeat=L):
    M=list(cols)
    if not monoT(M) or Red(M)!=M: continue
    if not entry(M,0,0)==entry(M,1,0): f2.append((M,entry(M,0,0),entry(M,1,0)))
print("reduced monoT with e00 != e10:",len(f2))
for x in f2[:8]: print(fmt(x[0]),x[1],x[2])
