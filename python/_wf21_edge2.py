import itertools
from red_model import *

def is_core_nontrunk(M):
    if not monoT(M): return False
    if entry(M,0,0)!=0 or entry(M,1,0)!=0: return False
    if Red(M)!=M: return False
    if TrMax(M)==Lng(M)-1: return False
    return True

# Examine the column mapping M col j -> N col (j-m+m1m) for j>=m, and trunk col p->p
checked=0; r1=0; fails=[]
detail_printed=0
for L in range(2,6):
  for cols in itertools.product(itertools.product(range(4),range(4)),repeat=L-1):
    M=[(0,0)]+list(cols)
    if not is_core_nontrunk(M): continue
    Brs=Br(M)
    if len(Brs)==0: continue
    Jstar=len(Brs)-1
    B=Brs[Jstar]; kk=Lng(B)-1
    if not kk>0: continue
    j1=Lng(M)-1
    if not hasParent(M,1,j1): continue
    p=parent(M,1,j1)
    off=FirstNodes(M)[Jstar]
    if not (p<off): continue
    r1+=1
    m=off; m1m=entry(M,1,m); RB=Red(B)
    N=diagSeq(0,m1m-1)+RB if m1m>0 else RB
    lastN=Lng(N)-1
    # Check: nextrel1 M p j1 holds (it's the parent edge)
    e_par = nextrel1(M,1,p,j1) if False else nextR(M,1,p,j1)
    # Check edge preservation: nextrel1 N p lastN
    e_N = nextR(N,1,p,lastN)
    # Also: p<=TrMax  (trunk)  and entry N 1 p = p (diagonal)
    pTr = p<=TrMax(M)
    eNp = entry(N,1,p)
    # mapping of last col: lastN = j1 - m + m1m
    lastform = lastN==(j1-m+m1m)
    # Check Red B = seg of N: N tail = Red B at cols m1m.. lastN
    # entry transfer for ALL cols j in [m..j1]: entry N 1 (j-m+m1m) ?= entry M 1 j ??? 
    # Actually Red B != seg M m j1 in value (Red changes row0). Row1?
    # the article maps via Red(B). check entry N 1 lastN = entry (Red B) 1 kk
    eRBkk = entry(RB,1,kk)
    eNlast=entry(N,1,lastN)
    if not (e_par and e_N and pTr and eNp==p and lastform):
      fails.append((M,dict(e_par=e_par,e_N=e_N,pTr=pTr,eNp=eNp,p=p,lastform=lastform,m=m,m1m=m1m)))
print("r1cross",r1,"fails",len(fails))
for f in fails[:15]: print("FAIL",fmt(f[0]),f[1])
