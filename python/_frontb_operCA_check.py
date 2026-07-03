import itertools
from red_model import *

def RedCondA(M):
    for i in (0,1):
        for j1 in range(Lng(M)):
            if hasParent(M,i,j1):
                j0=parent(M,i,j1)
                if entry(M,i,j0)+1 != entry(M,i,j1):
                    return False
    return True

def RedCondB(M):
    for j1 in range(Lng(M)):
        if (not hasParent(M,0,j1)) and j1 <= Lng(M)-1:
            if entry(M,0,j1)!=entry(M,1,j1):
                return False
    return True

def tile_cond(N):
    j1=Lng(N)-1
    if j1==0: return False
    if entry(N,0,j1)==0 and entry(N,1,j1)==0: return False
    i1=idx1(N,j1)
    if not hasParent(N,i1,j1): return False
    return True

# enumerate standard forms by applying oper repeatedly from diagSeq seeds
import random
random.seed(0)
seeds=[diagSeq(a,b) for a in range(0,3) for b in range(a,a+4)]
forms=set()
def key(M): return tuple(M)
work=list(seeds)
seen=set()
while work:
    M=work.pop()
    k=key(M)
    if k in seen: continue
    seen.add(k)
    forms.add(k)
    if Lng(M)<=8:
        for n in range(1,4):
            try:
                Mn=oper(M,n)
            except Exception:
                continue
            if Lng(Mn)<=10:
                work.append(Mn)

print("num forms",len(forms))
checked=0; fails=0
for k in forms:
    N=list(k)
    if not tile_cond(N): continue
    if not RedCondA(N): continue   # need RedCondA N as hypothesis
    if not RedCondB(N): continue
    j1=Lng(N)-1
    i1=idx1(N,j1)
    if not hasParent(N,i1,j1): continue
    for n in range(1,5):
        Nn=oper(N,n)
        checked+=1
        if not RedCondA(Nn):
            fails+=1
            if fails<=10:
                print("FAIL N=",fmt(N),"n=",n,"Nn=",fmt(Nn))
print("checked",checked,"fails",fails)
