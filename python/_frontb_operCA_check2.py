import itertools
from red_model import *

def RedCondA(M):
    for i in (0,1):
        for j1 in range(Lng(M)):
            if hasParent(M,i,j1):
                j0=parent(M,i,j1)
                if entry(M,i,j0)+1 != entry(M,i,j1):
                    return (False,i,j1,j0)
    return (True,)

def RedCondB(M):
    for j1 in range(Lng(M)):
        if not hasParent(M,0,j1):
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

# Build standard forms via BFS but cap and dedupe aggressively
seeds=[diagSeq(a,b) for a in range(0,3) for b in range(a,a+4)]
seen=set(); forms=[]
frontier=[tuple(s) for s in seeds]
while frontier and len(seen)<4000:
    new=[]
    for k in frontier:
        if k in seen: continue
        seen.add(k); forms.append(k)
        M=list(k)
        if Lng(M)<=7:
            for n in range(1,3):
                Mn=oper(M,n)
                if 1<Lng(Mn)<=9:
                    new.append(tuple(Mn))
    frontier=new

print("num forms",len(forms))
checked=0; fails=0
for k in forms:
    N=list(k)
    if not tile_cond(N): continue
    if RedCondA(N)[0] is False: continue
    if not RedCondB(N): continue
    for n in range(1,5):
        Nn=oper(N,n)
        checked+=1
        r=RedCondA(Nn)
        if r[0] is False:
            fails+=1
            if fails<=10:
                print("FAIL N=",fmt(N),"n=",n,"i,j1,j0=",r[1:],"Nn=",fmt(Nn))
print("checked",checked,"fails",fails)
