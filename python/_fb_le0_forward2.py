from red_model import *
def tile_cond(N):
    j1=Lng(N)-1
    if j1==0: return False
    if entry(N,0,j1)==0 and entry(N,1,j1)==0: return False
    i1=idx1(N,j1)
    return hasParent(N,i1,j1)
def RedCondA(M):
    for i in (0,1):
        for j1 in range(Lng(M)):
            if hasParent(M,i,j1) and entry(M,i,parent(M,i,j1))+1 != entry(M,i,j1): return False
    return True
def RedCondB(M):
    for j1 in range(Lng(M)):
        if not hasParent(M,0,j1) and entry(M,0,j1)!=entry(M,1,j1): return False
    return True
seeds=[diagSeq(a,b) for a in range(0,3) for b in range(a,a+4)]
seen=set(); forms=[]; frontier=[tuple(s) for s in seeds]
while frontier and len(seen)<4000:
    new=[]
    for k in frontier:
        if k in seen: continue
        seen.add(k); forms.append(k); M=list(k)
        if Lng(M)<=7:
            for n in range(1,3):
                Mn=oper(M,n)
                if 1<Lng(Mn)<=9: new.append(tuple(Mn))
    frontier=new

# Check the EXACT shape that matters: for the within1 parent of x in Nn, with
# x'=base(x), pN=parent N 1 x', need: le0 Nn p x where p=base-lifted pN into x's block,
# AND that p is the row-1 argmin.  Test instead the direct chain-confinement claim:
# le0 N a b with j0<=a, b<j1 (strict), via a chain all of whose nodes are in [j0,j1).
import sys
sys.setrecursionlimit(100000)
def le0_chain_in_block(N,a,b,j0,j1):
    # BFS within [j0,j1)
    if a==b: return True
    from collections import deque
    seen={a}; dq=deque([a])
    while dq:
        u=dq.popleft()
        for v in range(j0,j1):
            if v not in seen and nextrel0(N,u,v):
                if v==b: return True
                seen.add(v); dq.append(v)
    return b in seen
fwd_ok=fwd_bad=0
for k in forms:
    N=list(k)
    if not (tile_cond(N) and RedCondA(N) and RedCondB(N)): continue
    j1=Lng(N)-1; i1=idx1(N,j1); j0=parent(N,i1,j1); w=j1-j0
    if w<=0: continue
    for n in range(1,4):
        Nn=oper(N,n)
        for xp in range(j0, j1):
            for yp in range(xp, j1):
                if not le0_chain_in_block(N,xp,yp,j0,j1): continue
                for q in range(n):
                    tx=j0+q*w+(xp-j0); ty=j0+q*w+(yp-j0)
                    if tx>=Lng(Nn) or ty>=Lng(Nn): continue
                    if le0(Nn,tx,ty): fwd_ok+=1
                    else: fwd_bad+=1
print("block-confined forward le0 lift: ok",fwd_ok,"bad",fwd_bad)
