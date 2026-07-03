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

# Forward le0 within-block lift:
# if le0 N x' y' with j0<=x'<=y'<=j1, then le0 Nn (j0+q*w+(x'-j0)) (j0+q*w+(y'-j0)) for q<n.
fwd_ok=fwd_bad=0
for k in forms:
    N=list(k)
    if not (tile_cond(N) and RedCondA(N) and RedCondB(N)): continue
    j1=Lng(N)-1; i1=idx1(N,j1); j0=parent(N,i1,j1); w=j1-j0
    if w<=0: continue
    for n in range(1,4):
        Nn=oper(N,n)
        for xp in range(j0, j1+1):
            for yp in range(xp, j1+1):
                if not le0(N,xp,yp): continue
                for q in range(n):
                    tx=j0+q*w+(xp-j0); ty=j0+q*w+(yp-j0)
                    if tx>=Lng(Nn) or ty>=Lng(Nn): continue
                    if le0(Nn,tx,ty): fwd_ok+=1
                    else: fwd_bad+=1
print("forward le0 within-block lift: ok",fwd_ok,"bad",fwd_bad)
