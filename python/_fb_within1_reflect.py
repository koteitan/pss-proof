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

# within1: j0<=x<Lng(Nn), hasParent(Nn,1,x).
# x' = j0 + (x-j0) mod w  (base column)
# Claims:
#  hpN: hasParent N 1 x'
#  ex : entry Nn 1 x = entry N 1 x'
#  ep : entry Nn 1 (parent Nn 1 x) = entry N 1 (parent N 1 x')
hpN_ok=hpN_bad=0
ex_ok=ex_bad=0
ep_ok=ep_bad=0
within1_count=0
fails=[]
for k in forms:
    N=list(k)
    if not (tile_cond(N) and RedCondA(N) and RedCondB(N)): continue
    j1=Lng(N)-1; i1=idx1(N,j1); j0=parent(N,i1,j1); w=j1-j0
    if w<=0: continue
    if i1!=1:  # within1 only matters for d1=0 layout? Actually d1=0 when i1<=1; but for row1 reflection d1 always 0 since i1<=1
        pass
    for n in range(1,5):
        Nn=oper(N,n)
        for x in range(j0, Lng(Nn)):
            if not hasParent(Nn,1,x): continue
            within1_count+=1
            xb = j0 + (x-j0)%w
            # hpN
            if hasParent(N,1,xb): hpN_ok+=1
            else:
                hpN_bad+=1; fails.append(("hpN",tuple(N),n,x,xb))
            # ex
            if entry(Nn,1,x)==entry(N,1,xb): ex_ok+=1
            else:
                ex_bad+=1; fails.append(("ex",tuple(N),n,x,xb))
            # ep
            p=parent(Nn,1,x)
            if hasParent(N,1,xb):
                pN=parent(N,1,xb)
                if entry(Nn,1,p)==entry(N,1,pN): ep_ok+=1
                else:
                    ep_bad+=1; fails.append(("ep",tuple(N),n,x,xb,p,pN,entry(Nn,1,p),entry(N,1,pN)))
print("within1_count",within1_count)
print("hpN ok",hpN_ok,"bad",hpN_bad)
print("ex  ok",ex_ok,"bad",ex_bad)
print("ep  ok",ep_ok,"bad",ep_bad)
for f in fails[:20]: print("FAIL",f)
