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

# For within1: x>=j0, hasParent Nn 1 x.
# x' = j0 + (x-j0) mod w. p = parent Nn 1 x. pN = parent N 1 x'.
# Check: is entry Nn 1 p == entry N 1 pN ? Already verified (ep).
# Also check the base-of-p relationship: base(p) related to pN?
# And: idx1 of x in Nn -- is it always 1 (so hasParent Nn 1 x meaningful)?
# Key question for the proof: i1 value distribution.
i1_count={}
base_p_eq_pN=0; base_p_ne=0
for k in forms:
    N=list(k)
    if not (tile_cond(N) and RedCondA(N) and RedCondB(N)): continue
    j1=Lng(N)-1; i1=idx1(N,j1); j0=parent(N,i1,j1); w=j1-j0
    if w<=0: continue
    i1_count[i1]=i1_count.get(i1,0)+1
    for n in range(1,5):
        Nn=oper(N,n)
        for x in range(j0, Lng(Nn)):
            if not hasParent(Nn,1,x): continue
            xb = j0 + (x-j0)%w
            if not hasParent(N,1,xb): continue
            p=parent(Nn,1,x); pN=parent(N,1,xb)
            # base of p:
            bp = p if p<j0 else j0+(p-j0)%w
            if bp==pN: base_p_eq_pN+=1
            else: base_p_ne+=1
print("i1_count(over forms)",i1_count)
print("base(p)==pN:",base_p_eq_pN,"  base(p)!=pN:",base_p_ne)
