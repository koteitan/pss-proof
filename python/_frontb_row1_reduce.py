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
while frontier and len(seen)<3000:
    new=[]
    for k in frontier:
        if k in seen: continue
        seen.add(k); forms.append(k); M=list(k)
        if Lng(M)<=7:
            for n in range(1,3):
                Mn=oper(M,n)
                if 1<Lng(Mn)<=9: new.append(tuple(Mn))
    frontier=new

# Claim tests:
# (within) x=j0+q*w+s, s>0, parent at j0+q*w+sp with sp = parent N 1 (j0+s) - in same block
# verify: parent(Nn,1,x) - q*w == parent(N,1,j0+s) essentially. And entry+1 reduces to RedCondA N.
c_within_ok=0; c_within_bad=0
c_bd_ok=0; c_bd_bad=0
c_pref_ok=0; c_pref_bad=0
for k in forms:
    N=list(k)
    if not (tile_cond(N) and RedCondA(N) and RedCondB(N)): continue
    j1=Lng(N)-1; i1=idx1(N,j1); j0=parent(N,i1,j1); w=j1-j0
    for n in range(1,5):
        Nn=oper(N,n)
        for x in range(Lng(Nn)):
            if not hasParent(Nn,1,x): continue
            p=parent(Nn,1,x)
            if x<j0:
                # prefix: parent should be parent in N at x (verbatim region)
                ok = hasParent(N,1,x) and parent(N,1,x)==p
                c_pref_ok+= 1 if ok else 0; c_pref_bad += 0 if ok else 1
                continue
            qx=(x-j0)//w; sx=(x-j0)%w
            if sx>0:
                # within block qx: x base = j0+sx. parent base?
                pbase = p - qx*w if p>=j0 else p
                # claim: parent corresponds to N's parent of (j0+sx)
                ok = hasParent(N,1,j0+sx) and (parent(N,1,j0+sx)+ (qx*w if parent(N,1,j0+sx)>=j0 else 0))==p
                c_within_ok+= 1 if ok else 0; c_within_bad += 0 if ok else 1
            else:
                # block start x=j0+qx*w, parent in prefix p<j0
                # claim: x's row1 value = entry N 1 j0; p = parent N 1 j0; reduces to RedCondA N edge (1,j0)
                ok = (p<j0) and hasParent(N,1,j0) and parent(N,1,j0)==p
                c_bd_ok+= 1 if ok else 0; c_bd_bad += 0 if ok else 1
print("prefix ok/bad",c_pref_ok,c_pref_bad)
print("within ok/bad",c_within_ok,c_within_bad)
print("boundary(blockstart) ok/bad",c_bd_ok,c_bd_bad)
