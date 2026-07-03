import sys
sys.setrecursionlimit(10000)
from red_model import diagSeq, oper, fmt

# Fast self-contained: entry, nextrel0/1 reach via memoized BFS.
def Lng(M): return len(M)
def entry(M,i,j): return M[j][i]
def nextrel0(M,j0,j1):
    if not (j0<j1): return False
    if entry(M,0,j0)>=entry(M,0,j1): return False
    # j0 is the max index < j1 with entry0 < entry0 j1 AND ... use article def
    # nextrel0: j0<j1, entry0 j0<entry0 j1, and for all j0<j<j1: entry0 j>=entry0 j1
    for j in range(j0+1,j1):
        if entry(M,0,j)<entry(M,0,j1): return False
    return True
def nextrel1(M,j0,j1):
    if not (j0<j1): return False
    if entry(M,1,j0)>=entry(M,1,j1): return False
    if not le0reach(M,j0,j1): return False
    for j in range(j0+1,j1):
        if le0reach(M,j,j1) and entry(M,1,j)<entry(M,1,j1): return False
    return True

_le0cache={}
def le0reach(M,a,b):
    key=(tuple(M),a,b)
    if key in _le0cache: return _le0cache[key]
    # reflexive-transitive closure of nextrel0 from a to b
    L=len(M)
    seen=[False]*L
    stack=[a]; seen[a]=True
    while stack:
        x=stack.pop()
        if x==b: _le0cache[key]=True; return True
        for y in range(x+1,L):
            if not seen[y] and nextrel0(M,x,y):
                seen[y]=True; stack.append(y)
    r=seen[b]
    _le0cache[key]=r
    return r

def hasParent1(M,j1):
    return sum(1 for j0 in range(j1) if nextrel1(M,j0,j1))==1
def parent1(M,j1):
    for j0 in range(j1):
        if nextrel1(M,j0,j1): return j0
    return None
def idx1(M,j1): return 1 if entry(M,1,j1)>0 else 0

def build_closure(depth_max=5, ubound=3, vbound=6, maxlen=16):
    bases=[tuple(diagSeq(u,v)) for u in range(ubound+1) for v in range(u,vbound+1)]
    seen=set(bases); allM=set(bases); frontier=list(bases)
    for d in range(depth_max):
        newf=[]
        for M in frontier:
            Ml=list(M)
            for n in range(1,4):
                Nn=oper(Ml,n)
                if 1<=len(Nn)<=maxlen:
                    t=tuple(Nn)
                    if t not in seen:
                        seen.add(t); allM.add(t); newf.append(t)
        frontier=newf
    return [list(M) for M in allM]

def Ez_check(N):
    L=Lng(N)
    if L<=1: return []
    j1=L-1
    if not hasParent1(N,j1): return []
    j0=parent1(N,j1)
    if j0 is None or not (j0<j1): return []
    res=[]
    for z in range(1,j1):
        if not hasParent1(N,z): continue
        pz=parent1(N,z)
        if pz is None: continue
        if not (pz>j0 and z>j0): continue
        lhs=entry(N,0,j1); rhs=entry(N,0,z)+(j1-z)
        res.append((z,lhs==rhs))
    return res

if __name__=="__main__":
    Ms=build_closure()
    print("closure",len(Ms),flush=True)
    tot=0; fail=0; ex=[]
    for N in Ms:
        for (z,ok) in Ez_check(N):
            tot+=1
            if not ok:
                fail+=1
                if len(ex)<6: ex.append((fmt(N),z))
    print("Ez applicable",tot,"fail",fail,flush=True)
    for e in ex: print("FAIL",e)
