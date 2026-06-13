import sys; sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from fast_pss import oper, Lng, parent1, hasParent1, entry, idx1, diagSeq, parent0
import collections
def tup(M): return [tuple(x) for x in M]
# For idx1=0 tiling N, M[n]: check parent(N[n]) 1 z readback:
#  z block k offset s (s>0): is base(parent(N[n])1 z) == parent N1(base z) AND same block k?
seen=set(); dq=collections.deque()
for a in range(0,3):
    for b in range(a,4):
        D=tup(diagSeq(a,b)); t=tuple(D)
        if t not in seen: seen.add(t); dq.append(D)
chk=0; bad_base=0; bad_blk=0; pre=0; reached=0
while dq and reached<3000:
    N=dq.popleft(); reached+=1
    j1=Lng(N)-1
    if j1<1: continue
    i1=idx1(N,j1)
    expand=[]
    for n in range(1,4):
        Nn=tup(oper(N,n)); t=tuple(Nn)
        if t not in seen and len(seen)<3000: seen.add(t); dq.append(Nn)
        expand.append((n,Nn))
    if not (not (entry(N,0,j1)==0 and entry(N,1,j1)==0)): continue
    if i1!=0: continue
    j0=parent0(N,j1)  # idx1=0 row-0 parent
    if not (j0<j1): continue
    w=j1-j0
    for n,Nn in expand:
        Ln=Lng(Nn)
        for z in range(j0,Ln):
            s=(z-j0)%w; k=(z-j0)//w
            if s==0: continue
            if not hasParent1(Nn,z): continue
            chk+=1
            p=parent1(Nn,z)
            bp = p if p<j0 else j0+((p-j0)%w)
            base=j0+s
            if not hasParent1(N,base): continue  # only when base has parent
            if bp != parent1(N,base): bad_base+=1
            if p>=j0 and (p-j0)//w != k: bad_blk+=1
            if p<j0: pre+=1
print("checked",chk,"base!=parentN(base)",bad_base,"parent not same block",bad_blk,"prefix-parent",pre)
