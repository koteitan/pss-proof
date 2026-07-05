import sys, itertools
sys.path.insert(0,'python')
import red_model as R
_o=R.Red;_c={}
def Rm(M,d=0):
    k=tuple(map(tuple,M))
    if k in _c:return _c[k]
    v=_o(M,d);_c[k]=v;return v
R.Red=Rm
def c3(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0:return False
    if not R.hasParent(M,0,j1):return False
    j0=R.parent(M,0,j1)
    if R.entry(M,1,j0)<R.entry(M,1,j1):return False
    return R.adm(M,j0)
def c4(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0:return False
    if not R.hasParent(M,0,j1):return False
    j0=R.parent(M,0,j1)
    if R.entry(M,1,j0)<R.entry(M,1,j1):return False
    return not R.adm(M,j0)
from collections import deque
V=4;cols=[(a,b) for a in range(V+1) for b in range(a+1)]
seeds=[]
for bl in range(2,4):
    base=R.diagSeq(0,bl-1)
    for t in range(1,3):
        for tl in itertools.product(cols,repeat=t):
            M=base+list(tl)
            if R.Lng(M)>5:continue
            if R.Red(M)==M and R.monoT(M):
                try:
                    if R.is_standard(M):seeds.append(tuple(M))
                except:pass
seeds=list(dict.fromkeys(seeds))
n3=n3hp=n4=n4hp=0;fails=[];e10lt=0;e10ge=0
vis=set();q=deque(seeds)
while q and len(vis)<120000:
    M=list(q.popleft());k=tuple(M)
    if k in vis:continue
    vis.add(k)
    j1=R.Lng(M)-1
    if 2<=R.Lng(M)<=15 and 1<j1 and R.Red(M)==M and R.monoT(M):
        C3=c3(M);C4=c4(M)
        if C3 or C4:
            hp=R.hasParent(M,1,j1)
            if C3:n3+=1;n3hp+=hp
            if C4:n4+=1;n4hp+=hp
            if R.entry(M,1,0)<R.entry(M,1,j1):e10lt+=1
            else:e10ge+=1
            if not hp and len(fails)<15:
                fails.append((R.fmt(M),"c3" if C3 else "c4","e10",R.entry(M,1,0),"e1j1",R.entry(M,1,j1),"e00",R.entry(M,0,0)))
    if R.Lng(M)>15:continue
    for n in range(1,5):
        try:Mn=R.oper(M,n)
        except:continue
        if 1<R.Lng(Mn)<=15 and tuple(Mn) not in vis:q.append(tuple(Mn))
    if R.Lng(M)>1:
        Mp=R.Pred(M)
        if tuple(Mp) not in vis:q.append(tuple(Mp))
print("visited",len(vis))
print("condIII: n=",n3,"hasParent1=",n3hp,"  condIV: n=",n4,"hasParent1=",n4hp)
print("regime rows: e10<e1j1 (k=0 witness works):",e10lt,"  e10>=e1j1:",e10ge)
print("FAILS (transCondIII/IV but NOT hasParent1):",len(fails))
for e in fails:print("  ",e)
