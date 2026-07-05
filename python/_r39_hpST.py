import sys, itertools
sys.path.insert(0,'python')
import red_model as R
from collections import deque
_o=R.Red;_c={}
def Rm(M,d=0):
    k=tuple(map(tuple,M))
    if k in _c:return _c[k]
    v=_o(M,d);_c[k]=v;return v
R.Red=Rm
def cond34(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0:return (False,False)
    if not R.hasParent(M,0,j1):return (False,False)
    j0=R.parent(M,0,j1)
    if R.entry(M,1,j0)<R.entry(M,1,j1):return (False,False)
    a=R.adm(M,j0);return (a,not a)
# TRUE ST_PS: seeds = diagSeq u v (u<=v), then oper-orbit closure (ST_PS.oper)
seeds=[]
for u in range(0,4):
    for v in range(u,u+5):
        M=R.diagSeq(u,v)
        if R.Lng(M)>=2: seeds.append(tuple(M))
seeds=list(dict.fromkeys(seeds))
n3=n3hp=n4=n4hp=0; fails=[]; e10lt=0; e10ge=0
vis=set(); q=deque(seeds); MAXLEN=15
while q and len(vis)<200000:
    M=list(q.popleft()); k=tuple(M)
    if k in vis: continue
    vis.add(k)
    j1=R.Lng(M)-1
    if 2<=R.Lng(M)<=MAXLEN and 1<j1:
        # M in ST_PS by construction; regime for exchIII also needs PT_PS (monoT) & reduced?
        # The dispatcher applies exchIII with N in ST_PS AND N in PT_PS. So filter monoT.
        if R.monoT(M):
            C3,C4=cond34(M)
            if C3 or C4:
                hp=R.hasParent(M,1,j1)
                if C3:n3+=1;n3hp+=hp
                if C4:n4+=1;n4hp+=hp
                if R.entry(M,1,0)<R.entry(M,1,j1):e10lt+=1
                else:e10ge+=1
                if not hp and len(fails)<25:
                    fails.append((R.fmt(M),"c3" if C3 else "c4","e00",R.entry(M,0,0),"e10",R.entry(M,1,0),"e1j1",R.entry(M,1,j1)))
    if R.Lng(M)>MAXLEN: continue
    for n in range(1,5):
        try: Mn=R.oper(M,n)
        except: continue
        if 1<R.Lng(Mn)<=MAXLEN and tuple(Mn) not in vis: q.append(tuple(Mn))
print("visited(ST_PS orbit):",len(vis),flush=True)
print("monoT condIII: n=",n3,"hasParent1=",n3hp,"  condIV: n=",n4,"hasParent1=",n4hp,flush=True)
print("e10<e1j1:",e10lt,"  e10>=e1j1:",e10ge,flush=True)
print("FAILS (cond & monoT but NOT hasParent1):",len(fails),flush=True)
for e in fails:print("  ",e,flush=True)
