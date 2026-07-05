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
def cond4(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0:return False
    if not R.hasParent(M,0,j1):return False
    j0=R.parent(M,0,j1)
    if R.entry(M,1,j0)<R.entry(M,1,j1):return False
    return not R.adm(M,j0)
def transJm1(M): return R.Adm(M,R.parent(M,1,R.Lng(M)-1))  # jm1 = Adm(M, j0?) -- actually transJm1
# transJm1 M = Adm M (transJ1 M -1)? use defs: transJ0=parent M 0 (Lng-1); transJm1=Adm M transJ0
def transJ0(M): return R.parent(M,0,R.Lng(M)-1)
def s84x_jm2(M): return R.parent(M,1,R.Lng(M)-1)
n4=0; noguard_ok=0; admeq_ok=0; guard_and=[]; noguard_fail=[]
vis=set(); seeds=[tuple(R.diagSeq(u,v)) for u in range(4) for v in range(u,u+5) if v-u>=1]
q=deque(seeds); MAXLEN=15
while q and len(vis)<200000:
    M=list(q.popleft()); k=tuple(M)
    if k in vis: continue
    vis.add(k)
    j1=R.Lng(M)-1
    if 2<=R.Lng(M)<=MAXLEN and 1<j1 and R.monoT(M):
        if cond4(M) and R.hasParent(M,1,j1):
            jm2=s84x_jm2(M); jm3=R.Adm(M,jm2)
            guard = jm3<jm2
            n4+=1
            if not guard: noguard_ok+=1     # noguard = ¬guard holds
            else:
                if len(guard_and)<20: guard_and.append((R.fmt(M),"jm2",jm2,"jm3",jm3))
            # admeq: Adm M (jm2) = transJm1 M ;  transJm1 = Adm M transJ0
            jm1 = R.Adm(M, transJ0(M))
            if R.Adm(M,jm2)==jm1: admeq_ok+=1
    if R.Lng(M)>MAXLEN: continue
    for n in range(1,5):
        try: Mn=R.oper(M,n)
        except: continue
        if 1<R.Lng(Mn)<=MAXLEN and tuple(Mn) not in vis: q.append(tuple(Mn))
print("visited",len(vis),flush=True)
print("condIV monoT hasParent hosts:",n4,flush=True)
print("noguard (¬(jm3<jm2)) holds:",noguard_ok,"/",n4,"  (guard-holds cases:",n4-noguard_ok,")",flush=True)
print("admeq (Adm jm2 = transJm1) holds:",admeq_ok,"/",n4,flush=True)
if guard_and:
    print("--- condIV WITH guard (noguard FAILS): (M,jm2,jm3) ---",flush=True)
    for e in guard_and: print("  ",e,flush=True)
