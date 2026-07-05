import sys, itertools
sys.path.insert(0,'python')
import red_model as R
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
n3=n3hp=n4=n4hp=0;fails=[];e10lt=0;e10ge=0
V=5;cols=[(a,b) for a in range(V+1) for b in range(a+1)]
cnt=0
for bl in range(2,5):
    base=R.diagSeq(0,bl-1)
    for t in range(1,4):
        for tl in itertools.product(cols,repeat=t):
            M=base+list(tl)
            if R.Lng(M)>8:continue
            j1=R.Lng(M)-1
            if not(1<j1):continue
            if R.Red(M)!=M:continue
            if not R.monoT(M):continue
            C3,C4=cond34(M)
            if not(C3 or C4):continue
            try:
                if not R.is_standard(M):continue
            except:continue
            cnt+=1
            hp=R.hasParent(M,1,j1)
            if C3:n3+=1;n3hp+=hp
            if C4:n4+=1;n4hp+=hp
            if R.entry(M,1,0)<R.entry(M,1,j1):e10lt+=1
            else:e10ge+=1
            if not hp and len(fails)<20:
                fails.append((R.fmt(M),"c3" if C3 else "c4","e10",R.entry(M,1,0),"e1j1",R.entry(M,1,j1)))
print("standard condIII/IV hosts:",cnt,flush=True)
print("condIII: n=",n3,"hasParent1=",n3hp,"  condIV: n=",n4,"hasParent1=",n4hp,flush=True)
print("e10<e1j1 (k=0 witness OK):",e10lt,"  e10>=e1j1 (k=0 fails):",e10ge,flush=True)
print("FAILS (cond but NOT hasParent1):",len(fails),flush=True)
for e in fails:print("  ",e,flush=True)
