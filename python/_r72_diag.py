import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4c/python')
from red_model import Lng, entry, monoT, seg, parent, hasParent, Adm
from trans_model import Trans, adm
import buchholz as bu
ZB=('T',[])
def D(v,t): return ('D',v,t)
def T(ps): return ('T',ps)
def bucOf(t): return [('D',p[1],bucOf(p[2])) for p in t[1]]
def lt(a,b): return bu.lt_term(bucOf(a),bucOf(b))
def show(t):
    if not t[1]: return "0"
    return "+".join(("D%d(%s)"%(p[1],show(p[2]))) for p in t[1])
def hole_depth(t,v1):
    d=0
    while True:
        ps=t[1]
        if not ps: return None
        last=ps[-1]
        if last[1]==v1 and last[2]==ZB: return d
        t=last[2]; d+=1
        if d>300: return None
def rsub(t,k):
    for _ in range(k):
        if not t[1]: return None
        t=t[1][-1][2]
    return t
def ht(t):
    if not t[1]: return 0
    return 1+max(ht(p[2]) for p in t[1])
def surger(t,q):
    ps=t[1]; last=ps[-1]
    if last[2]==ZB: return T(ps[:-1]+[q])
    return T(ps[:-1]+[D(last[1],surger(last[2],q))])

M=[(0,0),(1,1),(2,1),(3,1),(4,0),(5,1),(6,1),(7,0),(8,1),(9,0),(6,1),(7,0),(8,1),(9,0),(6,1),(6,1)]
j1=Lng(M)-1
p1=parent(M,1,j1); p0=parent(M,0,j1)
jm3=Adm(M,p1); jm1=Adm(M,p0)
N=seg(M,jm3,j1); TN=Trans(N); BODY=TN[1][0][2]
v1=entry(M,1,j1); ub=v1-1
dR=hole_depth(BODY,v1)
print("v1=",v1,"ub=",ub,"dR=",dR,"ht(BODY)=",ht(BODY))
print("BODY  =",show(BODY))
print("TransN=",show(TN))
for k in range(0,(dR or 0)+3):
    z=rsub(BODY,k)
    print("  rsub",k,"=",("None" if z is None else show(z)),"ht=",(None if z is None else ht(z)))
X0=T([D(ub,ZB)]); X1=surger(BODY,D(ub,X0))
print("X1    =",show(X1))
for k in range(1,(dR or 0)+2):
    z=rsub(BODY,k)
    if z is None: break
    print("  KK k=",k,": lessBT(rsub,X1) =",lt(z,X1))
