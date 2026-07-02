import sys; sys.path.insert(0,'.')
from red_model import Lng,entry,monoT,reduced,Br,FirstNodes,Joints,TrMax,parent,Adm
import red_model as rm
from trans_model import Trans,Pred
from fast_pss import enum_reduced_tiling
def RN(t):
    xs=t[1]
    if not xs: return []
    l=xs[-1]; return [l[1]]+RN(l[2])
def transJm1(M):
    j1=Lng(M)-1; jp=parent(M,0,j1); return Adm(M,jp) if jp is not None else None
print("=== CASE B (Lng M = 3) full structure ===")
seen=[]
for M in enum_reduced_tiling(maxlen=5,maxe=4):
    M=[tuple(c) for c in M]
    if not reduced(M) or not monoT(M): continue
    if Lng(M)!=3: continue
    if Br(M)==[]: continue
    tj=transJm1(M)
    if tj is None or tj<=0: continue
    if Br(Pred(M))!=[] and (Lng(Pred(M))-1>1): continue  # ensure base
    J1=Lng(Br(M))-1
    fnJ1=FirstNodes(M)[J1]; jtJ1=Joints(M)[J1]
    rn1=RN(Trans(M))[1]
    seen.append((rm.fmt(M),TrMax(M),len(Br(M)),fnJ1,jtJ1,rn1,entry(M,1,1),entry(M,1,fnJ1),entry(M,1,jtJ1)))
print(f"{len(seen)} case-B sequences (maxe4)")
for s in seen:
    print("  M=%-22s TrMax=%d #Br=%d fnJ1=%d jtJ1=%d rn1=%d e1[1]=%d e1[fn]=%d e1[jt]=%d"%s)
