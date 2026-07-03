import sys; sys.path.insert(0,'.')
from red_model import Lng,entry,monoT,reduced,Br,diagSeq
import red_model as rm
from trans_model import Trans
from fast_pss import enum_reduced_tiling
def RN(t):
    xs=t[1]
    if not xs: return []
    l=xs[-1]; return [l[1]]+RN(l[2])
nondiag=[]; cnt=0; rnfail=[]
for M in enum_reduced_tiling(maxlen=5, maxe=3):
    M=[tuple(c) for c in M]
    if not reduced(M) or not monoT(M): continue
    if Br(M)!=[]: continue
    if Lng(M)<2: continue
    cnt+=1
    u=entry(M,1,0); v=entry(M,1,Lng(M)-1)
    if M!=diagSeq(u,v): nondiag.append((rm.fmt(M),u,v))
    rn=RN(Trans(M))
    if not (len(rn)>=2 and rn[1]==v): rnfail.append((rm.fmt(M),rn,v))
print("all-trunk reduced monoT:",cnt)
print("NON-diagSeq:",len(nondiag), nondiag[:20])
print("RN[1]!=v:",len(rnfail), rnfail[:20])
