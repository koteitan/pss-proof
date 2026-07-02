import sys, itertools; sys.path.insert(0,'.')
from red_model import Lng,entry,monoT,multiT,reduced,Br,FirstNodes,Joints,TrMax,parent,Adm,seg
import red_model as rm
def transJm1(M):
    j1=Lng(M)-1; jp=parent(M,0,j1); return Adm(M,jp) if jp is not None else None
bad=[]; nbr_vals=set(); n=0; segmulti=[]
V=7
for M in itertools.product([(a,b) for a in range(V) for b in range(V)],repeat=3):
    M=list(M)
    if not reduced(M) or not monoT(M) or Br(M)==[]: continue
    tj=transJm1(M)
    if tj is None or tj<=0: continue
    n+=1
    nbr_vals.add(len(Br(M)))
    if len(Br(M))!=1: bad.append((rm.fmt(M),TrMax(M),len(Br(M))))
    if TrMax(M)==0 and multiT(seg(M,1,2)): segmulti.append(rm.fmt(M))
with open('/tmp/claude-1000/-home-koteitan-proofs-pss-proof/9d301724-46c5-41cd-9d23-cd6fa387e7db/scratchpad/cb2.txt','w') as f:
    f.write(f"length-3 base-B-eligible: {n}, #Br values seen: {sorted(nbr_vals)}\n")
    f.write(f"#Br!=1 cases: {bad[:20]}\n")
    f.write(f"seg M 1 2 multi (TrMax=0): {len(segmulti)} {segmulti[:10]}\n")
print("done")
