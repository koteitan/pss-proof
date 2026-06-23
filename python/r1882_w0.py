import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng, entry, monoT, TrMax, Br, parent, FirstNodes, Joints, diagSeq, seg, Red)
from trans_model import (Trans, Pred, reduced, adm, Adm, ZB, Dpt, addBT, PB, bpHeadV, bpHeadT)
# M = diagSeq 0 v @ [(v+1, 0)]  for v=1,2,3
for v in [1,2,3]:
    M = diagSeq(0,v) + [(v+1, 0)]
    print(f"v={v}  M={M}")
    print(f"   reduced={reduced(M)} monoT={monoT(M)} Br={Br(M)} TrMax={TrMax(M)} Lng-1={Lng(M)-1}")
    j1=Lng(M)-1
    print(f"   Trans(Pred M)={Trans(Pred(M))}")
    print(f"   Trans(M)     ={Trans(M)}")
    J1=Lng(Br(M))-1
    print(f"   j1p={FirstNodes(M)[J1]}  j0p={Joints(M)[J1]}  e10={entry(M,1,0)} e1j1p={entry(M,1,FirstNodes(M)[J1])} e1j0p={entry(M,1,Joints(M)[J1])}")
    print(f"   transJ0={parent(M,0,j1)} transJm1={Adm(M,parent(M,0,j1))}")
