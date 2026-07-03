from red_model import Lng, seg, leR, le0, monoT, zeroT, Red, entry
from trans_model import Trans, Mark, adm
from fast_pss import enum_reduced_tiling

def marked(M,m):
    n=Lng(M)
    return n>=1 and adm(M,m) and leR(M,0,m,n-1)

tot=0; viol=0; ex=[]
for M in enum_reduced_tiling(maxlen=6, maxe=3):
    n=Lng(M)
    if n<2: continue
    if not monoT(M): continue          # RT∩PT reduced monoT case
    j1=n-1
    for m in range(0, j1):              # j1-m>0
        if not marked(M,m): continue
        lhs=Mark(M,m)
        rhs=Trans(seg(M,m,j1))
        tot+=1
        if lhs!=rhs:
            viol+=1
            if len(ex)<6: ex.append((M,m,lhs,rhs))
print(f"monoT reduced: checked {tot}, violations {viol}")
for e in ex: print("  CEX", e)

# also the fact2 reduction: Mark M m == Mark(seg M m j1) 0
tot2=0; viol2=0; ex2=[]
for M in enum_reduced_tiling(maxlen=6, maxe=3):
    n=Lng(M)
    if n<2 or not monoT(M): continue
    j1=n-1
    for m in range(0,j1):
        if not marked(M,m): continue
        N=seg(M,m,j1)
        tot2+=1
        if Mark(M,m)!=Mark(N,0):
            viol2+=1
            if len(ex2)<6: ex2.append((M,m,Mark(M,m),Mark(N,0)))
print(f"fact2 (Mark M m == Mark(seg M m j1) 0): checked {tot2}, violations {viol2}")
for e in ex2: print("  CEX", e)
