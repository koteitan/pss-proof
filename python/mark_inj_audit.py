"""A19 / Mark-preserves-order empirical check: Mark is injective on marked
columns (incl. m0=0), and the right-spine length g(m)=|RightNodes(Trans(seg M 0 m))|
is >=2 for marked m>=1 (with 0 marked) -- so the m0=0 distinctness reduces to a
non-leaf fact that is, however, specific to the marked-prefix structure."""
from trans_model import adm, Mark, Trans
from red_model import Lng, le0, seg
from fast_pss import enum_reduced_tiling
def marked(M,m): return adm(M,m) and le0(M,m,Lng(M)-1)
def RightNodes(t):
    xs=t[1]
    if not xs: return []
    u=xs[-1]
    return [u[1]]+RightNodes(u[2])
if __name__=='__main__':
    viol=0; pairs=0; gmin=99
    for M in enum_reduced_tiling(maxlen=5,maxe=3):
        n=Lng(M)
        if n<2: continue
        cols=[m for m in range(n) if marked(M,m)]
        mk={m:Mark(M,m) for m in cols}
        for i in range(len(cols)):
            for j in range(i+1,len(cols)):
                pairs+=1
                if mk[cols[i]]==mk[cols[j]]: viol+=1
        if marked(M,0):
            for m1 in cols:
                if m1>=1: gmin=min(gmin,len(RightNodes(Trans(seg(M,0,m1)))))
    print(f"marked pairs={pairs}, Mark-equal violations={viol}, min g(m1>=1)={gmin}")
