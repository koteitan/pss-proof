import sys, itertools
sys.path.insert(0,'python')
import red_model as R
_origRed=R.Red; _rc={}
def Rm(M,depth=0):
    k=tuple(map(tuple,M))
    if k in _rc: return _rc[k]
    v=_origRed(M,depth); _rc[k]=v; return v
R.Red=Rm

def transCond34(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return (False,False)
    if not R.hasParent(M,0,j1): return (False,False)
    j0=R.parent(M,0,j1)
    if R.entry(M,1,j0) < R.entry(M,1,j1): return (False,False)
    a=R.adm(M,j0); return (a, not a)

def descending_brs(Q):
    n=len(Q)
    for J0 in range(n):
        for J1 in range(J0,n):
            if R.entry(Q[J0],0,0)<R.entry(Q[J1],0,0): return False
            if R.entry(Q[J0],0,0)==R.entry(Q[J1],0,0) and R.entry(Q[J0],1,0)<R.entry(Q[J1],1,0): return False
    return True

def cfbx_detail(m,N):
    b=R.Br(N)
    if len(b)==0: return ("Br=[]",)
    last=len(b)-1; jl=R.Joints(N)[last]; fn=R.FirstNodes(N)[last]
    diag=R.entry(N,0,fn)==R.entry(N,1,fn); desc=descending_brs(b)
    disj1 = m<jl
    disj2 = (m==jl and diag and desc)
    return ("nbr",len(b),"jl",jl,"fn",fn,"m",m,"disj1(m<jl)",disj1,"m==jl",m==jl,"diag",diag,"desc",desc,"OK",disj1 or disj2)

found=[]
V=4
cols=[(a,b) for a in range(0,V+1) for b in range(0,a+1)]
for bl in range(2,4):
    base=R.diagSeq(0,bl-1)
    for t in range(1,3):
        for tail in itertools.product(cols,repeat=t):
            M=base+list(tail)
            if R.Lng(M)>5: continue
            j1=R.Lng(M)-1
            if not(1<j1): continue
            if R.Red(M)!=M: continue
            if not R.monoT(M): continue
            if not R.hasParent(M,1,j1): continue
            c3,c4=transCond34(M)
            if not(c3 or c4): continue
            try:
                if not R.is_standard(M): continue
            except Exception: continue
            jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2)
            if j1-1<jm3: continue
            RNp=R.Red(R.seg(M,jm3,j1-1))
            d=jm2-jm3; g=jm3<jm2; bne=len(R.Br(RNp))>0
            if bne and not g:  # B2 case: !guard & Br!=[]
                found.append((R.fmt(M),"c3" if c3 else "c4","jm2",jm2,"jm3",jm3,"d",d,
                              "RNp",R.fmt(RNp))+cfbx_detail(d,RNp))
print("B2 (!guard & Br!=[]) cases:",len(found))
for e in found: print("  ",e)
