import sys, itertools
sys.path.insert(0,'python')
import red_model as R
def condIIIorIV(M):
    j1=R.Lng(M)-1
    if not R.hasParent(M,0,j1): return False
    j0=R.parent(M,0,j1)
    return R.entry(M,1,j1)>0 and R.entry(M,1,j0)>=R.entry(M,1,j1)
def dump(M):
    L=R.Lng(M); j1=L-1
    jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2); d=jm2-jm3
    N=R.seg(M,jm3,j1); Np=R.Pred(N)
    RNp=R.Red(Np); RN=R.Red(N)
    br=R.Br(RNp); last=len(br)-1
    fnp=R.FirstNodes(RNp)[last]; jlp=R.Joints(RNp)[last]
    hp1=R.hasParent(RNp,1,fnp)
    p1=R.parent(RNp,1,fnp) if hp1 else None
    print("M=",R.fmt(M),"L",L,"jm2",jm2,"jm3",jm3,"d",d)
    print(" N=",R.fmt(N))
    print(" RNp=",R.fmt(RNp),"TrMax",R.TrMax(RNp),"Br=",[R.fmt(b) for b in br])
    print(" FN(RNp)=",R.FirstNodes(RNp),"J(RNp)=",R.Joints(RNp),"last",last,"fnp",fnp,"jlp",jlp)
    print(" e0d",R.entry(RNp,0,d),"e1d",R.entry(RNp,1,d),"e0fnp",R.entry(RNp,0,fnp),"e1fnp",R.entry(RNp,1,fnp),"hp1fnp",hp1,"p1",p1)
    if p1 is not None: print("   e1p1",R.entry(RNp,1,p1),"e0p1",R.entry(RNp,0,p1),"p1-jm3-region")
    print(" lastbranch=",R.fmt(br[last]),"len",len(br[last]))
    print("-"*50)
V=5
cols=[(a,b) for a in range(0,V+1) for b in range(0,a+1)]
found=0
for base_len in range(2,6):
    base=R.diagSeq(0,base_len-1)
    for t in range(1,4):
        for tail in itertools.product(cols,repeat=t):
            M=base+list(tail)
            if R.Lng(M)>10: continue
            try:
                if not R.is_standard(M): continue
            except Exception: continue
            L=R.Lng(M); j1=L-1
            if not(1<j1): continue
            if not R.hasParent(M,1,j1): continue
            if not R.hasParent(M,0,j1): continue
            if not condIIIorIV(M): continue
            jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2)
            if not(jm3<jm2): continue
            d=jm2-jm3; N=R.seg(M,jm3,j1)
            try: RNp=R.Red(R.Pred(N))
            except Exception: continue
            br=R.Br(RNp)
            if len(br)==0: continue
            last=len(br)-1; jlp=R.Joints(RNp)[last]
            if d!=jlp: continue
            dump(M); found+=1
            if found>=10: break
        if found>=10: break
    if found>=10: break
print("found",found)
