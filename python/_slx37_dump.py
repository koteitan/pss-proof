import sys, itertools, random
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
    print("M   =",R.fmt(M),"L",L,"jm2",jm2,"jm3",jm3,"d",d)
    print("N   =",R.fmt(N))
    print("Np  =",R.fmt(Np))
    print("RNp =",R.fmt(RNp),"Lng",R.Lng(RNp),"TrMax",R.TrMax(RNp))
    print("RN  =",R.fmt(RN),"Lng",R.Lng(RN),"TrMax",R.TrMax(RN))
    print("Br(RNp)=",[R.fmt(b) for b in br])
    print("FirstNodes(RNp)=",R.FirstNodes(RNp),"Joints(RNp)=",R.Joints(RNp))
    print("last",last,"fnp",fnp,"jlp",jlp,"d==jlp",d==jlp)
    print("entry RNp 0 d",R.entry(RNp,0,d),"entry RNp 1 d",R.entry(RNp,1,d))
    print("entry RNp 0 fnp",R.entry(RNp,0,fnp),"entry RNp 1 fnp",R.entry(RNp,1,fnp))
    # does fnp have a row1 parent in RNp?
    print("hasParent RNp 1 fnp",R.hasParent(RNp,1,fnp),"hasParent RNp 0 fnp",R.hasParent(RNp,0,fnp))
    if R.hasParent(RNp,1,fnp):
        p1=R.parent(RNp,1,fnp); print("   parent1(fnp)=",p1,"entry1 p1",R.entry(RNp,1,p1))
    # last branch of RNp
    print("last branch=",R.fmt(br[last]))
    print("="*60)

random.seed(11)
V2=9
cols2=[(a,b) for a in range(0,V2+1) for b in range(0,a+1)]
found=0
for _ in range(200000):
    bl=random.randint(2,8); base=R.diagSeq(0,bl-1)
    t=random.randint(1,8)
    M=base+[random.choice(cols2) for _ in range(t)]
    if R.Lng(M)<5 or R.Lng(M)>12: continue
    L=R.Lng(M); j1=L-1
    if not(1<j1): continue
    if not R.hasParent(M,1,j1): continue
    if not R.hasParent(M,0,j1): continue
    if not condIIIorIV(M): continue
    jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2)
    if not(jm3<jm2): continue
    d=jm2-jm3
    N=R.seg(M,jm3,j1)
    try: RNp=R.Red(R.Pred(N))
    except Exception: continue
    br=R.Br(RNp)
    if len(br)==0: continue
    last=len(br)-1
    jlp=R.Joints(RNp)[last]
    if d!=jlp: continue
    try:
        if not R.is_standard(M): continue
    except Exception: continue
    dump(M)
    found+=1
    if found>=6: break
print("found",found)
