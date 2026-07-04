import sys, itertools, random
sys.path.insert(0,'python')
import red_model as R

def condIIIorIV(M):
    j1=R.Lng(M)-1
    if not R.hasParent(M,0,j1): return False
    j0=R.parent(M,0,j1)
    return R.entry(M,1,j1)>0 and R.entry(M,1,j0)>=R.entry(M,1,j1)

st={'host':0,'guard':0,'brne':0,'eqd':0,'strictlt_eqd_true':0,
    'deep_eqd':0,'deep_eqd_true':0}
cex=[]
def check(M):
    L=R.Lng(M); j1=L-1
    if not(1<j1): return
    if not R.hasParent(M,1,j1): return
    if not R.hasParent(M,0,j1): return
    if not condIIIorIV(M): return
    jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2)
    st['host']+=1
    if not (jm3<jm2): return
    st['guard']+=1
    d=jm2-jm3
    N=R.seg(M,jm3,j1)
    try: RNp=R.Red(R.Pred(N))
    except Exception: return
    br=R.Br(RNp)
    if len(br)==0: return
    st['brne']+=1
    last=len(br)-1
    fnp=R.FirstNodes(RNp)[last]; jlp=R.Joints(RNp)[last]
    if d!=jlp: return
    st['eqd']+=1
    if fnp>=R.Lng(RNp): return
    lt = R.entry(RNp,1,d) < R.entry(RNp,1,fnp)
    deep = L>=10
    if deep: st['deep_eqd']+=1
    if lt:
        st['strictlt_eqd_true']+=1
        if deep: st['deep_eqd_true']+=1
    else:
        if len(cex)<8: cex.append((R.fmt(M),'L',L,'d',d,'fnp',fnp,'e1d',R.entry(RNp,1,d),'e1fnp',R.entry(RNp,1,fnp),'RNp',R.fmt(RNp)))

V=5
cols=[(a,b) for a in range(0,V+1) for b in range(0,a+1)]
for bl in range(2,7):
    base=R.diagSeq(0,bl-1)
    for t in range(1,4):
        for tail in itertools.product(cols,repeat=t):
            M=base+list(tail)
            if R.Lng(M)>12: continue
            try:
                if R.is_standard(M): check(M)
            except Exception: pass
random.seed(3)
V2=9
cols2=[(a,b) for a in range(0,V2+1) for b in range(0,a+1)]
for _ in range(20000):
    bl=random.randint(2,8); base=R.diagSeq(0,bl-1)
    t=random.randint(1,8)
    M=base+[random.choice(cols2) for _ in range(t)]
    if R.Lng(M)<4: continue
    try:
        if R.is_standard(M): check(M)
    except Exception: pass
print(st)
for c in cex: print("CEX_strictlt_eqd_FALSE",c)
