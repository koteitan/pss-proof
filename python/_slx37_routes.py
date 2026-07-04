import sys, itertools, random
sys.path.insert(0,'python')
import red_model as R
def condIIIorIV(M):
    j1=R.Lng(M)-1
    if not R.hasParent(M,0,j1): return False
    j0=R.parent(M,0,j1)
    return R.entry(M,1,j1)>0 and R.entry(M,1,j0)>=R.entry(M,1,j1)
st={'n':0,
    # route A
    'fn_lt_T':0,'fnp_eq_fn':0,'jlp_eq_jl':0,'lngbr_eq':0,
    # route B
    'nextR_RNp_1_d_Tp':0,'le0_RNp_fnp_Tp':0,'nextR_M_1_jm2_Lm2':0,
    # goal
    'strict':0}
cexA=[]; cexB=[]
def check(M):
    L=R.Lng(M); j1=L-1
    if not(1<j1): return
    if not R.hasParent(M,1,j1): return
    if not R.hasParent(M,0,j1): return
    if not condIIIorIV(M): return
    jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2)
    if not(jm3<jm2): return
    d=jm2-jm3
    N=R.seg(M,jm3,j1)
    try: RN=R.Red(N); RNp=R.Red(R.Pred(N))
    except Exception: return
    brp=R.Br(RNp)
    if len(brp)==0: return
    lastp=len(brp)-1; jlp=R.Joints(RNp)[lastp]; fnp=R.FirstNodes(RNp)[lastp]
    if d!=jlp: return
    try:
        if not R.is_standard(M): return
    except Exception: return
    st['n']+=1
    Tp=R.Lng(RNp)-1
    # route A
    br=R.Br(RN)
    if len(br)>0:
        last=len(br)-1; fn=R.FirstNodes(RN)[last]; jl=R.Joints(RN)[last]; T=R.Lng(RN)-1
        if fn<T: st['fn_lt_T']+=1
        if fnp==fn: st['fnp_eq_fn']+=1
        else:
            if len(cexA)<6: cexA.append((R.fmt(M),'fnp',fnp,'fn',fn,'T',T,'RN',R.fmt(RN),'RNp',R.fmt(RNp)))
        if jlp==jl: st['jlp_eq_jl']+=1
        if len(br)==len(brp): st['lngbr_eq']+=1
    # route B
    if R.nextR(RNp,1,d,Tp): st['nextR_RNp_1_d_Tp']+=1
    else:
        if len(cexB)<6: cexB.append((R.fmt(M),'d',d,'Tp',Tp,'RNp',R.fmt(RNp),'e1d',R.entry(RNp,1,d),'e1Tp',R.entry(RNp,1,Tp),'par1Tp',R.parent(RNp,1,Tp)))
    if R.le0(RNp,fnp,Tp): st['le0_RNp_fnp_Tp']+=1
    if R.nextR(M,1,jm2,L-2): st['nextR_M_1_jm2_Lm2']+=1
    if R.entry(RNp,1,d)<R.entry(RNp,1,fnp): st['strict']+=1
V=5
cols=[(a,b) for a in range(0,V+1) for b in range(0,a+1)]
for base_len in range(2,6):
    base=R.diagSeq(0,base_len-1)
    for t in range(1,4):
        for tail in itertools.product(cols,repeat=t):
            M=base+list(tail)
            if R.Lng(M)>11: continue
            try: check(M)
            except Exception: pass
random.seed(21)
V2=9
cols2=[(a,b) for a in range(0,V2+1) for b in range(0,a+1)]
for _ in range(80000):
    bl=random.randint(2,8); base=R.diagSeq(0,bl-1)
    t=random.randint(1,8)
    M=base+[random.choice(cols2) for _ in range(t)]
    if R.Lng(M)<4 or R.Lng(M)>12: continue
    try: check(M)
    except Exception: pass
print("ROUTES",st)
for c in cexA: print("CEXA",c)
for c in cexB: print("CEXB",c)
