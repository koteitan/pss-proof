import sys, itertools, random
sys.path.insert(0,'python')
import red_model as R
def cond34(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    j0=R.parent(M,0,j1)
    if j0 is None: return False
    return R.entry(M,1,j0)>=R.entry(M,1,j1)
st={'eq':0,'RN_orig00':0,'RN_orig10':0,'fnRN_lt_T':0,'LngBr_eq':0,
    'lastbranch_monoT':0,'fnp_eq_fnRN':0,'jlp_eq_jl':0,'le0_M_gp_j1':0,
    'diag_holds':0,'RNp_butlast_RN':0}
cex=[]
def check(M):
    j1=R.Lng(M)-1
    if not(1<j1): return
    if not R.hasParent(M,1,j1): return
    if not cond34(M): return
    jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2); d=jm2-jm3
    if d<=0 or j1-1<=jm3: return
    try:
        RN=R.Red(R.seg(M,jm3,j1)); RNp=R.Red(R.seg(M,jm3,j1-1))
    except Exception: return
    bp=R.Br(RNp)
    if len(bp)==0: return
    lastp=len(bp)-1; jlp=R.Joints(RNp)[lastp]; fnp=R.FirstNodes(RNp)[lastp]
    if d!=jlp: return
    st['eq']+=1
    T=R.Lng(RN)-1; Tp=R.Lng(RNp)-1
    b=R.Br(RN); last=len(b)-1
    fnRN=R.FirstNodes(RN)[last]; jl=R.Joints(RN)[last]
    ok=True
    if R.entry(RN,0,0)==0: st['RN_orig00']+=1
    else: ok=False
    if R.entry(RN,1,0)==0: st['RN_orig10']+=1
    else: ok=False
    if fnRN<T: st['fnRN_lt_T']+=1
    else: ok=False
    if len(b)==len(bp): st['LngBr_eq']+=1
    lastcomp=b[last]
    if len(lastcomp)>=2 and R.monoT(lastcomp): st['lastbranch_monoT']+=1
    if fnp==fnRN: st['fnp_eq_fnRN']+=1
    if jlp==jl: st['jlp_eq_jl']+=1
    if R.le0(M,jm3+fnp,j1): st['le0_M_gp_j1']+=1
    if RNp==RN[:-1]: st['RNp_butlast_RN']+=1
    # diag conclusion
    if R.entry(RNp,0,fnp)==R.entry(RNp,1,fnp): st['diag_holds']+=1
    if not ok and len(cex)<6:
        cex.append((R.fmt(M),R.fmt(RN),R.fmt(RNp),d,fnRN,T,jl,jlp,'e0RN0',R.entry(RN,0,0),'e1RN0',R.entry(RN,1,0)))
# brute straddle
V=5
cols=[(a,b) for a in range(0,V+1) for b in range(0,a+1)]
for base_len in range(2,6):
    base=R.diagSeq(0,base_len-1)
    for t in range(1,4):
        for tail in itertools.product(cols,repeat=t):
            M=base+list(tail)
            if R.Lng(M)>10: continue
            try:
                if R.is_standard(M): check(M)
            except Exception: pass
# random deep
random.seed(7)
V2=8
cols2=[(a,b) for a in range(0,V2+1) for b in range(0,a+1)]
for _ in range(5000):
    bl=random.randint(2,6); base=R.diagSeq(0,bl-1)
    t=random.randint(1,6)
    M=base+[random.choice(cols2) for _ in range(t)]
    if R.Lng(M)<3: continue
    try:
        if R.is_standard(M): check(M)
    except Exception: pass
print(st)
for c in cex: print("CEX",c)
