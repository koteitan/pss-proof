import sys, itertools
sys.path.insert(0,'python')
import red_model as R
def cond34(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    j0=R.parent(M,0,j1)
    if j0 is None: return False
    return R.entry(M,1,j0)>=R.entry(M,1,j1)
st={'eq':0,'fnp_eq_fnRN':0,'BrRN_last_singleton':0,'BrRNp_last_singleton':0,
    'fnRN_eq_T':0,'lastRN_eq_lastRNp':0,'LngBrRN_eq_LngBrRNp':0,
    'le0_RN_fnRN_T_always':0,'d_eq_parentRN0_fnp':0,'parentRN1_T_eq_d':0}
ex=[]
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
    fnRN=R.FirstNodes(RN)[last]
    if fnp==fnRN: st['fnp_eq_fnRN']+=1
    if len(b[last])==1: st['BrRN_last_singleton']+=1  # branch is list of pairs
    if len(bp[lastp])==1: st['BrRNp_last_singleton']+=1
    if fnRN==T: st['fnRN_eq_T']+=1
    if last==lastp: st['lastRN_eq_lastRNp']+=1
    if len(b)==len(bp): st['LngBrRN_eq_LngBrRNp']+=1
    if R.le0(RN,fnRN,T): st['le0_RN_fnRN_T_always']+=1
    if R.parent(RN,0,fnp)==d: st['d_eq_parentRN0_fnp']+=1
    if R.parent(RN,1,T)==d: st['parentRN1_T_eq_d']+=1
    if len(ex)<8:
        ex.append((R.fmt(M),d,fnp,fnRN,T,Tp,len(b),len(bp),
                   'brRNlast_len='+str(len(b[last])),'brRNplast_len='+str(len(bp[lastp]))))
V=4
cols=[(a,b) for a in range(0,V+1) for b in range(0,a+1)]
for base_len in range(2,5):
    base=R.diagSeq(0,base_len-1)
    for t in range(1,4):
        for tail in itertools.product(cols,repeat=t):
            M=base+list(tail)
            if R.Lng(M)>9: continue
            try:
                if R.is_standard(M): check(M)
            except Exception: pass
print(st)
for e in ex: print(e)
