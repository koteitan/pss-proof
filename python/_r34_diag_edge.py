import sys, itertools
sys.path.insert(0,'python')
import red_model as R
def cond34(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    j0=R.parent(M,0,j1)
    if j0 is None: return False
    return R.entry(M,1,j0)>=R.entry(M,1,j1)
st={'eq':0,'nextR_M_1_jm2_Lm2':0,'parent_M_1_Lm2_eq_jm2':0,
    'e1_Lm2_eq_e1_jm2_p1':0,'le0_M_jm2_Lm2':0}
cex=[]
def check(M):
    j1=R.Lng(M)-1
    if not(1<j1): return
    if not R.hasParent(M,1,j1): return
    if not cond34(M): return
    jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2); d=jm2-jm3
    if d<=0 or j1-1<=jm3: return
    try:
        RNp=R.Red(R.seg(M,jm3,j1-1))
    except Exception: return
    bp=R.Br(RNp)
    if len(bp)==0: return
    lastp=len(bp)-1; jlp=R.Joints(RNp)[lastp]
    if d!=jlp: return
    st['eq']+=1
    Lm2=j1-1
    ok=True
    if R.nextR(M,1,jm2,Lm2): st['nextR_M_1_jm2_Lm2']+=1
    else: ok=False
    if R.hasParent(M,1,Lm2) and R.parent(M,1,Lm2)==jm2: st['parent_M_1_Lm2_eq_jm2']+=1
    if R.le0(M,jm2,Lm2): st['le0_M_jm2_Lm2']+=1
    if R.entry(M,1,Lm2)==R.entry(M,1,jm2)+1: st['e1_Lm2_eq_e1_jm2_p1']+=1
    if not ok and len(cex)<8:
        cex.append((R.fmt(M),jm2,jm3,Lm2,R.parent(M,1,Lm2),R.entry(M,1,jm2),R.entry(M,1,Lm2)))
V=5
cols=[(a,b) for a in range(0,V+1) for b in range(0,a+1)]
for base_len in range(2,6):
    base=R.diagSeq(0,base_len-1)
    for t in range(1,4):
        for tail in itertools.product(cols,repeat=t):
            M=base+list(tail)
            if R.Lng(M)>9: continue
            try:
                if R.is_standard(M): check(M)
            except Exception: pass
print(st)
for c in cex: print("CEX",c)
