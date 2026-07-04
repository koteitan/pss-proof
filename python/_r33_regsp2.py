import sys, itertools
sys.path.insert(0,'python')
import red_model as R
def cond34(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    j0=R.parent(M,0,j1)
    if j0 is None: return False
    return R.entry(M,1,j0)>=R.entry(M,1,j1)
nEq=0; nle0g_j1=0; nle0g_Lm2=0; ex=[]
def check(M):
    global nEq,nle0g_j1,nle0g_Lm2
    j1=R.Lng(M)-1
    if not(1<j1): return
    if not R.hasParent(M,1,j1): return
    if not cond34(M): return
    jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2); d=jm2-jm3
    if d<=0 or j1-1<=jm3: return
    try: RNp=R.Red(R.seg(M,jm3,j1-1))
    except Exception: return
    b=R.Br(RNp)
    if len(b)==0: return
    last=len(b)-1; jl=R.Joints(RNp)[last]; fn=R.FirstNodes(RNp)[last]
    if d!=jl: return
    nEq+=1
    gp=jm3+fn   # M-node of RN' last-branch head
    Tp=R.Lng(RNp)-1; gT=jm3+Tp  # M-node of RN' terminal
    if R.le0(M,gp,j1): nle0g_j1+=1
    if R.le0(M,gp,jm3+Tp): nle0g_Lm2+=1
    # also: is RN' terminal's M-node = Lng M-2? and le0 M gp (Lng M-2)?
    if len(ex)<10:
        ex.append((R.fmt(M),d,fn,gp,gT, R.le0(M,gp,j1), R.entry(M,1,gp), R.entry(M,1,j1),
                   R.parent(M,1,gp)))
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
print("REGSP-eq",nEq,"le0 M g' j1:",nle0g_j1,"le0 M g' T'(M):",nle0g_Lm2)
print("(M,d,fn,g',gT', le0(g',j1), e1g', e1j1, parentM1 g'):")
for e in ex: print("  ",e)
