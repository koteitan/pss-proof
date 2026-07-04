import sys, itertools
sys.path.insert(0,'python')
import red_model as R
def cond34(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    j0=R.parent(M,0,j1)
    if j0 is None: return False
    return R.entry(M,1,j0)>=R.entry(M,1,j1)
# For RN' = Red(seg M jm3 (Lng M-2)): probe at equality whether
#  (a) d = parent RN' 1 fn'  (row-1 parent of last-branch first node)
#  (b) entry RN' 1 fn' == entry RN' 1 d + 1
#  (c) d < TrMax RN'  (trunk membership)
#  (d) le0 RN' d fn'  and  le0 RN' d T'
ex=[]; nEq=0; ntrunk_fail=0; nrow1par=0; nrow1val=0
def check(M):
    global nEq,ntrunk_fail,nrow1par,nrow1val
    j1=R.Lng(M)-1
    if not(1<j1): return
    if not R.hasParent(M,1,j1): return
    if not cond34(M): return
    jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2); d=jm2-jm3
    if d<=0: return
    if j1-1<=jm3: return
    try: RNp=R.Red(R.seg(M,jm3,j1-1))
    except Exception: return
    b=R.Br(RNp)
    if len(b)==0: return
    last=len(b)-1; jl=R.Joints(RNp)[last]; fn=R.FirstNodes(RNp)[last]
    tr=R.TrMax(RNp); Tp=R.Lng(RNp)-1
    if d>=tr: ntrunk_fail+=1
    if d==jl:
        nEq+=1
        # row-1 parent of fn in RNp
        p1=R.parent(RNp,1,fn)
        if p1==d: nrow1par+=1
        e1fn=R.entry(RNp,1,fn); e1d=R.entry(RNp,1,d)
        if e1fn==e1d+1: nrow1val+=1
        if len(ex)<12:
            ex.append((R.fmt(M),R.fmt(RNp),d,fn,Tp,p1, e1fn, e1d, R.entry(RNp,0,fn)))
V=5
cols=[(a,b) for a in range(0,V+1) for b in range(0,a+1)]
cnt=0
for base_len in range(2,6):
    base=R.diagSeq(0,base_len-1)
    for t in range(1,4):
        for tail in itertools.product(cols,repeat=t):
            M=base+list(tail)
            if R.Lng(M)>9: continue
            cnt+=1
            try:
                if R.is_standard(M): check(M)
            except Exception: pass
print("enum",cnt,"REGSP-eq",nEq,"trunk_fail(d>=TrMax')",ntrunk_fail)
print("at eq: row1par(d==parent RN' 1 fn)",nrow1par,"/",nEq,"  entry1 fn==entry1 d+1:",nrow1val,"/",nEq)
print("examples (M,RNp,d,fn,Tp,p1,e1fn,e1d,e0fn):")
for e in ex: print("  ",e)
