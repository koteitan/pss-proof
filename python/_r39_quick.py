import sys, itertools
sys.path.insert(0,'python')
import red_model as R

def transCond34(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return (False,False)
    if not R.hasParent(M,0,j1): return (False,False)
    j0=R.parent(M,0,j1)
    if R.entry(M,1,j0) < R.entry(M,1,j1): return (False,False)
    a=R.adm(M,j0)
    return (a, not a)   # (condIII, condIV)

def descending_brs(Q):
    n=len(Q)
    for J0 in range(n):
        for J1 in range(J0,n):
            if R.entry(Q[J0],0,0) < R.entry(Q[J1],0,0): return False
            if R.entry(Q[J0],0,0)==R.entry(Q[J1],0,0) and R.entry(Q[J0],1,0) < R.entry(Q[J1],1,0):
                return False
    return True

def cfbx_reg(m,N):
    if not R.reduced(N): return False
    if not R.monoT(N): return False
    b=R.Br(N)
    if len(b)==0: return False
    last=len(b)-1
    jl=R.Joints(N)[last]; fn=R.FirstNodes(N)[last]
    if m < jl: return True
    if m==jl and R.entry(N,0,fn)==R.entry(N,1,fn) and descending_brs(b): return True
    return False

regime=0; guardc=0; nguardc=0; brne=0
B2fail=[]; B4fail=[]
def check(M):
    global regime,guardc,nguardc,brne
    j1=R.Lng(M)-1
    if not(1<j1): return
    if not R.reduced(M): return
    if not R.monoT(M): return
    if not R.hasParent(M,1,j1): return
    c3,c4=transCond34(M)
    if not(c3 or c4): return
    jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2)
    if j1-1<jm3: return
    try: RNp=R.Red(R.seg(M,jm3,j1-1))
    except Exception: return
    d=jm2-jm3; g=jm3<jm2; bne=len(R.Br(RNp))>0
    regime+=1
    if g: guardc+=1
    else: nguardc+=1
    if bne: brne+=1
    cf=cfbx_reg(d,RNp)
    if bne and not g and len(B2fail)<20:
        std="?"
        try: std=R.is_standard(M)
        except Exception: pass
        B2fail.append((R.fmt(M),jm2,jm3,d,R.fmt(RNp),"std",std,"cfbx",cf))
    if bne and not cf and len(B4fail)<20:
        std="?"
        try: std=R.is_standard(M)
        except Exception: pass
        B4fail.append((R.fmt(M),jm2,jm3,d,R.fmt(RNp),"std",std,"guard",g,R.Joints(RNp)))

V=5
cols=[(a,b) for a in range(0,V+1) for b in range(0,a+1)]
cnt=0
for base_len in range(2,5):
    base=R.diagSeq(0,base_len-1)
    for t in range(1,4):
        for tail in itertools.product(cols,repeat=t):
            M=base+list(tail)
            if R.Lng(M)>8: continue
            check(M); cnt+=1
print("cands",cnt,"regime",regime,"guard",guardc,"!guard",nguardc,"Br!=[]",brne)
print("B2fail(Br!=[]&!guard):",len(B2fail))
for e in B2fail: print("  ",e)
print("B4fail(Br!=[]&!cfbx):",len(B4fail))
for e in B4fail: print("  ",e)
