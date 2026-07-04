import sys, itertools
sys.path.insert(0,'python')
import red_model as R
def cond34(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    j0=R.parent(M,0,j1)
    if j0 is None: return False
    return R.entry(M,1,j0)>=R.entry(M,1,j1)
exRS=[];exRP=[];nRS=0;nRP=0
def check(M):
    global nRS,nRP
    j1=R.Lng(M)-1
    if not(1<j1): return
    if not R.hasParent(M,1,j1): return
    if not cond34(M): return
    jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2); d=jm2-jm3
    if d<=0: return
    try: RN=R.Red(R.seg(M,jm3,j1))
    except Exception: RN=None
    if RN is not None:
        b=R.Br(RN)
        if len(b)>0:
            last=len(b)-1; jl=R.Joints(RN)[last]; fn=R.FirstNodes(RN)[last]
            if d==jl:
                nRS+=1
                diag=(R.entry(RN,0,fn)==R.entry(RN,1,fn)); single=(fn==R.Lng(RN)-1)
                if len(exRS)<15: exRS.append((R.fmt(M),R.fmt(RN),d,fn,R.Lng(RN)-1,diag,single))
    if j1-1>jm3:
        try: RNp=R.Red(R.seg(M,jm3,j1-1))
        except Exception: RNp=None
        if RNp is not None:
            b=R.Br(RNp)
            if len(b)>0:
                last=len(b)-1; jl=R.Joints(RNp)[last]; fn=R.FirstNodes(RNp)[last]
                if d==jl:
                    nRP+=1
                    diag=(R.entry(RNp,0,fn)==R.entry(RNp,1,fn)); single=(fn==R.Lng(RNp)-1)
                    if len(exRP)<15: exRP.append((R.fmt(M),R.fmt(RNp),d,fn,R.Lng(RNp)-1,diag,single))
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
print("enumerated",cnt,"RS-eq",nRS,"RP-eq",nRP)
print("REGS eq (M,RN,d,fn,T,diag,single):")
for e in exRS: print("  ",e)
print("REGSP eq:")
for e in exRP: print("  ",e)
print("REGS: all single?", all(e[6] for e in exRS) if exRS else "n/a", "all diag?", all(e[5] for e in exRS) if exRS else "n/a")
print("REGSP: all single?", all(e[6] for e in exRP) if exRP else "n/a", "all diag?", all(e[5] for e in exRP) if exRP else "n/a")
