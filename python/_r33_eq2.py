import sys
sys.path.insert(0,'python')
import red_model as R
def condIII(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    j0=R.parent(M,0,j1)
    if j0 is None: return False
    return R.entry(M,1,j0)>=R.entry(M,1,j1) and R.adm(M,j0)
def condIV(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    j0=R.parent(M,0,j1)
    if j0 is None: return False
    return R.entry(M,1,j0)>=R.entry(M,1,j1) and (not R.adm(M,j0))
def analyze(RN,d):
    b=R.Br(RN)
    if len(b)==0: return None
    last=len(b)-1; jl=R.Joints(RN)[last]; fn=R.FirstNodes(RN)[last]
    if d!=jl: return None
    diag=(R.entry(RN,0,fn)==R.entry(RN,1,fn))
    singleton=(fn==R.Lng(RN)-1)
    return dict(RN=R.fmt(RN),d=d,jl=jl,fn=fn,L=R.Lng(RN),diag=diag,single=singleton)
def orbit(cap,maxlen,nmax,seeds):
    seen=set(); fr=[]
    for s in seeds:
        t=tuple(s); seen.add(t); fr.append(s)
    out=[]
    while fr and len(out)<cap:
        M=fr.pop(0); out.append(M)
        if R.Lng(M)>=maxlen: continue
        for n in range(1,nmax+1):
            try: Mn=R.oper(M,n)
            except Exception: continue
            t=tuple(Mn)
            if t not in seen and R.Lng(Mn)<=maxlen:
                seen.add(t); fr.append(Mn)
    return out
seeds=[R.diagSeq(u,v) for u in range(0,5) for v in range(u,u+6)]
exRS=[]; exRP=[]
cnt=0
for M in orbit(20000,14,4,seeds):
    try:
        if not R.is_standard(M): continue
    except Exception: continue
    j1=R.Lng(M)-1
    if not(1<j1): continue
    if not R.hasParent(M,1,j1): continue
    if not(condIII(M) or condIV(M)): continue
    jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2); d=jm2-jm3
    if d<=0: continue
    cnt+=1
    try: RN=R.Red(R.seg(M,jm3,j1))
    except Exception: RN=None
    if RN is not None:
        a=analyze(RN,d)
        if a and len(exRS)<12: a['M']=R.fmt(M); exRS.append(a)
    if j1-1>jm3:
        try: RNp=R.Red(R.seg(M,jm3,j1-1))
        except Exception: RNp=None
        if RNp is not None:
            a=analyze(RNp,d)
            if a and len(exRP)<12: a['M']=R.fmt(M); exRP.append(a)
print("d>0 hosts:",cnt)
print("REGS eq examples:",len(exRS))
for e in exRS: print("  ",e)
print("REGS: all diag?",all(e['diag'] for e in exRS),"all single?",all(e['single'] for e in exRS) if exRS else None)
print("REGSP eq examples:",len(exRP))
for e in exRP: print("  ",e)
print("REGSP: all diag?",all(e['diag'] for e in exRP),"all single?",all(e['single'] for e in exRP) if exRP else None)
