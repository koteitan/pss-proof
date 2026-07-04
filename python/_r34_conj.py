import sys; sys.path.insert(0,'python')
import red_model as R
def condIV(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    j0=R.parent(M,0,j1)
    if j0 is None: return False
    return R.entry(M,1,j0)>=R.entry(M,1,j1) and (not R.adm(M,j0))
def orbit(cap,maxlen,width):
    seen=set();fr=[]
    for u in range(0,4):
        for v in range(u,u+4):
            d=tuple(R.diagSeq(u,v));seen.add(d);fr.append(list(d))
    out=[]
    while fr and len(out)<cap:
        M=fr.pop(0);out.append(M)
        if R.Lng(M)>=maxlen:continue
        for n in range(1,width):
            try:Mn=R.oper(M,n)
            except Exception:continue
            t=tuple(Mn)
            if t not in seen and R.Lng(Mn)<=maxlen:seen.add(t);fr.append(Mn)
    return out
st={'IV':0,'e1_lt':0,'le0':0,'both':0,'jm2_0':0}
for M in orbit(15000,14,4):
    try:
        if not R.is_standard(M):continue
    except Exception:continue
    j1=R.Lng(M)-1
    if not(1<j1 and R.hasParent(M,1,j1)):continue
    if not condIV(M):continue
    st['IV']+=1
    jm2=R.parent(M,1,j1)
    if jm2==0:
        st['jm2_0']+=1; continue
    a=jm2-1
    e1lt = R.entry(M,1,a) < R.entry(M,1,jm2)   # nextrel1 needs this
    le0 = R.le0(M,a,jm2)                        # nextrel1 needs this
    if e1lt: st['e1_lt']+=1
    if le0: st['le0']+=1
    if e1lt and le0: st['both']+=1
print("condIV(jm2>0):",st['IV']-st['jm2_0']," jm2==0:",st['jm2_0'])
print(" e1(jm2-1)<e1(jm2):",st['e1_lt']," le0(jm2-1,jm2):",st['le0']," BOTH(=>nadm possible):",st['both'])
