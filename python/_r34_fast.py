#!/usr/bin/env python3
import sys
sys.path.insert(0,'python')
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
n=0;exs=[]
for M in orbit(12000,13,4):
    try:
        if not R.is_standard(M):continue
    except Exception:continue
    j1=R.Lng(M)-1
    if not(1<j1 and R.hasParent(M,1,j1)):continue
    if condIV(M):
        n+=1
        j0=R.parent(M,0,j1);jm2=R.parent(M,1,j1)
        # nextR M 1 jm2 (jm2+1)?
        nx=R.nextR(M,1,jm2,jm2+1) if jm2+1<R.Lng(M) else None
        if len(exs)<8:
            exs.append((R.fmt(M),'j0=%d'%j0,'jm2=%d'%jm2,'admjm2=%s'%R.adm(M,jm2),
                        'nx1(jm2,jm2+1)=%s'%nx))
print("condIV hosts:",n,flush=True)
for e in exs:print(" ",e,flush=True)
