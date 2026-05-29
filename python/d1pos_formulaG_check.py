import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, Br, is_standard, fmt, le0)
def gen_std(maxlen, maxval, KMAX):
    base=[[(j,j) for j in range(u,v+1)] for u in range(maxval+1) for v in range(u,maxval+1)]
    store={fmt(m):m for m in base}; fr=list(base)
    for _ in range(KMAX):
        nf=[]
        for M in fr:
            for n in range(1,4):
                Mp=oper(M,n); k=fmt(Mp)
                if Mp and len(Mp)<=maxlen and all(a<=maxval and b<=maxval for(a,b)in Mp) and k not in store:
                    store[k]=Mp; nf.append(Mp)
        fr=nf
    return [m for m in store.values() if is_standard(m)]
def isd1(N):
    j1=Lng(N)-1
    return j1>=1 and monoT(N) and not(entry(N,0,j1)==0 and entry(N,1,j1)==0) and idx1(N,j1)==1 and hasParent(N,1,j1)
def brle(Mp):
    t=TrMax(Mp); return t==Lng(Mp)-1 or le0(Mp,t+1,Lng(Mp)-1)
ml,mv,km=(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])) if len(sys.argv)>3 else (11,4,6)
Ns=[N for N in gen_std(ml,mv,km) if isd1(N)]
tot=lenok=treqok=boundok=le0ok=0; ex=[]
for N in Ns:
    LN=Lng(N); jm2=parent(N,1,LN-1); w=LN-1-jm2
    if w<=0: continue
    for n in (1,2,3):
        M=oper(N,n)
        if Lng(M)<2: continue
        for j0p in range(Lng(M)):
            for j1p in range(j0p+1,Lng(M)):
                if not le0(M,j0p,j1p): continue
                Mp=seg(M,j0p,j1p)
                if not monoT(Mp): continue
                if j1p<LN-1: continue
                if brle(Mp): continue
                # formula G
                j0red = jm2+((j0p-jm2)%w) if j0p>=jm2 else j0p
                j1red = min(j0red+(j1p-j0p), LN-1)
                tot+=1
                if j0red<j1red<=LN-1: boundok+=1
                if le0(N,j0red,j1red): le0ok+=1
                Np=seg(N,j0red,j1red)
                if TrMax(Mp)==TrMax(Np): treqok+=1
                if len(Br(Mp))==len(Br(Np)): lenok+=1
                elif len(ex)<5: ex.append((fmt(N),n,j0p,j1p,j0red,j1red,len(Br(Mp)),len(Br(Np))))
print(f"[len{ml}/val{mv}/KMAX{km}] ¬brle residual={tot}")
print(f"  bound j0red<j1red<=LngN-1: {boundok}/{tot}")
print(f"  le0 N j0red j1red:         {le0ok}/{tot}")
print(f"  TrEq:                      {treqok}/{tot}")
print(f"  length(Br M')=Lng(Br Np):  {lenok}/{tot}")
if ex: print("  length fails:",ex)
