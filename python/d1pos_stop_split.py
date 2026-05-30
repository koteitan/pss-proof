import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, is_standard, fmt, le0, nextrel1, IncrFirst, funpow)

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
from collections import Counter
cnt=Counter()
# stop-transfer-easy verify: when tN+1<=c, stop holds via N-side stop; report counts
easy_ok=[0,0]
for N in Ns:
    LN=Lng(N); j0=parent(N,1,LN-1); w=LN-1-j0
    if w<=0: continue
    delta=entry(N,0,LN-1)-entry(N,0,j0)
    for n in (1,2,3):
        M=oper(N,n)
        if Lng(M)<2 or not is_standard(M): continue
        LM=Lng(M)
        for j0p in range(LM):
            for j1p in range(j0p+1,LM):
                if j1p<LN-1: continue
                if not le0(M,j0p,j1p): continue
                Mp=seg(M,j0p,j1p)
                if Lng(Mp)<2 or not monoT(Mp): continue
                if brle(Mp): continue
                if j0<=j0p: q=(j0p-j0)//w; j0red=j0+((j0p-j0)%w)
                else: q=0; j0red=j0p
                j1red=min(j0red+(j1p-j0p),LN-1)
                if not(j0red<j1red) or j1red>LN-1: continue
                c=j1red-1-j0red
                Nred=seg(N,j0red,j1red)
                tN=TrMax(Nred)
                iscap=(j0red+(j1p-j0p)>LN-1)
                key=("cap" if iscap else "unc", "tN<c" if tN<c else ("tN=c" if tN==c else "tN>c"))
                cnt[key]+=1
                # easy stop check: tN+1<=c -> stop should follow from N stop & agreement
                if tN+1<=c:
                    easy_ok[1]+=1
                    if not nextrel1(Mp,tN,tN+1): easy_ok[0]+=1
print(f"d1pos std N={len(Ns)}", flush=True)
for k in sorted(cnt): print(f"  {k}: {cnt[k]}", flush=True)
print(f"  easy(tN+1<=c) stop holds: {easy_ok[0]}/{easy_ok[1]}", flush=True)
