import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, is_standard, fmt, le0, nextrel1)

# Verify the KEY reachability that turns notbrle into TrMax Mp+1<=c:
#   TAIL: for all k with c+1 <= k <= Lng Mp - 1 :  le0 Mp k (Lng Mp -1)
#         (c = j1red-1-j0red).  Then notbrle's not-le0(Mp,TrMax+1,end) + Mlt(TrMax+1<=end)
#         forces TrMax Mp + 1 <= c.
# Split by capped/uncapped.  Also report whether the WEAKER 'le0 Mp (c+1) end' suffices.

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

ml,mv,km=(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])) if len(sys.argv)>3 else (12,5,7)
Ns=[N for N in gen_std(ml,mv,km) if isd1(N)]
tail_all=[0,0]; tail_c1=[0,0]; concl=[0,0]; capc=0; tot=0
ex=[]
for N in Ns:
    LN=Lng(N); j0=parent(N,1,LN-1); w=LN-1-j0
    if w<=0: continue
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
                LMp=Lng(Mp); end=LMp-1
                tot+=1
                iscap=(j0red+(j1p-j0p)>LN-1)
                if iscap: capc+=1
                # TAIL all
                ta=all(le0(Mp,k,end) for k in range(c+1,end+1))
                tail_all[1]+=1; tail_all[0]+=(1 if ta else 0)
                if not ta and len(ex)<6: ex.append(("tailall",fmt(N),n,j0p,j1p,c,end,iscap))
                # weaker: le0 Mp (c+1) end
                if c+1<=end:
                    tc=le0(Mp,c+1,end)
                    tail_c1[1]+=1; tail_c1[0]+=(1 if tc else 0)
                # conclusion check: TrMax+1<=c
                t=TrMax(Mp)
                concl[1]+=1; concl[0]+=(1 if t+1<=c else 0)
print(f"d1pos std N={len(Ns)} (len<={ml} val<={mv} KMAX={km}) cases={tot} capped={capc}", flush=True)
print(f"  TAIL-all  (all k in [c+1,end]: le0 Mp k end): {tail_all[0]}/{tail_all[1]}", flush=True)
print(f"  TAIL-c1   (le0 Mp (c+1) end):                 {tail_c1[0]}/{tail_c1[1]}", flush=True)
print(f"  concl     (TrMax Mp + 1 <= c):                {concl[0]}/{concl[1]}", flush=True)
for e in ex: print("  EX",e, flush=True)
