import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, is_standard, fmt, le0, nextrel1, IncrFirst, funpow, leR)

# DEEP verify the d1pos BOUNDARY-STOP ingredients (the irreducible brick), exact in-context hyps.
#  For the capped boundary case (j1red=LngN-1, TrMax Nred=c=j1red-1-j0red):
#   B1: stop index c+1 in Mp equals block (q+1) start in M  -> M!(j0'+c+1)=N!j0 shifted (q+1)delta
#       row-1:  entry Mp 1 (c+1) = entry N 1 j0  (j0=parent N 1 (LngN-1))
#   B2: entry Mp 1 c = entry N 1 (j1red-1) = entry N 1 (LngN-2)
#   B3: KEY inequality: entry N 1 j0 <= entry N 1 (j1red-1)   (row-1 drop at boundary)
#       (j0 is on the trunk of Nred: j0-j0red<=TrMax Nred; row-1 mono along trunk)
#   B4: j0red <= j0 ... actually j0red = j0+s0 >= j0; the trunk node we need is j1red-1 vs the
#       block-restart. Verify: entry N 1 j0 <= entry N 1 (LngN-2) AND j0 reachable.
# Also confirm: in capped boundary, leR N 1 (relation) j0red->(j1red-1) holds; and the
# overall stop holds.

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
print(f"d1pos std N={len(Ns)} (len<={ml} val<={mv} KMAX={km})", flush=True)
ncapbdry=0; B3=[0,0]; trunkj0=[0,0]; ord_e1=[0,0]
ex=[]
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
                # boundary case: tN==c AND capped
                if not (tN==c and iscap): continue
                ncapbdry+=1
                # j0 on trunk of Nred?  j0red<=j0<=j1red-1 ? Actually j0<=j0red here (j0red=j0+s0).
                # trunk node we compare: the block restart maps to N!j0; within Nred trunk the
                # last interior is index c = j1red-1-j0red i.e. N!(j1red-1)=N!(LN-2).
                # KEY: entry N 1 j0 <= entry N 1 (j1red-1)
                B3[1]+=1
                if entry(N,1,j0)<=entry(N,1,j1red-1): B3[0]+=1
                else:
                    if len(ex)<6: ex.append(("B3",fmt(N),n,j0p,j1p,j0,j0red,j1red,entry(N,1,j0),entry(N,1,j1red-1)))
                # is j0 row-1-reachable to j1red-1 in N? (mono)
                ord_e1[1]+=1
                if leR(N,1,j0,j1red-1): ord_e1[0]+=1
print(f"capped-boundary cases (tN=c & capped) = {ncapbdry}", flush=True)
print(f"  B3 (entry N 1 j0 <= entry N 1 (j1red-1)): {B3[0]}/{B3[1]}", flush=True)
print(f"  leR N 1 j0 (j1red-1):                     {ord_e1[0]}/{ord_e1[1]}", flush=True)
for e in ex: print("  EX",e, flush=True)
