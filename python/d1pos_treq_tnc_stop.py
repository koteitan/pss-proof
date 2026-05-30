import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, is_standard, fmt, le0, nextrel1, IncrFirst, funpow)

# DEEP verify the two sub-facts the notbrle-UNCONDITIONAL d1pos TrEq needs,
# with the EXACT in-context hyps (N std monoT d1pos i1=1, M=oper(N,n),
# Mp=seg M j0' j1' monoT, le0 M j0' j1', bge Lng N-1<=j1', notbrle):
#   Mlt   : TrMax Mp < Lng Mp - 1                       (from notbrle, M-side)
#   tnc   : TrMax Nred <= j1red-1-j0red (=Lng Nred-2)   (N-side confinement)
#   stop  : not nextrel1 Mp (TrMax Nred) (TrMax Nred+1) (boundary stop)
# split by capped (j0red+(j1'-j0')>Lng N-1) vs uncapped.
# Also: M-side trunk-confinement -> tnc transfer sanity:
#   tncM : TrMax Mp <= c   (with c=j1red-1-j0red)  [the M-side analogue]

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
print(f"d1pos std N = {len(Ns)} (len<={ml} val<={mv} KMAX={km})", flush=True)
tot=0; cap=0
Mlt=[0,0]; tnc=[0,0]; stop=[0,0]; tncM=[0,0]; treq=[0,0]; agree=[0,0]
fails=[]
for N in Ns:
    LN=Lng(N); jm2=parent(N,1,LN-1); w=LN-1-jm2
    if w<=0: continue
    delta=entry(N,0,LN-1)-entry(N,0,jm2)
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
                # formula G
                if jm2<=j0p:
                    q=(j0p-jm2)//w; j0red=jm2+((j0p-jm2)%w)
                else:
                    q=0; j0red=j0p
                j1red=min(j0red+(j1p-j0p), LN-1)
                if not(j0red<j1red) or j1red>LN-1: continue
                shamt=q*delta
                Nred=seg(N,j0red,j1red)
                c=j1red-1-j0red
                tN=TrMax(Nred); tM=TrMax(Mp)
                Npp=funpow(IncrFirst,shamt,Nred)
                iscap = (j0red+(j1p-j0p)>LN-1)
                tot+=1
                if iscap: cap+=1
                # Mlt
                Mlt[1]+=1; Mlt[0]+= (1 if tM<Lng(Mp)-1 else 0)
                # tnc
                tnc[1]+=1; tnc[0]+= (1 if tN<=c else 0)
                # tncM  (M-side confinement to c)
                tncM[1]+=1; tncM[0]+= (1 if tM<=c else 0)
                # stop
                s = not nextrel1(Mp,tN,tN+1)
                stop[1]+=1; stop[0]+= (1 if s else 0)
                # agreement on [0,c]
                ok=all(Mp[ss]==Npp[ss] for ss in range(0,c+1) if ss<Lng(Mp) and ss<Lng(Npp))
                agree[1]+=1; agree[0]+= (1 if ok else 0)
                # treq
                treq[1]+=1
                if tM==tN: treq[0]+=1
                else:
                    if len(fails)<6: fails.append(("TrEq",fmt(N),n,j0p,j1p,j0red,j1red,q,tM,tN,iscap))
print(f"cases={tot} capped={cap} uncapped={tot-cap}", flush=True)
print(f"  Mlt   {Mlt[0]}/{Mlt[1]}   (TrMax Mp < Lng Mp-1, from notbrle)", flush=True)
print(f"  tnc   {tnc[0]}/{tnc[1]}   (TrMax Nred <= c)", flush=True)
print(f"  tncM  {tncM[0]}/{tncM[1]}   (TrMax Mp   <= c)", flush=True)
print(f"  stop  {stop[0]}/{stop[1]}   (not nextrel1 Mp tN tN+1)", flush=True)
print(f"  agree {agree[0]}/{agree[1]}   (Mp!s=Npp!s on [0,c])", flush=True)
print(f"  TrEq  {treq[0]}/{treq[1]}", flush=True)
for f in fails: print("   FAIL", f, flush=True)
