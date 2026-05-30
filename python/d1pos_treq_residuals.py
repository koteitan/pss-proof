import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import *

# Verify the PROOF-INTERNAL residuals of the planned d1pos TrEq proof:
#  With c = j1red - 1 - j0red,  N'' = (IncrFirst^^shamt)(seg N j0red j1red):
#   (R0) agreement: Mp ! s == N'' ! s  for all s <= c                (sanity)
#   (R1) tnc : TrMax (seg N j0red j1red) <= c
#   (R2) boundary stop : not nextrel1 Mp (TrMax N'') (TrMax N'' + 1)
#         where TrMax N'' = TrMax(seg N j0red j1red)
#  Also re-verify the main TrEq on the same (smaller) pool.

_cache={}
def std(M):
    t=tuple(map(tuple,M))
    if t in _cache: return _cache[t]
    r=is_standard(M); _cache[t]=r; return r

def small_std(maxlen, maxval):
    res=[]
    for L in range(2,maxlen+1):
        for body in itertools.product(itertools.product(range(maxval+1),range(maxval+1)), repeat=L-1):
            M=[(0,0)]+list(body)
            if std(M): res.append(M)
    return res

def expand_pool(seedpool, maxlen, ns=(1,2,3), iters=4):
    pool=set(tuple(map(tuple,s)) for s in seedpool)
    frontier=[[tuple(x) for x in s] for s in seedpool]
    for _ in range(iters):
        newf=[]
        for s in frontier:
            for n in ns:
                M=oper(s,n)
                if Lng(M)>maxlen: continue
                t=tuple(map(tuple,M))
                if t in pool: continue
                if std(M): pool.add(t); newf.append([tuple(x) for x in M])
        frontier=newf
    return [list(map(tuple,p)) for p in pool]

def run(Npool, ns=(1,2,3)):
    treq=[0,0]; r1=[0,0]; r2=[0,0]; r0=[0,0]; ncap=0; ntot=0
    failed=[]
    for N in Npool:
        N=[tuple(x) for x in N]
        if Lng(N)<2 or not monoT(N): continue
        j1N=Lng(N)-1
        if idx1(N,j1N)!=1 or not hasParent(N,1,j1N): continue
        if entry(N,0,j1N)==0 and entry(N,1,j1N)==0: continue
        jm2=parent(N,1,j1N)
        if jm2 is None or jm2>=j1N: continue
        w=j1N-jm2; delta=entry(N,0,j1N)-entry(N,0,jm2)
        for n in ns:
            M=oper(N,n)
            if Lng(M)<2 or not std(M): continue
            LM=Lng(M)
            for j0p in range(LM):
                for j1p in range(j0p+1,LM):
                    Mp=seg(M,j0p,j1p)
                    if Lng(Mp)<2 or not monoT(Mp): continue
                    if not le0(M,j0p,j1p): continue
                    if not (j1N<=j1p): continue
                    # KEYSTONE is invoked only in the NOTBRLE context:
                    brle = (TrMax(Mp)==Lng(Mp)-1) or le0(Mp,TrMax(Mp)+1,Lng(Mp)-1)
                    if brle: continue
                    if jm2<=j0p:
                        q=(j0p-jm2)//w; j0red=jm2+((j0p-jm2)%w)
                    else:
                        q=0; j0red=j0p
                    j1red=min(j0red+(j1p-j0p), j1N)
                    if not (j0red<j1red) or j1red>j1N: continue
                    shamt=q*delta
                    Nred=seg(N,j0red,j1red)
                    Npp=funpow(IncrFirst,shamt,Nred)
                    c=j1red-1-j0red
                    ntot+=1
                    if j0red+(j1p-j0p)>j1N: ncap+=1
                    # R0 agreement
                    ok0=all(Mp[s]==Npp[s] for s in range(0,c+1) if s<Lng(Mp) and s<Lng(Npp))
                    r0[1]+=1; r0[0]+= (1 if ok0 else 0)
                    tN=TrMax(Nred)
                    # R1 tnc
                    r1[1]+=1; r1[0]+= (1 if tN<=c else 0)
                    # R2 boundary stop
                    stop = not nextrel1(Mp,tN,tN+1)
                    r2[1]+=1; r2[0]+= (1 if stop else 0)
                    # main TrEq
                    treq[1]+=1
                    if TrMax(Mp)==tN: treq[0]+=1
                    else:
                        if len(failed)<5: failed.append((N,n,j0p,j1p,j0red,j1red,q,TrMax(Mp),tN))
    print(f"  cases={ntot} capped={ncap}", flush=True)
    print(f"  TrEq      {treq[0]}/{treq[1]}", flush=True)
    print(f"  R0 agree  {r0[0]}/{r0[1]}", flush=True)
    print(f"  R1 tnc    {r1[0]}/{r1[1]}  (TrMax Nred <= j1red-1-j0red)", flush=True)
    print(f"  R2 stop   {r2[0]}/{r2[1]}  (not nextrel1 Mp tN tN+1)", flush=True)
    for ex in failed: print("   TrEq FAIL", ex, flush=True)

if __name__=="__main__":
    small=small_std(5,3)
    print("small std", len(small), flush=True)
    big=expand_pool(small, 11, ns=(1,2,3), iters=4)
    print("pool", len(big), "maxlen", max((len(p) for p in big),default=0), flush=True)
    run(big, ns=(1,2,3))
