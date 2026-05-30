import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import *

# Verify the d1pos TrEq KEYSTONE (see task spec):
#   N standard monoT d1pos, M=N[n], slice seg M j0' j1' monoT, le0 M j0' j1',
#   bge: Lng N-1 <= j1';  formula-G witnesses:
#     jm2=parent N 1 (Lng N-1), w=Lng N-1-jm2, delta=entry N 0 (Lng N-1)-entry N 0 jm2
#     q   = (j0'-jm2) div w           if jm2<=j0' else 0
#     j0red = jm2 + (j0'-jm2) mod w   if jm2<=j0' else j0'
#     j1red = min (j0red+(j1'-j0')) (Lng N-1)     (MIN-CAP essential)
#   CLAIM: TrMax (seg M j0' j1') = TrMax (seg N j0red j1red)

_cache={}
def std(M):
    t=tuple(map(tuple,M))
    if t in _cache: return _cache[t]
    r=is_standard(M); _cache[t]=r; return r

def small_std(maxlen, maxval):
    """Brute small standard seqs with cheap prechecks before subprocess."""
    res=[]
    vals=range(maxval+1)
    for L in range(2,maxlen+1):
        for body in itertools.product(itertools.product(vals,vals), repeat=L-1):
            M=[(0,0)]+list(body)
            # cheap necessary: row0[0]=row1[0]=0 already; weak structural prune
            if std(M): res.append(M)
    return res

def expand_pool(seedpool, maxlen, ns=(1,2,3), iters=4):
    pool=set(tuple(map(tuple,s)) for s in seedpool)
    frontier=[list(map(list,s)) for s in seedpool]
    frontier=[[tuple(x) for x in s] for s in frontier]
    for _ in range(iters):
        newf=[]
        for s in frontier:
            for n in ns:
                M=oper([tuple(x) for x in s],n)
                if Lng(M)>maxlen: continue
                t=tuple(map(tuple,M))
                if t in pool: continue
                if std(M):
                    pool.add(t); newf.append([tuple(x) for x in M])
        frontier=newf
    return [list(map(tuple,p)) for p in pool]

def check(Npool, tag, ns=(1,2,3)):
    tot=0; fails=0; nwit=0; failed=[]
    for N in Npool:
        N=[tuple(x) for x in N]
        if Lng(N)<2: continue
        if not monoT(N): continue
        j1N=Lng(N)-1
        if idx1(N,j1N)!=1: continue
        if not hasParent(N,1,j1N): continue
        if entry(N,0,j1N)==0 and entry(N,1,j1N)==0: continue
        jm2=parent(N,1,j1N)
        if jm2 is None or jm2>=j1N: continue
        w=j1N-jm2
        delta=entry(N,0,j1N)-entry(N,0,jm2)
        nwit+=1
        for n in ns:
            M=oper(N,n)
            if Lng(M)<2: continue
            if not std(M): continue
            LM=Lng(M)
            for j0p in range(0,LM):
                for j1p in range(j0p+1,LM):
                    Mp=seg(M,j0p,j1p)
                    if Lng(Mp)<2: continue
                    if not monoT(Mp): continue
                    if not le0(M,j0p,j1p): continue
                    if not (j1N<=j1p): continue
                    brle = (TrMax(Mp)==Lng(Mp)-1) or le0(Mp,TrMax(Mp)+1,Lng(Mp)-1)
                    if brle: continue
                    if jm2<=j0p:
                        q=(j0p-jm2)//w
                        j0red=jm2+((j0p-jm2)%w)
                    else:
                        q=0; j0red=j0p
                    j1red=min(j0red+(j1p-j0p), j1N)
                    if not (j0red<j1red): continue
                    if j1red>j1N: continue
                    Nred=seg(N,j0red,j1red)
                    lhs=TrMax(Mp); rhs=TrMax(Nred)
                    tot+=1
                    if lhs!=rhs:
                        fails+=1
                        if len(failed)<6:
                            failed.append((N,n,j0p,j1p,jm2,w,delta,q,j0red,j1red,lhs,rhs))
    print(f"[{tag}] TrEq {tot-fails}/{tot}  (N-witnesses {nwit})", flush=True)
    for ex in failed: print("   FAIL", ex, flush=True)
    return fails

if __name__=="__main__":
    print("building small standard pool...", flush=True)
    small=small_std(5,3)
    print("small std:", len(small), flush=True)
    print("expanding (rank, len up to 13)...", flush=True)
    big=expand_pool(small, 13, ns=(1,2,3,4), iters=6)
    print("expanded pool:", len(big), "max len", max((len(p) for p in big), default=0), flush=True)
    # combine small + expanded for breadth + depth
    allpool=small+big
    check(allpool, "len<=13 combined", ns=(1,2,3))
