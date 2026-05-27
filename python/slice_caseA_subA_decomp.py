import sys, itertools
sys.path.insert(0, '/home/koteitan/pss-slice/python')
from red_model import (Lng, entry, seg, oper, P, Br, TrMax, FirstNodes,
                       is_standard, parent, idx1, le0, leR, monoT, hasParent)
def all_pairseqs(maxlen, maxval):
    for L in range(1, maxlen+1):
        cells = list(itertools.product(range(maxval+1), repeat=2))
        for tup in itertools.product(cells, repeat=L):
            yield list(tup)
MAXLEN=int(sys.argv[1]); MAXVAL=int(sys.argv[2]); NMAX=int(sys.argv[3])
nA=0; idfail=0; prefixfail=0
for N in all_pairseqs(MAXLEN, MAXVAL):
    if not is_standard(N): continue
    LN=Lng(N)
    if LN<2: continue
    if entry(N,1,LN-1)==0 and entry(N,0,LN-1)==0: continue
    if entry(N,1,LN-1)!=0: continue
    if idx1(N,LN-1)!=0: continue
    if not hasParent(N,0,LN-1): continue
    j0N=parent(N,0,LN-1)
    if not (j0N < LN-1): continue
    w=(LN-1)-j0N
    for n in range(2, NMAX+1):
        M=oper(N,n); LM=Lng(M)
        for j0p in range(0, j0N):
            for j1p in range(j0N+1, LM):
                if j1p > LM-1: continue
                if not (LN-1 <= j1p): continue
                if not leR(M,0,j0p,j1p): continue
                Mp=seg(M,j0p,j1p)
                if not monoT(Mp): continue
                Np=seg(N,j0p,LN-1)
                TrNp=TrMax(Np)
                if not (j0N - j0p <= TrNp): continue
                a=j0p+TrNp+1
                BrMp=Br(Mp); BrNp=Br(Np)
                J1=Lng(BrNp)-1
                blk=seg(N,j0N,(LN-1)-1)
                qb=(j1p - j0N)//w
                r2=(j1p - j0N)%w
                partial=seg(N,j0N,j0N+r2)
                expect = BrNp[:J1] + [blk]*(qb-1) + [partial]
                nA+=1
                if BrMp != expect:
                    idfail+=1
                    if idfail<=8:
                        print("ID FAIL",N,n,j0p,j1p,"qb",qb,"r2",r2)
                        print("  BrMp",BrMp); print("  exp ",expect)
                if BrMp[:J1] != BrNp[:J1]:
                    prefixfail+=1
print("instances",nA,"idfail",idfail,"prefixfail",prefixfail)
