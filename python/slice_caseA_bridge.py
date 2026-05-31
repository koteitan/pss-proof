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
nA=0; bridgefail=0; foldfail=0; aeq=0; alt=0
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
                nA+=1
                # final fold result: P(seg M a (LN-2)) @ [blk]*(qb-1) @ [partial]
                fold = P(seg(M,a,LN-2)) + [blk]*(qb-1) + [partial]
                if BrMp != fold:
                    foldfail+=1
                    if foldfail<=8:
                        print("FOLD FAIL",N,n,j0p,j1p,"a",a,"qb",qb,"r2",r2,"LN-2",LN-2)
                        print("  BrMp",BrMp); print("  fold",fold)
                # bridge: P(seg M a (LN-2)) == take J1 (Br N')  ( = BrNp[:J1] )
                bridge_lhs = P(seg(M,a,LN-2))
                bridge_rhs = BrNp[:J1]
                if a < LN-1: alt+=1
                else: aeq+=1
                if bridge_lhs != bridge_rhs:
                    bridgefail+=1
                    if bridgefail<=8:
                        print("BRIDGE FAIL a<LN-1?",a<LN-1,N,n,j0p,j1p,"a",a,"J1",J1)
                        print("  lhs",bridge_lhs); print("  rhs",bridge_rhs)
print("instances",nA,"foldfail",foldfail,"bridgefail",bridgefail,"a<LN-1:",alt,"a=LN-1:",aeq)
