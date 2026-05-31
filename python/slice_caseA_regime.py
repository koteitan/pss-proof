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
nA=0
# In regime a<LN-1: check Br Mp = P(seg M a (LN-2)) @ [blk]*(qb-1) @ [partial]
#                   and P(seg M a (LN-2)) = BrNp[:J1] (so total = BrNp[:J1]@..)
# In regime a=LN-1: J1=0, qb computed. check Br Mp = [blk]*(qb-1)@[partial], BrNp[:0]=[]
f_lt=0; f_eq=0; n_lt=0; n_eq=0
# also: when a=LN-1, what is the structure? seg(M,a,j1') with a=LN-1=j0N+w?
# block boundary. Let's check Br Mp = [blk]*(qb-1)+[partial] directly when a=LN-1
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
                if a < LN-1:
                    n_lt+=1
                    lhs=P(seg(M,a,LN-2))
                    if lhs != BrNp[:J1]: f_lt+=1
                else:
                    n_eq+=1
                    # a=LN-1 => J1 should be 0
                    # Br Mp should be [blk]*(qb-1)+[partial]
                    exp=[blk]*(qb-1)+[partial]
                    if BrMp != exp: f_eq+=1
                    if J1 != 0:
                        print("a=LN-1 but J1!=0",N,n,j0p,j1p,"J1",J1)
print("instances",nA,"n_lt",n_lt,"f_lt",f_lt,"n_eq",n_eq,"f_eq",f_eq)
