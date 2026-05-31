# §6.8 d0zero 1466, sub-case B: validate the LOW/HIGH split route used in the proof.
#   B: TrMax(N') < d = j0^N - j0', and parent_{N'}(0,d) = jm1 <= TrMax(N').
#   a = j0' + TrMax(N') + 1   (<= j0^N here, since TrMax < d).
#   Route:  Br M' = P(seg M a j1')
#                 = P(seg M a (j0^N - 1))  @  P(seg M j0^N j1')          (low @ high)
#     low  = P(seg M a (j0^N-1)) = take J1 (Br N')   (trunk-before-block, M=N on [a,j0^N-1])
#     high = P(seg M j0^N j1')   = replicate qb blk @ [partial]          (qb WHOLE blocks)
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
nB=0; idfail=0; lowfail=0; highfail=0; lowtakefail=0; splitfail=0; mnfail=0
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
                if (j0N - j0p <= TrNp): continue   # NOT case A
                tgt = j0N - j0p
                if not hasParent(Np,0,tgt): continue
                jm1 = parent(Np,0,tgt)
                if not (jm1 <= TrNp): continue      # case B only
                a=j0p+TrNp+1
                BrMp=Br(Mp); BrNp=Br(Np)
                J1=Lng(BrNp)-1
                blk=seg(N,j0N,(LN-1)-1)
                qb=(j1p - j0N)//w
                r2=(j1p - j0N)%w
                partial=seg(N,j0N,j0N+r2)
                nB+=1
                # a <= j0^N (in M-coordinate a is j0' + TrNp + 1; in N coordinate the block
                # start is j0N). a relative to M's block start (which is j0N) :
                if not (a <= j0N): mnfail+=1
                high = [blk]*qb + [partial]
                # TWO REGIMES, split on a < j0N (== J1>=1) vs a == j0N (== J1==0):
                if a < j0N:
                    # J1>=1 regime. LOW = P(seg M a (j0^N-1)) = take J1 (Br N'); high anchored at j0N
                    low = P(seg(M, a, j0N-1))
                    if BrMp != low + high:
                        splitfail+=1
                        if splitfail<=6:
                            print("SPLIT FAIL",N,n,j0p,j1p,"a",a,"j0N",j0N,"qb",qb,"r2",r2)
                            print("  BrMp",BrMp);print("  low ",low);print("  high",high)
                    if low != BrNp[:J1]:
                        lowtakefail+=1
                        if lowtakefail<=6:
                            print("LOW=takeJ1 FAIL",N,n,j0p,j1p,"J1",J1)
                            print("  low",low);print("  takeJ1",BrNp[:J1])
                else:
                    # a == j0N, J1==0 regime: Br M' = replicate qb blk @ [partial] directly
                    if J1 != 0:
                        print("REGIME MISMATCH a==j0N but J1=",J1,N,n,j0p,j1p)
                    if BrMp != high:
                        splitfail+=1
                        if splitfail<=6:
                            print("PUREBLK FAIL",N,n,j0p,j1p,"qb",qb,"r2",r2)
                            print("  BrMp",BrMp);print("  high",high)
                # high == replicate qb blk @ [partial]  (independent verification = P(seg M j0N j1'))
                highP = P(seg(M, j0N, j1p))
                if highP != [blk]*qb + [partial]:
                    highfail+=1
                    if highfail<=6:
                        print("HIGH FAIL",N,n,j0p,j1p,"qb",qb,"r2",r2)
                        print("  high",high);print("  exp ",[blk]*qb+[partial])
                # full B decomposition
                if BrMp != BrNp[:J1] + [blk]*qb + [partial]:
                    idfail+=1
print("B instances",nB,"idfail",idfail,"splitfail",splitfail,
      "lowtakefail",lowtakefail,"highfail",highfail,"a>j0N(mnfail)",mnfail)
