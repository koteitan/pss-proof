# §6.8 d0zero 1466, sub-cases B/C empirical decomposition check.
# Discriminant (after NOT case-A, i.e. TrMax(N') < j0^N - j0'):
#   jm1 = parent_{N'}(0, j0^N - j0');  B: jm1 <= TrMax(N') < j0^N-j0';  C: TrMax(N') < jm1.
# FINDINGS (depth<=6, maxval 2, n<=3):
#   B: FirstNodes(N')_{J1} = j0^N - j0' (Bfnfail=0); prefix take J1 (Br N') agrees (Bprefixfail=0);
#      Br(M') = take J1 (Br N') @ replicate qb blk @ [partial]  -- 'qb' WHOLE blocks, i.e.
#      ONE MORE than case-A (A uses qb-1).  237/237 clean at depth 6.
#   C: ZERO witnesses up to depth 6 / maxval 3 / n<=4 -- decomposition UNVALIDATED empirically.
# CAUTION: case-A machinery does NOT transfer to B:
#   - A-bridge  P(seg M a (Lng N-2)) = take J1 (Br N')  FAILS (60/60) because a=j0'+TrMax+1 <= j0^N.
#   - P-additive split at j0^N also FAILS (120/237): when a>=j0^N the low prefix degenerates ([[]]).
#   High half  P(seg M j0^N j1') = replicate qb blk @ [partial]  IS clean (highfail=0).
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
nB=0; nC=0; Bidfail=0; Cidfail=0; Btags={}
Bfnfail=0; Cfnfail=0
Bprefixfail=0; Cprefixfail=0
Bdescfail=0; Cdescfail=0
def descending_ok(blocks):
    # check Br(Mp) descending using row-0 then row-1 lex of heads (cdom proxy):
    # we just trust BrMp==expect; descending separately checked in proof
    return True
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
                # NOT caseA:
                if (j0N - j0p <= TrNp): continue
                # j_{-1}: parent of (j0N - j0p) in N' along row 0
                tgt = j0N - j0p   # = (0, j0N - j0') position in N'
                if not hasParent(Np,0,tgt): continue
                jm1 = parent(Np,0,tgt)
                BrMp=Br(Mp); BrNp=Br(Np)
                J1=Lng(BrNp)-1
                FN=FirstNodes(Np)  # left endpoints in N'
                blk=seg(N,j0N,(LN-1)-1)
                qb=(j1p - j0N)//w
                r2=(j1p - j0N)%w
                partial=seg(N,j0N,j0N+r2)
                if (jm1 <= TrNp) and (TrNp < tgt):
                    # case B
                    nB+=1
                    if FN[J1] != tgt:
                        Bfnfail+=1
                        if Bfnfail<=5: print("B FN FAIL", N,n,j0p,j1p,"FN[J1]",FN[J1],"tgt",tgt)
                    # Br(Mp) = take J1 (Br Np) @ [blk]*(qb-1) @ ... actually article:
                    # = take J1 BrNp @ blk*(... ) ; article says one more whole block than A:
                    #   Lng(BrMp)-1 = J1 + n - 1  vs A's J1 + n - 2
                    # decomposition: (Br N')_{0..J1-1} ⊕ block^{k=0..n-2} ⊕ partial
                    expectA = BrNp[:J1] + [blk]*(qb-1) + [partial]
                    expectB = BrNp[:J1] + [blk]*qb + [partial]
                    tag=None
                    if BrMp==expectA: tag="A-shape"
                    elif BrMp==expectB: tag="B-shape(qb whole)"
                    if tag is None:
                        Bidfail+=1
                        if Bidfail<=8:
                            print("B ID FAIL",N,n,j0p,j1p,"qb",qb,"r2",r2,"J1",J1,"TrNp",TrNp,"jm1",jm1)
                            print("  BrMp",BrMp); print("  expA",expectA); print("  expB",expectB)
                    else:
                        Btags.setdefault(tag,0)
                        Btags[tag]+=1
                    if BrMp[:J1] != BrNp[:J1]:
                        Bprefixfail+=1
                elif (TrNp < jm1):
                    # case C
                    nC+=1
                    if not (FN[J1] <= jm1):
                        Cfnfail+=1
                        if Cfnfail<=5: print("C FN FAIL", N,n,j0p,j1p,"FN[J1]",FN[J1],"jm1",jm1)
                    # Br(Mp) = take J1 BrNp @ [ seg M (FN[J1]+j0') j1' ]
                    tail = seg(M, FN[J1]+j0p, j1p)
                    expect = BrNp[:J1] + [tail]
                    if BrMp != expect:
                        Cidfail+=1
                        if Cidfail<=8:
                            print("C ID FAIL",N,n,j0p,j1p,"J1",J1,"FN[J1]",FN[J1],"jm1",jm1,"TrNp",TrNp)
                            print("  BrMp",BrMp); print("  exp ",expect)
                    if BrMp[:J1] != BrNp[:J1]:
                        Cprefixfail+=1
                    # junction index FN[J1]+j0' should be < j1N so M=N there
                    if FN[J1]+j0p < j0N:
                        if M[FN[J1]+j0p] != N[FN[J1]+j0p]:
                            print("C MN FAIL", N,n,j0p,j1p)
print("B instances",nB,"Bidfail",Bidfail,"Bfnfail",Bfnfail,"Bprefixfail",Bprefixfail,"tags",Btags)
print("C instances",nC,"Cidfail",Cidfail,"Cfnfail",Cfnfail,"Cprefixfail",Cprefixfail)
