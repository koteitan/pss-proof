# Focused caseC empirical check: is seg M ?a j1' monoT in every caseC witness?
# (Y proposed a "monoT route" for caseC closure; this verifies the precondition.)
import sys, itertools
sys.path.insert(0, '/home/koteitan/pss-proof/python')
from red_model import (Lng, entry, seg, oper, P, Br, TrMax, FirstNodes,
                       is_standard, parent, idx1, le0, leR, monoT, hasParent)

def all_pairseqs(maxlen, maxval):
    for L in range(1, maxlen+1):
        cells = list(itertools.product(range(maxval+1), repeat=2))
        for tup in itertools.product(cells, repeat=L):
            yield list(tup)

MAXLEN=int(sys.argv[1]); MAXVAL=int(sys.argv[2]); NMAX=int(sys.argv[3])
nC=0; nC_monoT=0; nC_lng1=0; nC_else=0; cex=[]
for N in all_pairseqs(MAXLEN, MAXVAL):
    if not is_standard(N): continue
    LN=Lng(N)
    if LN<2: continue
    # d0zero filter
    if entry(N,1,LN-1)==0 and entry(N,0,LN-1)==0: continue
    if entry(N,1,LN-1)!=0: continue
    if idx1(N,LN-1)!=0: continue
    if not hasParent(N,0,LN-1): continue
    j0N=parent(N,0,LN-1)
    if not (j0N < LN-1): continue
    for n in range(1, NMAX+1):
        M=oper(N,n); LM=Lng(M)
        if LM<2: continue
        if not is_standard(M): continue
        for j0p in range(LM):
            for j1p in range(j0p+1, LM):
                if not leR(M,0,j0p,j1p): continue
                if not (j0p < j0N < j1p): continue  # lt0:False
                Np = seg(N, j0p, LN-1)
                if not Np: continue
                TrNp = TrMax(Np)
                a = j0p + TrNp + 1
                # caseBC:False (TrMax(N') < j0N - j0')
                if not (TrNp < j0N - j0p): continue
                # asmall:True (a < j0N)
                if not (a < j0N): continue
                # caseC: NOT (parent ?Np 0 (j0N-j0') <= TrMax ?Np)
                if not hasParent(Np, 0, j0N - j0p): continue
                pNp = parent(Np, 0, j0N - j0p)
                if pNp <= TrNp: continue  # caseB; we want caseC
                # OK this is caseC. Test: is seg M a j1' monoT?
                nC += 1
                S = seg(M, a, j1p)
                if Lng(S) <= 1:
                    nC_lng1 += 1
                elif monoT(S):
                    nC_monoT += 1
                    # print structural info: is j1' in block 0?
                    if len(cex) < 6:
                        cex.append(("monoT", N, n, j0p, j1p, j0N, LN, a, S))
                else:
                    nC_else += 1
                    if len(cex) < 6:
                        cex.append(("NONmono", N, n, j0p, j1p, j0N, LN, a, S))

print(f"caseC instances: {nC}")
print(f"  Lng(seg M a j1') = 1 (trivial): {nC_lng1}")
print(f"  Lng > 1 AND monoT: {nC_monoT}")
print(f"  Lng > 1 AND NOT monoT (counterexample): {nC_else}")
if cex:
    print("Witnesses:")
    for tag,N,n,j0p,j1p,j0N,LN,a,S in cex:
        print(f"  {tag} N={N} n={n} j0'={j0p} j1'={j1p} j0N={j0N} LN={LN} (j1'<=LN-2? {j1p<=LN-2}) a={a} seg={S}")
