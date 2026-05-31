#!/usr/bin/env python3
"""Find the exact sub-case A decomposition formula for Br M'."""
import sys, itertools
sys.path.insert(0, __file__.rsplit('/',1)[0])
from red_model import (Lng, entry, seg, oper, P, Br, TrMax, FirstNodes,
                       is_standard, parent, idx1, le0, leR, monoT, hasParent)

def all_pairseqs(maxlen, maxval):
    for L in range(1, maxlen+1):
        cells = list(itertools.product(range(maxval+1), repeat=2))
        for tup in itertools.product(cells, repeat=L):
            yield list(tup)

def main():
    import sys as _s
    MAXLEN=int(_s.argv[1]) if len(_s.argv)>1 else 4
    MAXVAL=int(_s.argv[2]) if len(_s.argv)>2 else 3
    NMAX=int(_s.argv[3]) if len(_s.argv)>3 else 4
    nA=0; fails=0
    for N in all_pairseqs(MAXLEN, MAXVAL):
        if not is_standard(N): continue
        LN=Lng(N)
        if LN<2: continue
        if entry(N,1,LN-1)==0 and entry(N,0,LN-1)==0: continue
        if entry(N,1,LN-1)!=0: continue
        i1=idx1(N,LN-1)
        if i1!=0: continue
        if not hasParent(N,i1,LN-1): continue
        j0N=parent(N,0,LN-1)
        if not (j0N < LN-1): continue
        w=(LN-1)-j0N
        for n in range(2, NMAX+1):
            M=oper(N,n); LM=Lng(M)
            for j0p in range(0, j0N):
                for j1p in range(j0N+1, LM):
                    if j1p > LM-1: continue
                    if not (LN-2 <= j1p): continue
                    if not leR(M,0,j0p,j1p): continue
                    Mp=seg(M,j0p,j1p)
                    if not monoT(Mp): continue
                    Np=seg(N,j0p,LN-1)
                    TrNp=TrMax(Np)
                    if not (j0N - j0p <= TrNp): continue
                    a=j0p+TrNp+1
                    BrMp=Br(Mp); BrNp=Br(Np)
                    J1=Lng(BrNp)-1
                    blk=seg(N,j0N,(LN-1)-1)  # seg N j0N (j1N-1), head N!j0N
                    # the tail after take J1 BrNp
                    tail=BrMp[J1:]
                    # candidate: tail = replicate(nfull) blk @ [partial]  where partial=seg N j0N (j0N+rp)
                    # the branch region of M' spans indices [a, j1p] in M.
                    # a maps to N-index: a is past TrNp; a >= j0N (since j0N-j0p<=TrNp => a=j0p+TrNp+1 > j0N)
                    # block-0 fragment then repeated blocks.
                    # Try: the M-index region [a, j1p]; relative to j0N: lo=a-j0N? but a may be in block 0.
                    # Compute via: number of components in tail, and check each.
                    # Derive: r2 = (j1p - j0N) mod w; nblk = (j1p - j0N)//w
                    r2=(j1p - j0N) % w
                    qb=(j1p - j0N)//w
                    # the first tail component is the block-0 remainder: seg N a (j1N-1)? since a in block 0
                    # Build expected tail:
                    # comp0 = P(seg N a (j1N-1)) -- but a>j0N so this is partial-from-left
                    # Actually the structure: BrM' = takeJ1 BrNp @ [blk]*? @ [partial]
                    # Let's just record the multiset shape: how many tail comps equal blk (full), the last partial.
                    nfull=sum(1 for c in tail if c==blk)
                    # check tail = [blk]*nfull then maybe one partial != blk
                    rest=[c for c in tail if c!=blk]
                    okshape = (tail == [blk]*nfull + rest) and len(rest)<=1
                    # the partial (if any)
                    partial = rest[0] if rest else None
                    # hypothesis count: len(tail) == qb (full blocks count incl partial)? and partial when r2>0
                    print(f"N={N} n={n} j0p={j0p} j1p={j1p} j0N={j0N} w={w} a={a} TrNp={TrNp} J1={J1}")
                    print(f"   len(tail)={len(tail)} nfull={nfull} qb={qb} r2={r2} partial={partial} blk={blk} okshape={okshape}")
                    nA+=1
                    if nA>=30:
                        print("...(truncated)"); return
    print("done", nA)

if __name__=='__main__':
    main()
