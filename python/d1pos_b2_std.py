#!/usr/bin/env python3
"""B2 on STANDARD d1pos N: branch region Y'=Br(monoT slice M' of M=N[n]).
Test row-1 tie-break of consecutive P-components of Y'."""
import sys, itertools
sys.path.insert(0, __file__.rsplit('/',1)[0])
from red_model import (Lng, entry, oper, idx1, hasParent, parent, P, seg,
                       le0, monoT, TrMax, is_standard)

def d1pos(N):
    if Lng(N) <= 1: return False
    j1 = Lng(N)-1
    if entry(N,0,j1)==0 and entry(N,1,j1)==0: return False
    if entry(N,1,j1) == 0: return False
    if idx1(N,j1) != 1: return False
    if not hasParent(N,1,j1): return False
    return parent(N,1,j1) < j1

def gen_seqs(maxlen, maxval):
    pairs = [(a,b) for a in range(maxval+1) for b in range(maxval+1)]
    for L in range(2, maxlen+1):
        for tup in itertools.product(pairs, repeat=L):
            yield list(tup)

w=0; tie=0; fail=0; nstd=0
for N in gen_seqs(4,2):
    if not d1pos(N): continue
    if not is_standard(N): continue
    nstd+=1
    for n in range(1,4):
        M = oper(N,n)
        if Lng(M)<2: continue
        for j0p in range(Lng(M)):
            for j1p in range(j0p+1, Lng(M)):
                Mp = seg(M,j0p,j1p)
                if not monoT(Mp): continue
                tr=TrMax(Mp)
                if tr==Lng(Mp)-1: continue
                Y=seg(Mp,tr+1,Lng(Mp)-1)
                PY=P(Y)
                if len(PY)<2: continue
                w+=1
                for J in range(1,len(PY)):
                    r0L=entry(PY[J-1],0,0);r0R=entry(PY[J],0,0)
                    r1L=entry(PY[J-1],1,0);r1R=entry(PY[J],1,0)
                    if r0R==r0L:
                        tie+=1
                        if not (r1R<=r1L):
                            fail+=1
                            if fail<=5: print(f"FAIL std N={N} n={n} M'=[{j0p},{j1p}] Y={Y} PY={PY}")
print(f"standard d1pos N={nstd}; Br-of-monoT-slice witnesses={w}, tie pairs={tie}, fails={fail}")
