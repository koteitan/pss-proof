#!/usr/bin/env python3
"""Empirical check of B2 (d1pos row-1 tie-break for branch-region P-components).

The branch region is Y' = seg M' (TrMax M'+1) (Lng M'-1) where M' = seg M j0' j1'
is a MONOT slice of M = N[n] (d1pos oper).  Test the row-1 tie-break on
consecutive P-components of Y' (= Br M').  Also test alternate clean hypotheses
to pin the minimal sufficient condition for B2 as a self-contained lemma.
"""
import sys, itertools
sys.path.insert(0, __file__.rsplit('/',1)[0])
from red_model import (Lng, entry, oper, idx1, hasParent, parent, P, seg,
                       le0, nextR, monoT, IdxSum, TrMax)

def d1pos(N):
    if Lng(N) <= 1: return False
    j1 = Lng(N)-1
    if entry(N,0,j1)==0 and entry(N,1,j1)==0: return False
    if entry(N,1,j1) == 0: return False
    if idx1(N,j1) != 1: return False
    if not hasParent(N,1,j1): return False
    j0 = parent(N,1,j1)
    if not (j0 < j1): return False
    return True

def gen_seqs(maxlen, maxval):
    pairs = [(a,b) for a in range(maxval+1) for b in range(maxval+1)]
    for L in range(2, maxlen+1):
        for tup in itertools.product(pairs, repeat=L):
            yield list(tup)

# Stat counters for the actual structure: Y' = branch of monoT slice M'
w_brY = 0; tie_brY = 0; fail_brY = 0

# Also: the CLEAN abstract hypothesis "Q = seg M a b, where component left-ends
# of P Q are each le0-reachable in M from the slice start a" - test this.
w_anchor = 0; tie_anchor = 0; fail_anchor = 0

for N in gen_seqs(4, 2):
    if not d1pos(N): continue
    for n in range(1,4):
        M = oper(N, n)
        if Lng(M) < 2: continue
        for j0p in range(Lng(M)):
            for j1p in range(j0p+1, Lng(M)):
                Mp = seg(M, j0p, j1p)
                if not monoT(Mp): continue
                tr = TrMax(Mp)
                if tr == Lng(Mp)-1: continue   # Br empty
                Y = seg(Mp, tr+1, Lng(Mp)-1)
                PY = P(Y)
                if len(PY) < 2: continue
                w_brY += 1
                for J in range(1, len(PY)):
                    r0L=entry(PY[J-1],0,0); r0R=entry(PY[J],0,0)
                    r1L=entry(PY[J-1],1,0); r1R=entry(PY[J],1,0)
                    if r0R == r0L:
                        tie_brY += 1
                        if not (r1R <= r1L):
                            fail_brY += 1
                            if fail_brY<=5:
                                print(f"BR-Y FAIL N={N} n={n} M'=[{j0p},{j1p}] Y={Y} PY={PY}")

print(f"Y'=Br(monoT slice): witnesses={w_brY}, row0-tie pairs={tie_brY}, fails={fail_brY}")
