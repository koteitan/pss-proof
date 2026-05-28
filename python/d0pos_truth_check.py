#!/usr/bin/env python3
"""Empirical truth-check for the d0pos branch of m_6_8 slice (article 1516-1589).

We want descending(Br(seg M j0' j1')) for every standard N in SkT_PS_k and
every M = N[n], j0' < j1' <= Lng M - 1, leR M 0 j0' j1', under the condition

    NOT (j1' < Lng N - 1)    (the "jlarge" case)
    entry N 1 (Lng N - 1) != 0   (d0pos)
    N non-multi
    M non-multi
    Lng N > 1

We enumerate small N matrices and reasonable n, check the side conditions, and
verify the conclusion.
"""
import sys, itertools, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__)))
from red_model import (Lng, entry, leR, le0, multiT, monoT, oper, seg, Br,
                       is_standard, fmt, idx1)

def descending(L):
    # L : list of pairseqs.  descending = weakly decreasing on (row0, row1) of first cell
    for J0 in range(len(L)):
        for J1 in range(J0, len(L)):
            a0 = entry(L[J0],0,0); a1 = entry(L[J0],1,0)
            b0 = entry(L[J1],0,0); b1 = entry(L[J1],1,0)
            if a0 < b0: return False
            if a0 == b0 and a1 < b1: return False
    return True

def candidate_Ns(max_len=5, max_v=3):
    """Enumerate standard pair sequences N with Lng>1 and N non-multi."""
    for L in range(2, max_len+1):
        for cells in itertools.product(itertools.product(range(max_v+1), repeat=2), repeat=L):
            N = list(cells)
            if multiT(N): continue       # need N non-multi
            if not is_standard(N): continue
            yield N

count = 0; hits = 0
counterexamples = []
seen_d0pos = 0
for N in candidate_Ns(max_len=5, max_v=2):
    LN = Lng(N)
    if LN <= 1: continue
    last = LN - 1
    if entry(N,1,last) == 0: continue   # not d0pos
    # try small n values
    for n in range(1, 5):
        M = oper(N, n)
        LM = Lng(M)
        if LM <= 1: continue
        if multiT(M): continue          # need M non-multi (we are in nmN+LNgt branch)
        # iterate j0', j1'
        for j0 in range(LM):
            for j1 in range(j0+1, LM):
                if j1 > LM - 1: continue
                if j1 < LN - 1: continue   # we want jlarge = NOT (j1' < Lng N - 1)
                if not le0(M, j0, j1): continue
                seen_d0pos += 1
                M_seg = seg(M, j0, j1)
                br = Br(M_seg)
                if not descending(br):
                    counterexamples.append((N, n, j0, j1, M_seg, br))
                    print("COUNTEREXAMPLE", "N=", fmt(N), "n=", n, "j0=", j0, "j1=", j1,
                          "M_seg=", fmt(M_seg), "Br=", [fmt(b) for b in br])
                    if len(counterexamples) > 5:
                        sys.exit(2)

print(f"Explored {seen_d0pos} d0pos instances")
if not counterexamples:
    print("PASS: no counterexample at explored depths")
else:
    print(f"FAIL: {len(counterexamples)} counterexamples")
