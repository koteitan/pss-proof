#!/usr/bin/env python3
"""Empirical reachability check for dead-branch[20] of Red (§6.5).

dead-branch[20] = the `else: return M` fall-through in Red's mono / M0!=(0,0) /
m10>0 case (red_model.py line ~163), taken when NOT
  (m10 <= jN  AND  seg(N, m10, jN) is monoT)
with N = Red(diagSeq(0,m10-1) ++ IncrFirst^{m10}(M)), jN = Lng N - 1.

The §6.5 propositions claim this branch never occurs. This script runs an
instrumented Red on standard-form inputs (yaBMS is_standard filter) and ALL
their recursive sub-calls, counting how often the m10>0 case is reached and
whether the dead branch is ever taken.
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/python')
from red_model import (Lng, entry, zeroT, multiT, monoT, P, TrMax, Br,
                       FirstNodes, Joints, THE_nextR, diagSeq, IncrFirst,
                       funpow, seg, is_standard, fmt)

stats = {'m10pos': 0, 'dead': 0, 'examples': []}

def Red_inst(M, depth=0):
    if depth > 200: raise RuntimeError("deep "+fmt(M))
    if zeroT(M): return [(0,0)]
    if multiT(M):
        out=[]
        for blk in P(M): out += Red_inst(blk, depth+1)
        return out
    j1=Lng(M)-1; j1p=TrMax(M); m00=entry(M,0,0); m10=entry(M,1,0)
    if m00==0 and m10==0:
        if j1p==j1:
            return diagSeq(m10, m10+j1)
        out=diagSeq(0,j1p); b=Br(M); fn=FirstNodes(M); jn=Joints(M)
        for J in range(len(b)):
            br10=entry(b[J],1,0)
            np = 0 if br10==0 else THE_nextR(M,1,fn[J])+1
            eJ=jn[J]+1-np
            NJ=[(m00+jn[J]+1, m10+np)]+b[J][1:]
            out+=funpow(IncrFirst, eJ, Red_inst(NJ, depth+1))
        return out
    if m10==0:
        core=[(entry(M,0,j)-m00, entry(M,1,j)) for j in range(j1+1)]
        return Red_inst(core, depth+1)
    # ---- m10 > 0 case: the dead-branch[20] lives here ----
    stats['m10pos'] += 1
    N=Red_inst(diagSeq(0,m10-1)+funpow(IncrFirst,m10,M), depth+1)
    jN=Lng(N)-1; sg=seg(N,m10,jN)
    if m10<=jN and len(sg)>0 and monoT(sg):
        return [(entry(N,0,j)-entry(N,0,m10)+entry(N,1,m10), entry(N,1,j)) for j in range(m10,jN+1)]
    # dead branch taken:
    stats['dead'] += 1
    if len(stats['examples']) < 10:
        stats['examples'].append((fmt(M), fmt(N), m10, jN))
    return M

def all_pairseqs(maxlen, maxval):
    cells=list(itertools.product(range(maxval+1), repeat=2))
    for L in range(1, maxlen+1):
        for tup in itertools.product(cells, repeat=L):
            yield list(tup)

if __name__=="__main__":
    MAXLEN=int(sys.argv[1]) if len(sys.argv)>1 else 5
    MAXVAL=int(sys.argv[2]) if len(sys.argv)>2 else 6
    nstd=0
    for M in all_pairseqs(MAXLEN, MAXVAL):
        if not is_standard(M): continue
        nstd += 1
        try: Red_inst(M)
        except RuntimeError as e:
            print("DEEP/ERROR on", fmt(M), e)
    print(f"standard inputs tested: {nstd}  (maxlen={MAXLEN}, maxval={MAXVAL})")
    print(f"m10>0 case reached:    {stats['m10pos']} times")
    print(f"dead-branch[20] taken: {stats['dead']} times")
    if stats['dead']:
        print("COUNTEREXAMPLES (M, N, m10, jN):")
        for e in stats['examples']: print("  ", e)
    else:
        print("=> dead-branch[20] UNREACHABLE on all tested standard inputs + sub-calls ✓")
