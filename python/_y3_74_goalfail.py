"""r80-Y3: dump the reduced (N,j,j0) triples where the RELAXED goal fails,
with the full N-level diagnostic (adm, le0, joint-decomposition count).

The GOAL only depends on (N,j,j0) with N = Red^2 M (Mark M = Mark N).  So every
possible counterexample to the T_PS-level §7.4 corollary must be one of these
triples, WITH a T_PS preimage M satisfying the article's hypotheses.
"""
import sys, itertools
sys.setrecursionlimit(10000)
from red_model import Lng, le0, Pred, fmt
from trans_model import Mark, flatBT, scb_decomps, reduced, adm

def gen_reduced(maxe, maxl):
    cols = [(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    out = []
    def rec(M):
        if M: out.append(list(M))
        if len(M) == maxl: return
        for c in cols:
            M.append(c)
            if reduced(M): rec(M)
            M.pop()
    rec([])
    return out

def joint(N, j, j0):
    da = set((tuple(s),tuple(b)) for s,b in scb_decomps(Mark(Pred(N),j), flatBT(Mark(Pred(N),j0))))
    db = set((tuple(s),tuple(b)) for s,b in scb_decomps(Mark(N,j),        flatBT(Mark(N,j0))))
    return da & db

def main():
    maxe = int(sys.argv[1]); maxl = int(sys.argv[2])
    Ns = gen_reduced(maxe, maxl)
    print(f"# reduced N, entries<={maxe}, Lng<={maxl}: {len(Ns)}")
    tot = fail = 0
    for N in Ns:
        n = Lng(N)
        for j0 in range(n-1):
            if not le0(N, j0, n-1): continue
            for j in range(j0+1):
                if not le0(N, j, j0): continue
                tot += 1
                try: k = len(joint(N,j,j0))
                except RecursionError: continue
                if k == 1: continue
                fail += 1
                print(f"FAIL {fmt(N)} j={j} j0={j0} |joint|={k} "
                      f"adm_j={adm(N,j)} adm_j0={adm(N,j0)}")
    print(f"# non-vacuous {tot}, failures {fail}")

main()
