"""r80-Y3: THE decisive hunt.

The §7.4 goal depends only on (N,j,j0) with N = Red^2 M (Mark M k = Mark N k, and
Lng is Red-invariant).  Every reduced triple (N,j,j0) on which the goal FAILS is a
potential counterexample to the article's T_PS-level corollary --- provided some
M in T_PS with Red^2 M = N satisfies the article's hypotheses at (j,j0).

This script enumerates the failing reduced triples (entries<=MAXE_N, Lng<=MAXL) and
then, for each, brute-forces preimages M (same Lng --- Red preserves Lng) with
entries <= MAXE_M, testing the article's hypotheses.
"""
import sys, itertools
sys.setrecursionlimit(10000)
from red_model import Lng, le0, Red, Pred, fmt
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

def goal(N, j, j0):
    P = Pred(N)
    da = set((tuple(s),tuple(b)) for s,b in scb_decomps(Mark(P,j), flatBT(Mark(P,j0))))
    db = set((tuple(s),tuple(b)) for s,b in scb_decomps(Mark(N,j), flatBT(Mark(N,j0))))
    return len(da & db) == 1

def hyp_at(M, j, j0):
    """article hypotheses on M: EX! nextAdm parent = j0, (M,j) Marked, le0 M j j0"""
    n = Lng(M)
    if n < 2 or not (j <= j0 < n-1): return False
    cand = [c for c in range(n-1) if le0(M,c,n-1) and adm(M,c)
            and all((not le0(M,x,n-1)) or (not adm(M,x)) for x in range(c+1, n-1))]
    if cand != [j0]: return False
    return adm(M,j) and le0(M,j,n-1) and le0(M,j,j0)

def main():
    maxeN, maxl, maxeM = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    fails = []
    for N in gen_reduced(maxeN, maxl):
        n = Lng(N)
        for j0 in range(n-1):
            if not le0(N, j0, n-1): continue
            for j in range(j0+1):
                if not le0(N, j, j0): continue
                try:
                    if not goal(N, j, j0): fails.append((tuple(N), j, j0))
                except RecursionError: pass
    print(f"# failing reduced triples (entries<={maxeN}, Lng<={maxl}): {len(fails)}")
    bylen = {}
    for (N,j,j0) in fails: bylen.setdefault(len(N), []).append((N,j,j0))
    cols = [(a,b) for a in range(maxeM+1) for b in range(maxeM+1)]
    hits = 0
    for L in sorted(bylen):
        targets = {}
        for (N,j,j0) in bylen[L]: targets.setdefault(N, set()).add((j,j0))
        print(f"# Lng={L}: {len(targets)} distinct N, preimage search over "
              f"{len(cols)}^{L} = {len(cols)**L} sequences (entries<={maxeM})")
        cnt = 0
        for M in itertools.product(cols, repeat=L):
            M = list(M)
            cnt += 1
            # cheap first: does M satisfy the hypotheses for SOME (j,j0)?
            n = L
            cand = [c for c in range(n-1) if le0(M,c,n-1) and adm(M,c)
                    and all((not le0(M,x,n-1)) or (not adm(M,x)) for x in range(c+1, n-1))]
            if len(cand) != 1: continue
            j0 = cand[0]
            js = [j for j in range(j0+1) if adm(M,j) and le0(M,j,n-1) and le0(M,j,j0)]
            if not js: continue
            try: N = tuple(Red(Red(M)))
            except RecursionError: continue
            if N not in targets: continue
            bad = [j for j in js if (j,j0) in targets[N]]
            if bad:
                hits += 1
                print(f"*** COUNTEREXAMPLE  M={fmt(M)}  Red^2 M={fmt(list(N))}  "
                      f"j0={j0}  j in {bad}")
                if hits > 5: return
        print(f"#   scanned {cnt}")
    print(f"# TOTAL preimage counterexamples: {hits}")

main()
