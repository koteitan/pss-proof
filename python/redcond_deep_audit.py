#!/usr/bin/env python3
"""DEEP-closure audit (depth>=8, provenance-tracked) of the FAITHFUL §6.7 target:
  operCA/operCB:  M in ST_PS reduced  ==>  RedCondA(M[n]) & RedCondB(M[n])
and the global target ST_PS subset RT_PS (reduced) via RedCondA & RedCondB.

This replaces the (refuted) has_gz=>D route.  RedCondA is the LOCAL parent+1
condition; RedCondB the no-row0-parent => rows-equal condition."""
import sys
from gtw_tile_fast import (Lng, entry, oper, parent1, hasParent1, hasParent,
                           idx1, diagSeq, fmt)

def parent0(M, j1):
    cands = [j0 for j0 in range(Lng(M)) if _nr0(M, j0, j1)]
    return cands[0] if len(cands) == 1 else None
def _nr0(M, j0, j1):
    n = Lng(M)
    if not (j0 < n and j1 < n and j0 < j1): return False
    if not (entry(M, 0, j0) < entry(M, 0, j1)): return False
    return all(entry(M, 0, j) >= entry(M, 0, j1) for j in range(j0+1, j1))
def hasParent0(M, j1):
    return sum(1 for j0 in range(Lng(M)) if _nr0(M, j0, j1)) == 1

def RedCondA(M):
    n = Lng(M)
    for j in range(n):
        if hasParent0(M, j):
            if entry(M, 0, parent0(M, j)) + 1 != entry(M, 0, j): return False
        if hasParent1(M, j):
            if entry(M, 1, parent1(M, j)) + 1 != entry(M, 1, j): return False
    return True

def RedCondB(M):
    n = Lng(M)
    for j in range(n):
        if (not hasParent0(M, j)) and j <= n-1:
            if entry(M, 0, j) != entry(M, 1, j): return False
    return True

def maxent(M): return max((max(a, b) for (a, b) in M), default=0)

def main():
    MAXLEN = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    MAXE   = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    NMAX   = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    seeds = [diagSeq(a, b) for a in range(0, 4) for b in range(a, a+7)]
    prov = {}; frontier = []
    for s in seeds:
        k = tuple(s)
        if k not in prov and Lng(s) <= MAXLEN and maxent(s) <= MAXE:
            prov[k] = (None, 0, 0); frontier.append(s)
    # BFS, check RedCondA/B per member; also operCA step (M reduced -> M[n] cond)
    memb = 0; ca_f = cb_f = 0; depth = 0
    caex = cbex = None; maxdepth = 0
    while frontier:
        nxt = []
        for M in frontier:
            for n in range(1, NMAX+1):
                N = oper(M, n); k = tuple(N)
                if k not in prov and Lng(N) <= MAXLEN and maxent(N) <= MAXE:
                    prov[k] = (tuple(M), n, depth+1); nxt.append(N); memb += 1
                    if not RedCondA(N):
                        ca_f += 1
                        if caex is None: caex = (fmt(N), depth+1)
                    if not RedCondB(N):
                        cb_f += 1
                        if cbex is None: cbex = (fmt(N), depth+1)
        frontier = nxt; depth += 1; maxdepth = max(maxdepth, depth)
    print(f"members={memb} maxdepth={maxdepth} (MAXLEN={MAXLEN},MAXE={MAXE},n<= {NMAX})")
    print(f"RedCondA(N): FAIL={ca_f}" + (f"  ex={caex}" if caex else "  OK"))
    print(f"RedCondB(N): FAIL={cb_f}" + (f"  ex={cbex}" if cbex else "  OK"))

if __name__ == "__main__":
    main()
