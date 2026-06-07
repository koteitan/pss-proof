#!/usr/bin/env python3
"""Probe the operCA (RedCondA(N[n])) row-1 proof decomposition for reduced
tiling N.  For each row-1 parent edge (p->c) in N[n], classify child c by
position (prefix s<j0 / block-start s==0 / interior s>0) and confirm
entry1[p]+1==entry1[c].  Tells us which readback cases are actually needed and
whether the (circular) s==0 boundary case arises as a row-1 PARENT child."""
import sys
from gtw_tile_fast import (Lng, entry, oper, parent1, hasParent1, idx1, diagSeq,
                           fmt, _nextrel0_raw)

def parent0_unique(M, j1):
    cs = [j0 for j0 in range(Lng(M)) if _nextrel0_raw(M, j0, j1)]
    return cs[0] if len(cs) == 1 else None

def tiling_data(N):
    j1 = Lng(N) - 1
    if j1 <= 0: return None
    if entry(N, 0, j1) == 0 and entry(N, 1, j1) == 0: return None
    i1 = idx1(N, j1)
    if i1 == 1:
        if not hasParent1(N, j1): return None
        j0 = parent1(N, j1)
    else:
        j0 = parent0_unique(N, j1)
        if j0 is None: return None
    if not (j0 < j1): return None
    return j0, j1, i1, j1 - j0

def maxent(M): return max((max(a, b) for (a, b) in M), default=0)

def main():
    MAXLEN = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    MAXE   = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    NMAX   = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    seeds = [diagSeq(a, b) for a in range(0, 4) for b in range(a, a+7)]
    prov = {}; frontier = []
    for s in seeds:
        k = tuple(s)
        if k not in prov and Lng(s) <= MAXLEN and maxent(s) <= MAXE:
            prov[k] = 1; frontier.append(s)
    cls = {"prefix": [0,0], "block-start": [0,0], "interior": [0,0]}
    bad = []
    members = 0; depth = 0; maxdepth = 0
    while frontier and members < 4000:
        nxt = []
        for M in frontier:
            td = tiling_data(M)
            for n in range(1, NMAX+1):
                N = oper(M, n); k = tuple(N)
                if k not in prov and Lng(N) <= MAXLEN and maxent(N) <= MAXE:
                    prov[k] = 1; nxt.append(N); members += 1
                if td is None: continue
                j0, j1, i1, w = td
                # classify row-1 parent edges of THIS N (=M[n]); use M's tiling
                Nn = oper(M, n)
                for c in range(Lng(Nn)):
                    if not hasParent1(Nn, c): continue
                    p = parent1(Nn, c)
                    ok = (entry(Nn, 1, p) + 1 == entry(Nn, 1, c))
                    if c < j0:
                        key = "prefix"
                    else:
                        s = (c - j0) % w
                        key = "block-start" if s == 0 else "interior"
                    cls[key][0] += 1
                    if not ok:
                        cls[key][1] += 1
                        if len(bad) < 3: bad.append((fmt(M), n, c, key))
        frontier = nxt; depth += 1; maxdepth = max(maxdepth, depth)
    print(f"members~{members} maxdepth={maxdepth}")
    for k, (t, f) in cls.items():
        print(f"  row1 edge child={k:12s} tot={t:6d} FAIL(+1)={f}")
    for b in bad: print("  BAD", b)

if __name__ == "__main__":
    main()
