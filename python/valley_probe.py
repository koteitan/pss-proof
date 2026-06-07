#!/usr/bin/env python3
"""Probe the block-start boundary VALLEY for operCA, to find a RedCondA/RedCondB
based (non-GTWF) discharge.  For reduced tiling N=M[n] and block-start
z=j0+q*w (q>=1), enumerate le0-predecessors j'>pj (pj=parent M 1 j0) and check
entry1(N) j' >= entry M 1 j0.  Classify j' by (block, offset) to expose the
structure that forces the valley."""
import sys
from gtw_tile_fast import (Lng, entry, oper, parent1, hasParent1, idx1, diagSeq,
                           fmt, le0)

def tiling_data(N):
    j1 = Lng(N) - 1
    if j1 <= 0: return None
    if entry(N, 0, j1) == 0 and entry(N, 1, j1) == 0: return None
    if idx1(N, j1) != 1: return None
    if not hasParent1(N, j1): return None
    j0 = parent1(N, j1)
    if not (j0 < j1): return None
    if not hasParent1(N, j0): return None      # need M-side parent of j0 (pj)
    return j0, j1, j1 - j0, parent1(N, j0)

def maxent(M): return max((max(a, b) for (a, b) in M), default=0)

def main():
    MAXLEN = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    MAXE   = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    NMAX   = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    seeds = [diagSeq(a, b) for a in range(0, 4) for b in range(a, a+6)]
    prov = {}; frontier = []
    for s in seeds:
        k = tuple(s)
        if k not in prov and Lng(s) <= MAXLEN and maxent(s) <= MAXE:
            prov[k] = 1; frontier.append(s)
    # buckets: classify valley predecessor j' relative to z's block q
    buck = {}      # (rel_block, offset_sign) -> [tot, dip_below]
    dips = []
    members = 0
    while frontier and members < 2500:
        nxt = []
        for M in frontier:
            td = tiling_data(M)
            for n in range(1, NMAX+1):
                N = oper(M, n); k = tuple(N)
                if k not in prov and Lng(N) <= MAXLEN and maxent(N) <= MAXE:
                    prov[k] = 1; nxt.append(N); members += 1
            if td is None: continue
            j0, j1, w, pj = td
            ev_j0 = entry(M, 1, j0)
            for n in range(1, NMAX+1):
                N = oper(M, n)
                for q in range(1, n):           # q>=1 block starts (q=0 is prefix)
                    z = j0 + q*w
                    if z >= Lng(N): continue
                    for jp in range(pj+1, z+1):
                        if jp == z: continue
                        if not le0(N, jp, z): continue
                        ev = entry(N, 1, jp)
                        # classify jp
                        if jp < j0: rel = "prefix"
                        else:
                            qq = (jp - j0)//w; s = (jp - j0) % w
                            rel = f"blk{qq-q}_s{'0' if s==0 else '+'}"
                        b = buck.setdefault(rel, [0, 0])
                        b[0] += 1
                        if ev < ev_j0:
                            b[1] += 1
                            if len(dips) < 4: dips.append((fmt(M), n, q, jp, ev, ev_j0))
        frontier = nxt
    print(f"members~{members}")
    for rel in sorted(buck):
        t, d = buck[rel]
        print(f"  pred {rel:12s} tot={t:6d} DIP(<entryM1 j0)={d}")
    for x in dips: print("  DIP", x)

if __name__ == "__main__":
    main()
