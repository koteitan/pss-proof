#!/usr/bin/env python3
"""Audit the ACTUAL §6.7 residuals (m_6_7_oper_gstrict), NOT the (refuted) GTWF.

  has_gz(K) := j1=Lng K-1 > 0 & hasParent1(K,j1) &
               EX z in (parent1 K j1, j1): hasParent1(K,z) & parent1(K,z) > parent1(K,j1)
  D(K)      := entry K 0 (Lng K-1) == entry K 0 0 + (Lng K-1)

  T_goal (m_6_7_oper_gstrict):  has_gz(N) ==> D(N)
  T_disj:  M in tiling branch (idx1=1, j0<j1) & has_gz(M[n]) ==> has_gz(M) | D(M)
  T_gate:  has_gz(M[n]) ==> [1<Lng M & endpoint!=(0,0) & hasParent(idx1,j1)
                              & idx1=1 & parent1<j1]
"""
import sys
from gtw_tile_fast import (Lng, entry, oper, parent1, hasParent1, hasParent,
                           idx1, diagSeq, fmt, build_closure)

def has_gz(K):
    j1 = Lng(K) - 1
    if j1 <= 0: return False
    if not hasParent1(K, j1): return False
    pj1 = parent1(K, j1)
    for z in range(pj1 + 1, j1):
        if hasParent1(K, z) and parent1(K, z) > pj1:
            return True
    return False

def D(K):
    j1 = Lng(K) - 1
    return entry(K, 0, j1) == entry(K, 0, 0) + j1

def tiling_idx1(M):
    j1 = Lng(M) - 1
    if j1 <= 0: return False
    if entry(M, 0, j1) == 0 and entry(M, 1, j1) == 0: return False
    if idx1(M, j1) != 1: return False
    if not hasParent(M, 1, j1): return False
    return parent1(M, j1) < j1

def main():
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    maxe   = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    nmax   = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    cap    = int(sys.argv[4]) if len(sys.argv) > 4 else 8000
    seeds = [diagSeq(a, b) for a in range(0, 3) for b in range(a, a+6)]
    ns = list(range(1, nmax+1))
    closure = build_closure(seeds, ns, maxlen, maxe, cap=cap)
    print(f"closure size (maxlen={maxlen}, maxe={maxe}, n=1..{nmax}, cap={cap}): {len(closure)}")

    # T_goal
    g_t = g_f = 0; gex = None
    for N in closure:
        if has_gz(N):
            g_t += 1
            if not D(N):
                g_f += 1
                if gex is None: gex = fmt(N)
    print(f"T_goal has_gz=>D:  tested={g_t} FAIL={g_f}" + (f"  ex={gex}" if gex else "  OK"))

    # T_disj and T_gate over gated oper-steps
    d_t = d_f = 0; dex = None
    k_t = k_f = 0; kex = None
    big_ns = list(range(1, nmax+3))
    for M in closure:
        for n in big_ns:
            N = oper(M, n)
            if has_gz(N):
                # gatekeep
                k_t += 1
                if not tiling_idx1(M):
                    k_f += 1
                    if kex is None: kex = (fmt(M), n)
                # disj (only meaningful when M is in tiling branch)
                if tiling_idx1(M):
                    d_t += 1
                    if not (has_gz(M) or D(M)):
                        d_f += 1
                        if dex is None: dex = (fmt(M), n, fmt(N))
    print(f"T_gate:            tested={k_t} FAIL={k_f}" + (f"  ex M={kex[0]} n={kex[1]}" if kex else "  OK"))
    print(f"T_disj:            tested={d_t} FAIL={d_f}" + (f"  ex M={dex[0]} n={dex[1]} -> {dex[2]}" if dex else "  OK"))

if __name__ == "__main__":
    main()
