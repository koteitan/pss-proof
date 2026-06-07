#!/usr/bin/env python3
"""Fast self-contained audit of gtw_tile / GTWF-invariance on a broad ST_PS
closure.  Reachability is memoized per sequence so long tiled sequences are
cheap.  No yaBMS dependency: we generate the ST_PS closure directly (the
faithful domain) by BFS from diagSeq seeds under oper(.,n)."""
import sys
from functools import lru_cache

def Lng(M): return len(M)
def entry(M, i, j): return M[j][i]

@lru_cache(maxsize=None)
def _reach0(M):
    n = len(M)
    # nextrel0 adjacency then transitive-reflexive closure
    adj = [[False]*n for _ in range(n)]
    for a in range(n):
        for b in range(a+1, n):
            adj[a][b] = _nextrel0_raw(M, a, b)
    R = [[i == j for j in range(n)] for i in range(n)]
    for a in range(n):
        for b in range(n):
            if adj[a][b]: R[a][b] = True
    for k in range(n):
        for i in range(n):
            if R[i][k]:
                Rk = R[k]
                Ri = R[i]
                for j in range(n):
                    if Rk[j]: Ri[j] = True
    return tuple(tuple(r) for r in R)

def _nextrel0_raw(M, j0, j1):
    n = len(M)
    if not (j0 < n and j1 < n and j0 < j1): return False
    if not (entry(M, 0, j0) < entry(M, 0, j1)): return False
    # le0 within [j0,j1] via direct: nextrel0 is the immediate-next on row0
    # definition: j0<j1, M0[j0]<M0[j1], and for all j0<j<j1: M0[j] >= M0[j1]
    return all(entry(M, 0, j) >= entry(M, 0, j1) for j in range(j0+1, j1))

def le0(M, j0, j1):
    n = len(M)
    if not (j0 < n and j1 < n): return False
    return _reach0(tuple(M))[j0][j1]

def nextrel1(M, j0, j1):
    n = len(M)
    if not (j0 < n and j1 < n and j0 < j1): return False
    if not (entry(M, 1, j0) < entry(M, 1, j1)): return False
    if not le0(M, j0, j1): return False
    return all(entry(M, 1, j) >= entry(M, 1, j1) for j in range(j0+1, n) if le0(M, j, j1))

def hasParent1(M, j1):
    return sum(1 for j0 in range(Lng(M)) if nextrel1(M, j0, j1)) == 1
def parent1(M, j1):
    for j0 in range(Lng(M)):
        if nextrel1(M, j0, j1): return j0
    return None
def idx1(M, j1): return 1 if entry(M, 1, j1) > 0 else 0
def hasParent(M, i, j1):
    if i == 1: return hasParent1(M, j1)
    return sum(1 for j0 in range(Lng(M)) if _nextrel0_raw(M, j0, j1)) == 1

def diagSeq(a, b): return [(j, j) for j in range(a, b+1)]

def oper(M, n):
    j1 = Lng(M) - 1
    if j1 == 0: return list(M)
    if entry(M, 0, j1) == 0 and entry(M, 1, j1) == 0:
        return list(M[:-1]) if Lng(M) > 1 else list(M)
    i1 = idx1(M, j1)
    if not hasParent(M, i1, j1):
        return list(M[:-1]) if Lng(M) > 1 else list(M)
    j0 = parent1(M, j1) if i1 == 1 else (
        [x for x in range(Lng(M)) if _nextrel0_raw(M, x, j1)][0])
    d0 = (entry(M, 0, j1) - entry(M, 0, j0)) if i1 > 0 else 0
    d1 = (entry(M, 1, j1) - entry(M, 1, j0)) if i1 > 1 else 0
    out = list(M[:j0])
    for k in range(n):
        for j in range(j0, j1):
            out.append((entry(M, 0, j) + k*d0, entry(M, 1, j) + k*d1))
    return out

def GTWF(M):
    n = Lng(M)
    for y in range(n):
        if hasParent1(M, y):
            py = parent1(M, y)
            for z in range(py+1, y):
                if not (hasParent1(M, z) and parent1(M, z) >= py):
                    return False
    return True

def tiling_branch(M):
    j1 = Lng(M) - 1
    if j1 == 0: return False
    if entry(M, 0, j1) == 0 and entry(M, 1, j1) == 0: return False
    return hasParent(M, idx1(M, j1), j1)

def fmt(M): return "".join(f"({a},{b})" for (a, b) in M)

def build_closure(seeds, ns, maxlen, maxe, cap=8000):
    seen = set(); closure = []; frontier = []
    def maxent(M): return max((max(a, b) for (a, b) in M), default=0)
    for s in seeds:
        k = tuple(s)
        if k not in seen and Lng(s) <= maxlen and maxent(s) <= maxe:
            seen.add(k); frontier.append(s); closure.append(s)
    while frontier and len(closure) < cap:
        nxt = []
        for M in frontier:
            for n in ns:
                N = oper(M, n); k = tuple(N)
                if k not in seen and Lng(N) <= maxlen and maxent(N) <= maxe:
                    seen.add(k); nxt.append(N); closure.append(N)
                    if len(closure) >= cap: break
            if len(closure) >= cap: break
        frontier = nxt
    return closure

def main():
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    maxe   = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    nmax   = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    seeds = [diagSeq(a, b) for a in range(0, 3) for b in range(a, a+6)]
    ns = list(range(1, nmax+1))
    closure = build_closure(seeds, ns, maxlen, maxe)
    print(f"closure size (maxlen={maxlen}, maxe={maxe}, n=1..{nmax}): {len(closure)}")

    inv_fail = [M for M in closure if not GTWF(M)]
    print(f"GTWF invariant: tested={len(closure)} FAIL={len(inv_fail)}"
          + (f"  ex={fmt(inv_fail[0])}" if inv_fail else "  OK"))

    step_t = step_f = 0; ex = None
    # stress the tiling step with n possibly LARGER than the closure cap
    big_ns = list(range(1, nmax+3))
    for M in closure:
        if GTWF(M) and tiling_branch(M):
            for n in big_ns:
                N = oper(M, n); step_t += 1
                if not GTWF(N):
                    step_f += 1
                    if ex is None: ex = (fmt(M), n, fmt(N))
    print(f"gtw_tile step:  tested={step_t} FAIL={step_f}"
          + (f"  ex M={ex[0]} n={ex[1]} -> N={ex[2]}" if ex else "  OK"))

if __name__ == "__main__":
    main()
