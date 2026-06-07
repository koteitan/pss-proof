#!/usr/bin/env python3
"""Fast PSS model: bitset-based row-0 reachability (Python big-int masks) +
targeted enumeration (no full closure BFS).  ~50-100x faster le0 than
red_model.reach, so the boundary-valley mechanism can be verified at the depth
needed to exhibit multi-block dips.

A pairseq is a list of (row0, row1) int tuples.  le0 = reflexive-transitive
closure of nextrel0; stored as one big-int bitmask per node (bit b of R[a] set
iff a le0 b).  All higher predicates (nextrel1, parent1, oper, Red) reuse it."""
from functools import lru_cache

def Lng(M): return len(M)
def entry(M, i, j): return M[j][i]
def fmt(M): return "".join(f"({a},{b})" for (a, b) in M)

@lru_cache(maxsize=None)
def _reach0_masks(M):
    """M is a tuple of pairs; return tuple of big-int bitmasks for row-0 le0."""
    n = len(M)
    r0 = [p[0] for p in M]
    adj = [0]*n
    for a in range(n):
        e0a = r0[a]
        for b in range(a+1, n):
            e0b = r0[b]
            if e0a < e0b:
                ok = True
                for j in range(a+1, b):
                    if r0[j] < e0b:
                        ok = False; break
                if ok:
                    adj[a] |= (1 << b)
    R = [(1 << i) | adj[i] for i in range(n)]
    changed = True
    while changed:
        changed = False
        for i in range(n):
            ri = R[i]; newr = ri; x = ri
            while x:
                b = (x & -x).bit_length() - 1
                newr |= R[b]
                x &= x - 1
            if newr != ri:
                R[i] = newr; changed = True
    return tuple(R)

def le0(M, a, b):
    n = len(M)
    if not (0 <= a < n and 0 <= b < n): return False
    return bool((_reach0_masks(tuple(M))[a] >> b) & 1)

def nextrel0(M, j0, j1):
    n = Lng(M)
    if not (j0 < n and j1 < n and j0 < j1): return False
    if not (entry(M, 0, j0) < entry(M, 0, j1)): return False
    return all(entry(M, 0, j) >= entry(M, 0, j1) for j in range(j0+1, j1))

def nextrel1(M, j0, j1):
    n = Lng(M)
    if not (j0 < n and j1 < n and j0 < j1): return False
    if not (entry(M, 1, j0) < entry(M, 1, j1)): return False
    if not le0(M, j0, j1): return False
    return all(entry(M, 1, j) >= entry(M, 1, j1) for j in range(j0+1, n) if le0(M, j, j1))

def hasParent1(M, j1): return sum(1 for j0 in range(Lng(M)) if nextrel1(M, j0, j1)) == 1
def parent1(M, j1):
    for j0 in range(Lng(M)):
        if nextrel1(M, j0, j1): return j0
    return None
def hasParent0(M, j1): return sum(1 for j0 in range(Lng(M)) if nextrel0(M, j0, j1)) == 1
def parent0(M, j1):
    for j0 in range(Lng(M)):
        if nextrel0(M, j0, j1): return j0
    return None
def idx1(M, j1): return 1 if entry(M, 1, j1) > 0 else 0
def diagSeq(a, b): return [(j, j) for j in range(a, b+1)]

def oper(M, n):
    j1 = Lng(M) - 1
    if j1 == 0: return list(M)
    if entry(M, 0, j1) == 0 and entry(M, 1, j1) == 0:
        return list(M[:-1]) if Lng(M) > 1 else list(M)
    i1 = idx1(M, j1)
    if i1 == 1:
        if not hasParent1(M, j1): return list(M[:-1]) if Lng(M) > 1 else list(M)
        j0 = parent1(M, j1)
    else:
        if not hasParent0(M, j1): return list(M[:-1]) if Lng(M) > 1 else list(M)
        j0 = parent0(M, j1)
    d0 = (entry(M, 0, j1) - entry(M, 0, j0)) if i1 > 0 else 0
    d1 = (entry(M, 1, j1) - entry(M, 1, j0)) if i1 > 1 else 0
    out = list(M[:j0])
    for k in range(n):
        for j in range(j0, j1):
            out.append((entry(M, 0, j) + k*d0, entry(M, 1, j) + k*d1))
    return out

def RedCondA(M):
    n = Lng(M)
    for j in range(n):
        if hasParent0(M, j) and entry(M, 0, parent0(M, j)) + 1 != entry(M, 0, j): return False
        if hasParent1(M, j) and entry(M, 1, parent1(M, j)) + 1 != entry(M, 1, j): return False
    return True
def RedCondB(M):
    n = Lng(M)
    for j in range(n):
        if (not hasParent0(M, j)) and entry(M, 0, j) != entry(M, 1, j): return False
    return True
def reduced(M): return RedCondA(M) and RedCondB(M)

def maxent(M): return max((max(a, b) for (a, b) in M), default=0)

def enum_reduced_tiling(maxlen, maxe):
    """Directly enumerate reduced (RedCondA&RedCondB) tiling-i1=1 sequences,
    small.  No closure; brute force over columns then filter."""
    import itertools
    cols = [(a, b) for a in range(maxe+1) for b in range(maxe+1)]
    out = []
    for L in range(2, maxlen+1):
        for M in itertools.product(cols, repeat=L):
            M = list(M)
            j1 = L-1
            if entry(M, 0, j1) == 0 and entry(M, 1, j1) == 0: continue
            if idx1(M, j1) != 1: continue
            if not hasParent1(M, j1): continue
            if not (parent1(M, j1) < j1): continue
            if reduced(M):
                out.append(M)
    return out
