"""Memoisation shim for red_model: le0/le1 recompute the whole reachability
closure on EVERY call, which makes any census O(n^5).  This caches `reach` per
(M, relation) -- semantics-preserving, purely a speed-up.  Import BEFORE anything
that uses red_model/trans_model.
"""
import red_model as rm

_reach_cache = {}
_orig_reach = rm.reach

def reach(M, nextf):
    k = (tuple(M), nextf.__name__)
    r = _reach_cache.get(k)
    if r is None:
        r = _orig_reach(M, nextf)
        _reach_cache[k] = r
    return r

rm.reach = reach

def le0(M, j0, j1):
    n = len(M)
    if not (j0 < n and j1 < n):
        return False
    return reach(M, rm.nextrel0)[j0][j1]

def le1(M, j0, j1):
    n = len(M)
    if not (j0 < n and j1 < n):
        return False
    return reach(M, rm.nextrel1)[j0][j1]

rm.le0 = le0
rm.le1 = le1

def leR(M, i, j0, j1):
    return le0(M, j0, j1) if i == 0 else le1(M, j0, j1)

rm.leR = leR
