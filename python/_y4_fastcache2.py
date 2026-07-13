"""Memoisation shim for trans_model (Trans / Mark / scb_decomps).  Import AFTER
_y4_fastcache.  Semantics-preserving: the `depth` argument is only a divergence
guard, and the cached value is the value the uncached function would return.
"""
import _y4_fastcache  # noqa: F401  (must come first)
import trans_model as tm

_T = {}
_M = {}
_S = {}

_oT, _oM, _oS = tm.Trans, tm.Mark, tm.scb_decomps


def Trans(M, depth=0):
    k = tuple(M)
    if k not in _T:
        _T[k] = _oT(list(M), depth)
    return _T[k]


def Mark(M, m, depth=0):
    k = (tuple(M), m)
    if k not in _M:
        _M[k] = _oM(list(M), m, depth)
    return _M[k]


def _freeze(t):
    return ('T', tuple(('D', p[1], _freeze(p[2])) for p in t[1]))


def scb_decomps(t, c):
    k = (_freeze(t), tuple(c))
    if k not in _S:
        _S[k] = _oS(t, list(c))
    return _S[k]


tm.Trans = Trans
tm.Mark = Mark
tm.scb_decomps = scb_decomps
