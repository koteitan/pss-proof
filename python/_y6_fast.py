"""Memoised wrappers around red_model / trans_model (Red, Trans, Mark, reduced, P).

Monkey-patches the module globals so that the INTERNAL recursion of Red/Trans/Mark
also goes through the cache (they call the module-level names).
Semantics unchanged: all these are pure functions of the pair sequence.
"""
import sys
sys.setrecursionlimit(100000)
import red_model as rm
import trans_model as tm

_le0 = {}
_orig_le0 = rm.le0
def le0(M, a, b):
    k = (tuple(M), a, b)
    v = _le0.get(k)
    if v is None:
        v = _orig_le0(list(M), a, b)
        _le0[k] = v
    return v

_nr0 = {}
_orig_nr0 = rm.nextrel0
def nextrel0(M, a, b):
    k = (tuple(M), a, b)
    v = _nr0.get(k)
    if v is None:
        v = _orig_nr0(list(M), a, b)
        _nr0[k] = v
    return v

_nr1 = {}
_orig_nr1 = rm.nextrel1
def nextrel1(M, a, b):
    k = (tuple(M), a, b)
    v = _nr1.get(k)
    if v is None:
        v = _orig_nr1(list(M), a, b)
        _nr1[k] = v
    return v

_le1 = {}
_orig_le1 = rm.le1
def le1(M, a, b):
    k = (tuple(M), a, b)
    v = _le1.get(k)
    if v is None:
        v = _orig_le1(list(M), a, b)
        _le1[k] = v
    return v

rm.le0 = le0
rm.le1 = le1
rm.nextrel0 = nextrel0
rm.nextrel1 = nextrel1

_red = {}
_orig_Red = rm.Red
def Red(M, depth=0):
    k = tuple(M)
    v = _red.get(k)
    if v is None:
        v = _orig_Red(list(M), depth)
        _red[k] = v
    return v

_reduced = {}
_orig_reduced = tm.reduced
def reduced(M):
    k = tuple(M)
    v = _reduced.get(k)
    if v is None:
        v = _orig_reduced(list(M))
        _reduced[k] = v
    return v

_P = {}
_orig_P = rm.P
def P(M):
    k = tuple(M)
    v = _P.get(k)
    if v is None:
        v = _orig_P(list(M))
        _P[k] = v
    return v

_trans = {}
_orig_Trans = tm.Trans
def Trans(M, depth=0):
    k = tuple(M)
    v = _trans.get(k)
    if v is None:
        v = _orig_Trans(list(M), depth)
        _trans[k] = v
    return v

_mark = {}
_orig_Mark = tm.Mark
def Mark(M, m, depth=0):
    k = (tuple(M), m)
    v = _mark.get(k)
    if v is None:
        v = _orig_Mark(list(M), m, depth)
        _mark[k] = v
    return v

def freeze(t):
    return ('T', tuple((p[0], p[1], freeze(p[2])) for p in t[1]))

_scb = {}
_orig_scb = tm.scb_decomps
def scb_decomps(t, c):
    k = (freeze(t), tuple(c))
    v = _scb.get(k)
    if v is None:
        v = _orig_scb(t, list(c))
        _scb[k] = v
    return v

# patch both module namespaces
rm.Red = Red
rm.P = P
tm.Red = Red
tm.P = P
tm.le0 = le0
tm.reduced = reduced
tm.Trans = Trans
tm.Mark = Mark
tm.scb_decomps = scb_decomps

flatBT = tm.flatBT
Pred = tm.Pred
Lng = rm.Lng
entry = rm.entry
le0 = rm.le0
leR = rm.leR
adm = tm.adm
fmt = rm.fmt
ZB = tm.ZB

def cache_stats():
    return dict(red=len(_red), trans=len(_trans), mark=len(_mark),
                reduced=len(_reduced), scb=len(_scb))

def cache_clear():
    for d in (_red, _reduced, _P, _trans, _mark, _scb):
        d.clear()
