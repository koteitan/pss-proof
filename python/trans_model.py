#!/usr/bin/env python3
"""Executable model of §7.3 Trans/Mark (pss_paper.thy 1111-1176, faithful).
BT terms: ('T', [list of BP]); BP: ('D', v, BT). v is an int (enat embedding).
0_B = ('T', []).  Used to empirically verify the §7.3 value propositions
(invariant (Trans M, Mark M m) ∈ T_B^Marked, zeroT, c1<c2, Pred-descent...).
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-gtw/python')
from red_model import (Red, Lng, entry, P, monoT, zeroT, le0, leR, seg,
                       parent, hasParent)
import red_model as rm

ZB = ('T', [])

def Dpt(v, t): return ('T', [('D', v, t)])

def addBT(a, b): return ('T', a[1] + b[1])

def PB(t): return [('T', [p]) for p in t[1]]

def SigmaB(ts):
    out = []
    for t in ts: out += t[1]
    return ('T', out)

def bpHeadV(t): return t[1][0][1] if t[1] else 0
def bpHeadT(t): return t[1][0][2] if t[1] else ZB

# flat: symbol strings; symbols: ('D', v) / 'Z' / '(' / ',' / ')'
def flatBT(t):
    ps = t[1]
    if not ps: return ['Z']
    if len(ps) == 1: return flatBP(ps[0])
    out = ['(']
    out += flatBP(ps[0])
    for p in ps[1:]:
        out.append(',')
        out += flatBP(p)
    out.append(')')
    return out

def flatBP(p): return [('D', p[1])] + flatBT(p[2])

def unflatBT(xs, _memo={}):
    # inverse by parsing (flat is injective); raise if not in image
    t, rest = _parseBT(xs)
    if rest: raise ValueError('unflat: trailing %r' % rest)
    return t

def _parseBT(xs):
    if not xs: raise ValueError('empty')
    if xs[0] == 'Z': return ZB, xs[1:]
    if isinstance(xs[0], tuple) and xs[0][0] == 'D':
        p, rest = _parseBP(xs)
        return ('T', [p]), rest
    if xs[0] == '(':
        ps = []
        rest = xs[1:]
        p, rest = _parseBP(rest)
        ps.append(p)
        while rest and rest[0] == ',':
            p, rest = _parseBP(rest[1:])
            ps.append(p)
        if not rest or rest[0] != ')': raise ValueError('no rp')
        return ('T', ps), rest[1:]
    raise ValueError('bad head %r' % (xs[0],))

def _parseBP(xs):
    if not (isinstance(xs[0], tuple) and xs[0][0] == 'D'): raise ValueError('no D')
    v = xs[0][1]
    t, rest = _parseBT(xs[1:])
    return ('D', v, t), rest

def isPTB_str(c):
    try:
        p, rest = _parseBP(c)
        return not rest
    except Exception:
        return False

def scb_decomps(t, c):
    """All (s,b) with scb_decomp t s c b (c a fixed symbol list)."""
    f = flatBT(t)
    out = []
    n, m = len(f), len(c)
    nontrivial_pt = (t != ZB)
    for i in range(n - m + 1):
        if f[i:i+m] == c:
            s, b = f[:i], f[i+m:]
            if nontrivial_pt and not isPTB_str(c): continue
            if all(x == ')' for x in b): out.append((s, b))
    return out

def adm(M, j):
    if j > Lng(M): return False
    a = rm.nextR(M, 1, max(j-1, 0), j) and rm.nextR(M, 1, j, j+1)
    return not a

def Adm(M, j):
    if adm(M, j): return j
    return max(jp for jp in range(j) if adm(M, jp))

def Pred(M): return M[:-1] if Lng(M) > 1 else M

def reduced(M):
    # keystone m_6_6_reduced_iff_cond (proven): reduced iff RedCondA and RedCondB
    n = Lng(M)
    for j in range(n):
        for i in (0, 1):
            ps = [a for a in range(j) if rm.nextR(M, i, a, j)]
            if len(ps) == 1 and entry(M, i, ps[0]) + 1 != entry(M, i, j):
                return False
    for j in range(n):
        ps = [a for a in range(j) if rm.nextR(M, 0, a, j)]
        if len(ps) != 1 and entry(M, 0, j) != entry(M, 1, j):
            return False
    return True

def Pcut_last(M):
    comps = P(M)
    return Lng(M) - Lng(comps[-1])

def condI(M):
    j1 = Lng(M)-1; jp = parent(M, 0, j1)
    return entry(M,1,j1) == 0 and adm(M, jp)
def condIII(M):
    j1 = Lng(M)-1; jp = parent(M, 0, j1)
    return entry(M,1,j1) > 0 and entry(M,1,jp) >= entry(M,1,j1) and adm(M, jp)
def condV(M):
    j1 = Lng(M)-1; jp = parent(M, 0, j1)
    return entry(M,1,j1) > 0 and entry(M,1,jp)+1 == entry(M,1,j1) and jp+1 < j1
def condVI(M):
    j1 = Lng(M)-1; jp = parent(M, 0, j1)
    return entry(M,1,j1) > 0 and entry(M,1,jp)+1 == entry(M,1,j1) and jp+1 == j1

def Trans(M, depth=0):
    if depth > 200: raise RecursionError('Trans diverges')
    if not reduced(M): return Trans(Red(M), depth+1)
    j1 = Lng(M) - 1
    if j1 == 0:
        return ZB if M[0] == (0,0) else Dpt(entry(M,1,0), ZB)
    if monoT(M):
        t1 = Trans(Pred(M), depth+1)
        if t1 == ZB: return Dpt(0, Dpt(entry(M,1,j1), ZB))
        jp = parent(M, 0, j1)
        c1 = Mark(Pred(M), Adm(M, jp), depth+1)
        v = bpHeadV(c1); t2 = bpHeadT(c1)
        c2 = _c2(M, j1, jp, v, t2)
        ds = scb_decomps(t1, flatBT(c1))
        assert ds, 'no scb decomposition (invariant breach)'
        s1, b1 = ds[0]
        return unflatBT(s1 + flatBT(c2) + b1)
    # multi
    J1 = len(P(M)) - 1; PJ = P(M)[J1]; j0 = j1 - Lng(PJ) + 1
    if PJ == [(0,0)]:
        return addBT(Trans(seg(M,0,j0-1), depth+1), Dpt(0, ZB))
    return addBT(Trans(seg(M,0,j0-1), depth+1), Trans(PJ, depth+1))

def _c2(M, j1, jp, v, t2):
    if condI(M) or condIII(M) or condV(M):
        return Dpt(v, addBT(t2, Dpt(entry(M,1,j1), ZB)))
    if condVI(M):
        return Dpt(v, Dpt(entry(M,1,j1), ZB))
    if t2 == ZB:
        return Dpt(v, Dpt(entry(M,1,jp), Dpt(entry(M,1,j1), ZB)))
    Pt2 = PB(t2); J1b = len(Pt2) - 1; pj = Pt2[J1b]
    leftDj0 = (bpHeadV(pj) == entry(M,1,jp))
    t3 = SigmaB(Pt2[:J1b]) if leftDj0 else t2
    t4 = bpHeadT(pj) if leftDj0 else t2
    return Dpt(v, addBT(t3, Dpt(entry(M,1,jp), addBT(t4, Dpt(entry(M,1,j1), ZB)))))

def Mark(M, m, depth=0):
    if depth > 200: raise RecursionError('Mark diverges')
    if not reduced(M): return Mark(Red(M), m, depth+1)
    j1 = Lng(M) - 1
    if j1 == 0:
        return ZB if M[0] == (0,0) else Dpt(entry(M,1,0), ZB)
    if monoT(M):
        t1 = Trans(Pred(M), depth+1)
        if t1 == ZB:
            return Dpt(0, Dpt(entry(M,1,j1), ZB)) if m == 0 else Dpt(entry(M,1,j1), ZB)
        jp = parent(M, 0, j1)
        c1 = Mark(Pred(M), Adm(M, jp), depth+1)
        v = bpHeadV(c1); t2 = bpHeadT(c1)
        c2 = _c2(M, j1, jp, v, t2)
        if m < j1:
            c0 = Mark(Pred(M), m, depth+1)
            if scb_decomps(c0, flatBT(c1)):
                sm = scb_decomps(c0, flatBT(c1))[0]
                return unflatBT(sm[0] + flatBT(c2) + sm[1])
            return Dpt(entry(M,1,j1), ZB)
        return Dpt(entry(M,1,j1), ZB)
    J1 = len(P(M)) - 1; PJ = P(M)[J1]; j0 = j1 - Lng(PJ) + 1
    if PJ == [(0,0)]: return Dpt(0, ZB)
    return Mark(PJ, m - j0, depth+1)

def dfree_BT(t): return all(dfree_BP(p) for p in t[1])
def dfree_BP(p): return dfree_BT(p[2])   # v != inf always (ints)

if __name__ == '__main__':
    # smoke: twoColumn
    M = [(1,1),(2,2)]
    assert reduced(M) and monoT(M)
    assert Trans(M) == Dpt(1, Dpt(2, ZB)), Trans(M)
    assert Mark(M,0) == Dpt(1, Dpt(2, ZB))
    assert Mark(M,1) == Dpt(2, ZB)
    M2 = [(0,0),(1,1),(2,2)]
    print('Trans (0,0)(1,1)(2,2) =', Trans(M2))
    print('smoke ok')
