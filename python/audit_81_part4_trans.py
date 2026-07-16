#!/usr/bin/env python3
"""Empirical audit of lean/8/8.1-part4-trans.lean statements (canonical model).

Checks, over all small reduced mono pair sequences:
  1. c1_around_part4_TransN_41  (Isabelle m_8_1_c1_around_part4_TransN_41, 31445)
     part(4) setup + gap guard + 4-1 guard ==>
       Trans (seg M jm1' j0) = D_{M_{1,jm1'}} (t2 + D_{M_{1,j0}} 0)  for some t2.
  2. c1_around_part4_segpos     (Isabelle m_8_1_c1_around_part4_segpos, 31903)
     the leaf D_{M_{1,j0}} 0 sits in Trans (seg M jm1' j0) at a common scb
     position with c1 = Trans (seg M j0 (j1-1)) in Trans (seg M jm1' (j1-1)).
"""
import itertools
import sys

sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
from trans_model import (Trans, Dpt, addBT, ZB, flatBT, scb_decomps,
                         adm, Adm, reduced)
from red_model import Lng, entry, monoT, leR, seg, parent, hasParent
import red_model as rm


def gen_candidates():
    """Small reduced mono sequences (RT_PS ∩ PT_PS)."""
    for n, emax in ((4, 4), (5, 3)):
        vals = range(emax + 1)
        for cols in itertools.product(itertools.product(vals, vals), repeat=n):
            M = list(cols)
            if not monoT(M):
                continue
            if not reduced(M):
                continue
            yield M


def head_body(t):
    """t = D_v(body) (single principal) -> (v, body) or None."""
    if len(t[1]) != 1:
        return None
    p = t[1][0]
    return (p[1], p[2])


def check_TransN_41(M):
    """Returns (tested, failures)."""
    j1 = Lng(M) - 1
    if j1 <= 1:
        return 0, []
    if not hasParent(M, 0, j1):
        return 0, []
    j0 = parent(M, 0, j1)
    if not adm(M, j0):
        return 0, []
    if not hasParent(M, 0, j0):
        return 0, []
    j0p = parent(M, 0, j0)
    if not rm.nextR(M, 0, j0p, j0):
        return 0, []
    if not (j0p + 1 < j0):
        return 0, []
    jm1 = Adm(M, j0p)
    guard = (jm1 == j0p) or (entry(M, 1, j0p) + 1 == entry(M, 1, j0))
    if not guard:
        return 0, []
    T = Trans(seg(M, jm1, j0))
    hb = head_body(T)
    fails = []
    if hb is None:
        fails.append((M, 'not principal', T))
        return 1, fails
    v, body = hb
    if v != entry(M, 1, jm1):
        fails.append((M, 'head value', T))
        return 1, fails
    # body = t2 + D_{M_{1,j0}} 0  <=> last principal of body is D_{M_{1,j0}}(0)
    if not body[1] or body[1][-1] != ('D', entry(M, 1, j0), ZB):
        fails.append((M, 'trailing leaf', T))
        return 1, fails
    return 1, []


def check_segpos(M):
    """Returns (tested, failures)."""
    tested, fails = 0, []
    n = Lng(M)
    for j1 in range(2, n):          # 1 < j1 < Lng M
        for j0 in range(1, j1 - 1):  # j0 < j1 - 1
            for jm1 in range(j0):    # jm1' < j0
                if not leR(M, 0, jm1, j0):
                    continue
                if not leR(M, 0, jm1, j1 - 1):
                    continue
                S = seg(M, jm1, j1 - 1)
                mm = j0 - jm1
                # Marked S mm
                if not adm(S, mm):
                    continue
                if not leR(S, 0, mm, Lng(S) - 1):
                    continue
                tested += 1
                c1 = Trans(seg(M, j0, j1 - 1))
                leaf = flatBT(Dpt(entry(M, 1, j0), ZB))
                d1 = set(map(lambda sb: (tuple(sb[0]), tuple(sb[1])),
                             scb_decomps(Trans(seg(M, jm1, j0)), leaf)))
                d2 = set(map(lambda sb: (tuple(sb[0]), tuple(sb[1])),
                             scb_decomps(Trans(seg(M, jm1, j1 - 1)),
                                         flatBT(c1))))
                if not (d1 & d2):
                    fails.append((M, jm1, j0, j1))
    return tested, fails


def main():
    n41 = nsp = 0
    f41 = fsp = []
    for M in gen_candidates():
        t, f = check_TransN_41(M)
        n41 += t
        f41 += f
        t, f = check_segpos(M)
        nsp += t
        fsp += f
    print(f'TransN_41: {n41} instances tested, {len(f41)} failures')
    for x in f41[:5]:
        print('  FAIL', x)
    print(f'segpos   : {nsp} instances tested, {len(fsp)} failures')
    for x in fsp[:5]:
        print('  FAIL', x)
    if f41 or fsp:
        sys.exit(1)
    print('OK')


if __name__ == '__main__':
    main()
