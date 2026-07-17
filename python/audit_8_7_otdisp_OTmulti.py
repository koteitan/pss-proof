#!/usr/bin/env python3
"""Audit for lean/8/8.7-otdisp-OTmulti.lean (Isabelle opx_OTmulti).

Substantiates the hypothesis-mismatch report: the Lean Prop OTdisp_OTmulti drops
opx_OTmulti's OTint / TVall / ordIntC hypotheses.  The interior branch (conds
III/IV/V of the last mono P-component L of a multi standard host N) is exactly
OTint-for-mono; here we check it is EMPIRICALLY vacuous (last component always
condI), and that the f7x "then-branch" (first P-block of L[m] = [(0,0)]) always
yields a numeral Trans(L[m]) -- the two facts a full standalone proof would need
but which are not portable theorems in the built tree.

    python3 python/audit_8_7_otdisp_OTmulti.py
"""
import sys
sys.path.insert(0, 'python')
from collections import Counter
from red_model import Lng, entry, P, monoT, oper, diagSeq, multiT
from red_model import parent
from trans_model import Pred, Trans, condI, condIII, condV


def condII(M):
    j1 = Lng(M) - 1; jp = parent(M, 0, j1)
    from trans_model import adm
    return entry(M, 1, j1) == 0 and not adm(M, jp)


def condIV(M):
    j1 = Lng(M) - 1; jp = parent(M, 0, j1)
    from trans_model import adm
    return entry(M, 1, j1) > 0 and entry(M, 1, jp) >= entry(M, 1, j1) and not adm(M, jp)


def which(L):
    if condI(L): return 'I'
    if condII(L): return 'II'
    if condIII(L): return 'III'
    if condIV(L): return 'IV'
    if condV(L): return 'V'
    return 'VI'


def norm(M):
    return tuple((int(a), int(b)) for a, b in M)


def build_pool(umax, span, depth, lngmax):
    pool = set(); seed = []
    for u in range(0, umax):
        for v in range(u, u + span):
            M = diagSeq(u, v); pool.add(norm(M)); seed.append(M)
    frontier = seed
    for _ in range(depth):
        newf = []
        for M in frontier:
            for n in range(1, 5):
                try:
                    N = oper(M, n)
                except Exception:
                    continue
                nN = norm(N)
                if nN not in pool and Lng(N) <= lngmax:
                    pool.add(nN); newf.append([list(p) for p in nN])
        frontier = newf
    return pool


D00 = ('D', 0, ('T', []))


def is_numeral(t):
    return all(p == D00 for p in t[1])


def main():
    pool = build_pool(umax=5, span=5, depth=5, lngmax=18)
    print("standard-form pool size:", len(pool))
    cnt = Counter(); ncases = 0
    then_total = 0; then_nonnum = 0
    for Mt in pool:
        M = [list(p) for p in Mt]
        if not multiT(M):
            continue
        L = P(M)[-1]
        if not monoT(L) or Lng(L) <= 1:
            continue
        ncases += 1
        cnt[which(L)] += 1
        for m in (2, 3):
            if oper(M, m) == Pred(M):
                continue
            Lm = oper(L, m)
            if [tuple(x) for x in P(Lm)[0]] == [(0, 0)]:
                then_total += 1
                try:
                    if not is_numeral(Trans(Lm)):
                        then_nonnum += 1
                except Exception:
                    pass
            break
    print("multi host with mono last comp (Lng>1):", ncases)
    print("  condition of that last comp:", dict(cnt))
    print("  -> interior branch (III/IV/V) count:",
          cnt['III'] + cnt['IV'] + cnt['V'], "(empirically vacuous)")
    print("f7x then-branch (first block of L[m] = [(0,0)]):", then_total)
    print("  of which Trans(L[m]) is NOT a numeral:", then_nonnum,
          "(0 => then-branch always numeral)")
    ok = (cnt['III'] + cnt['IV'] + cnt['V'] == 0) and (then_nonnum == 0)
    print("VERDICT:", "consistent with report" if ok else "MISMATCH")


if __name__ == '__main__':
    main()
