#!/usr/bin/env python3
"""Audit of §8.4 補題（条件(III)か(IV)の下での基本列の基本性質）part (1)
   (content.md 5000; isabelle p_8_4_oper_basic first `shows`).

Claim (1):  M[n] = M[n+1][1]^{j1 - j_{-2}},  j_{-2} = parent(M,1,j1), j1 = Lng M - 1,
for M in ST_PS ∩ PT_PS, n >= 1, hasParent(M,1,j1), j1 > 1, condIII(M) or condIV(M).

Hosts are REAL standard forms: the diagSeq orbit under oper with n >= 1
(ST_PS is the closure of diagSeq under the fundamental sequence).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm

Lng, entry, oper, Pred = rm.Lng, rm.entry, rm.oper, rm.Pred
parent, hasParent, adm = rm.parent, rm.hasParent, rm.adm


def lastIdx(M):
    return Lng(M) - 1


def lastParent(M):
    return parent(M, 0, lastIdx(M))


def condIII(M):
    j1 = lastIdx(M)
    j0 = lastParent(M)
    if j0 is None:
        return False
    return entry(M, 1, j1) > 0 and entry(M, 1, j1) <= entry(M, 1, j0) and adm(M, j0)


def condIV(M):
    j1 = lastIdx(M)
    j0 = lastParent(M)
    if j0 is None:
        return False
    return entry(M, 1, j1) > 0 and entry(M, 1, j1) <= entry(M, 1, j0) and not adm(M, j0)


def oper1_iter(X, k):
    for _ in range(k):
        X = oper(X, 1)
    return X


def standard_orbit(maxlen, depth, nmax):
    """diagSeq orbit under oper (n>=1) -- genuine ST_PS elements."""
    seeds = [rm.diagSeq(u, v) for u in range(0, 3) for v in range(u, u + 3)]
    seen = {}
    frontier = []
    for S in seeds:
        t = tuple(S)
        if t not in seen:
            seen[t] = S
            frontier.append(S)
    for _ in range(depth):
        nxt = []
        for M in frontier:
            for n in range(1, nmax + 1):
                N = oper(M, n)
                if not N or Lng(N) > maxlen:
                    continue
                t = tuple(N)
                if t not in seen:
                    seen[t] = N
                    nxt.append(N)
        frontier = nxt
        if not frontier:
            break
    return list(seen.values())


def main():
    hosts = standard_orbit(maxlen=14, depth=5, nmax=4)
    checked = fails = 0
    vac_nohost = 0
    for M in hosts:
        j1 = lastIdx(M)
        if not (j1 > 1):
            continue
        if not hasParent(M, 1, j1):
            continue
        if not (condIII(M) or condIV(M)):
            continue
        # PT_PS = reduced and monoT
        if not (rm.reduced(M) and rm.monoT(M)):
            continue
        jm2 = parent(M, 1, j1)
        vac_nohost += 1
        for n in range(1, 6):
            lhs = oper(M, n)
            rhs = oper1_iter(oper(M, n + 1), j1 - jm2)
            checked += 1
            if list(lhs) != list(rhs):
                fails += 1
                if fails <= 5:
                    print("COUNTEREXAMPLE")
                    print("  M   =", M)
                    print("  n   =", n, " j1 =", j1, " j_-2 =", jm2)
                    print("  LHS =", lhs)
                    print("  RHS =", rhs)
    print("hosts in orbit          :", len(hosts))
    print("hosts satisfying hyps   :", vac_nohost)
    print("part(1) instances checked:", checked)
    print("part(1) failures         :", fails)
    print("RESULT:", "PASS" if (fails == 0 and checked > 0) else "FAIL/VACUOUS")


if __name__ == "__main__":
    main()
