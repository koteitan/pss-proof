"""Analyze the BACK-SLICE S = seg M jm1' (j1-1) for (4-1)/(4-2).

slicepeel goal: Trans(S) = Dpt(e1 jm1')(t0 +B c1)    [c1 = Trans(seg M j0 (j1-1))]

Within S (0-indexed), jm1' maps to 0, j0 maps to (j0 - jm1'), j1-1 maps to last.
Record:
 - transJm1(S), cond(I/III/V/VI) of S
 - parent S 0 (Lng S -1)  -- the "j0 of S"
 - whether (j0-jm1') is the rightmost basepoint-ancestor of S
 - whether Trans(S) front-peels at 0 to Dpt(e1 jm1')(body),
   and body == t +B c1   (4-1)   /  body == t3 +B Dpt(e1 j0')(t4 +B c1)  (4-2)
"""
import itertools
from trans_model import (Trans, Mark, Adm, Dpt, ZB, condI, condIII, condV,
                         condVI)
from red_model import (Lng, entry, seg, parent, Pred, reduced, monoT,
                       hasParent, nextR, adm, Adm as rAdm)


def transJm1(N):
    j1 = Lng(N) - 1
    if not hasParent(N, 0, j1):
        return None
    jp = parent(N, 0, j1)
    return rAdm(N, jp)


def head_peel(val, v):
    if val[0] != 'T' or len(val[1]) != 1:
        return None
    p = val[1][0]
    if p[0] != 'D' or p[1] != v:
        return None
    return p[2]


def suffix_ok(body, c1):
    bps = body[1]; cps = c1[1]
    return len(cps) <= len(bps) and bps[len(bps) - len(cps):] == cps


def run(maxlen, maxval):
    rows = {}
    n41 = ok41 = n42 = ok42 = 0
    cex = []
    pairs = [(a, b) for a in range(maxval + 1) for b in range(maxval + 1)]
    for nn in range(4, maxlen + 1):
        for tup in itertools.product(pairs, repeat=nn - 1):
            M = [(0, 0)] + list(tup)
            if not reduced(M) or not monoT(M):
                continue
            j1 = Lng(M) - 1
            if j1 <= 1 or not hasParent(M, 0, j1):
                continue
            j0 = parent(M, 0, j1)
            if not adm(M, j0) or entry(M, 1, j0) < entry(M, 1, j1):
                continue
            j0ps = [jp for jp in range(j0) if nextR(M, 0, jp, j0)]
            if len(j0ps) != 1:
                continue
            j0p = j0ps[0]
            if not (j0p + 1 < j0):
                continue
            jm1p = Adm(M, j0p)
            PM = Pred(M)
            c1 = Mark(PM, j0)
            S = seg(M, jm1p, j1 - 1)
            # S facts
            tjS = transJm1(S)
            sf = (tjS == 0 if tjS is not None else None,
                  condI(S), condIII(S), condV(S), condVI(S))
            # the index of j0 inside S
            j0_in_S = j0 - jm1p
            jpS = parent(S, 0, Lng(S) - 1) if hasParent(S, 0, Lng(S) - 1) else None
            is41 = (jm1p == j0p) or (entry(M, 1, j0p) + 1 == entry(M, 1, j0))
            is42 = (jm1p < j0p) and (entry(M, 1, j0p) >= entry(M, 1, j0))
            tag = '41' if is41 else ('42' if is42 else '?')
            key = (tag, sf, jpS == j0_in_S, j0_in_S, Lng(S) - 1)
            rows[key] = rows.get(key, 0) + 1
            v = entry(M, 1, jm1p)
            body = head_peel(Trans(S), v)
            if is41:
                n41 += 1
                if body is not None and suffix_ok(body, c1):
                    ok41 += 1
            if is42:
                n42 += 1
                w = entry(M, 1, j0p)
                good = False
                if body is not None and body[1] and body[1][-1][0] == 'D' \
                        and body[1][-1][1] == w:
                    good = suffix_ok(body[1][-1][2], c1)
                if good:
                    ok42 += 1
                elif len(cex) < 3:
                    cex.append((M, j0, j0p, jm1p, Trans(S), c1))
    print(f"maxlen={maxlen} maxval={maxval}: 41 {ok41}/{n41}  42 {ok42}/{n42}")
    print("(tag, (tjm1=0,I,III,V,VI), jpS==j0_in_S, j0_in_S, last) -> count")
    for k, c in sorted(rows.items(), key=lambda x: (x[0][0], -x[1])):
        print("   ", k, c)
    for e in cex:
        print("  CEX42:", e[:4], "TransS=", e[4], "c1=", e[5])


if __name__ == '__main__':
    import sys
    ml = int(sys.argv[1]); mv = int(sys.argv[2])
    run(ml, mv)
