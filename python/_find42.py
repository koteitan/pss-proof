"""Find (4-2) instances quickly: prune generation early.

(4-2) needs: M in RT cap PT, j1=Lng-1>1, j0=parent M 0 j1 admissible,
e1 j0 >= e1 j1, unique next-parent j0' with j0'+1 < j0,
jm1'=Adm M j0' < j0', and e1 j0' >= e1 j0.
"""
import itertools
from trans_model import Trans, Mark, Adm, Dpt, ZB
from red_model import (Lng, entry, seg, parent, Pred, reduced, monoT,
                       hasParent, nextR, adm, Adm as rAdm)


def head_peel(val, v):
    if val[0] != 'T' or len(val[1]) != 1:
        return None
    p = val[1][0]
    if p[0] != 'D' or p[1] != v:
        return None
    return p[2]


def is_suffix_addBT(body, c1):
    bps = body[1]; cps = c1[1]
    if len(cps) > len(bps):
        return False
    return bps[len(bps) - len(cps):] == cps


def gen(maxlen, maxval):
    pairs = [(a, b) for a in range(maxval + 1) for b in range(maxval + 1)]
    for n in range(4, maxlen + 1):
        for tup in itertools.product(pairs, repeat=n - 1):
            yield [(0, 0)] + list(tup)


def run(maxlen, maxval):
    n42 = bad42 = found = 0
    exs = []
    for M in gen(maxlen, maxval):
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
        if not (jm1p < j0p and entry(M, 1, j0p) >= entry(M, 1, j0)):
            continue
        n42 += 1
        PM = Pred(M)
        c1 = Mark(PM, j0)
        tslc = Trans(seg(M, jm1p, j1 - 1))
        v = entry(M, 1, jm1p); w = entry(M, 1, j0p)
        body = head_peel(tslc, v)
        ok = False
        if body is not None and body[1] and body[1][-1][0] == 'D' \
                and body[1][-1][1] == w:
            inner = body[1][-1][2]
            ok = is_suffix_addBT(inner, c1)
        if not ok:
            bad42 += 1
            if len(exs) < 5:
                exs.append(('BAD', M, j0, j0p, jm1p, tslc, c1))
        else:
            found += 1
            if found <= 3:
                exs.append(('OK', M, j0, j0p, jm1p, tslc, c1))
    print(f"maxlen={maxlen} maxval={maxval}: (4-2) {n42} cases, {bad42} bad")
    for e in exs:
        print(" ", e[0], e[1], "j0",e[2],"j0p",e[3],"jm1p",e[4])
        print("      tslc=", e[5])
        print("      c1  =", e[6])


if __name__ == '__main__':
    import sys
    ml = int(sys.argv[1]); mv = int(sys.argv[2])
    run(ml, mv)
