"""Scratch: validate the slicepeel witness shape for §8.1 part(4-1)/(4-2).

slicepeel(4-1): Trans(seg M jm1' (j1-1)) = Dpt(e1 jm1')(t0 +B c1)
slicepeel(4-2): Trans(seg M jm1' (j1-1))
                 = Dpt(e1 jm1')(t3 +B Dpt(e1 j0')(t4 +B c1))
where c1 = Mark(Pred M) j0  (= Mark(Pred M) jm1, adm j0 => jm1=j0).

Note the slice is seg M jm1' (j1-1)  (full back-slice, not seg M jm1' j0).
Also separately record the slice N = seg M jm1' j0 facts:
  is N RT? transJm1 N == 0? cond(I/III/V/VI)?
and whether Trans(seg M jm1' (j1-1)) front-peels at jm1' into Dpt(e1 jm1')(body).
"""
import itertools
from trans_model import (Trans, Mark, Adm, Dpt, addBT, flatBT, ZB, condI,
                         condIII, condV, condVI)
import trans_model as tm
from red_model import (Lng, entry, seg, parent, Pred, reduced, monoT,
                       hasParent, nextR, adm, Adm as rAdm)


def is_RT(M):
    return reduced(M)


def is_PT(M):
    return monoT(M)


def transJm1(N):
    j1 = Lng(N) - 1
    if not hasParent(N, 0, j1):
        return None
    jp = parent(N, 0, j1)
    return rAdm(N, jp)


def head_peel(val, v):
    """val == Dpt(v)(body) == Trm[DB v body]: return body or None.
    Dpt is represented as ('T', [('D', v, body)]) (a single-principal Trm)."""
    if val[0] != 'T':
        return None
    if len(val[1]) != 1:
        return None
    p = val[1][0]
    if p[0] != 'D' or p[1] != v:
        return None
    return p[2]


def is_suffix_addBT(body, c1):
    """body == t +B c1 for some t? i.e. c1's principal list is a suffix
    of body's principal list, and prefix is also a valid term (addBT)."""
    bps = body[1]
    cps = c1[1]
    if len(cps) > len(bps):
        return False
    if bps[len(bps) - len(cps):] != cps:
        return False
    # prefix t = Trm(bps[:len-...]) ; any prefix is a valid term in this model
    return True


def gen_seqs(maxlen, maxval):
    pairs = [(a, b) for a in range(maxval + 1) for b in range(maxval + 1)]
    for n in range(3, maxlen + 1):
        for tup in itertools.product(pairs, repeat=n - 1):
            yield [(0, 0)] + list(tup)


def audit(maxlen, maxval):
    n41 = bad41 = 0
    n42 = bad42 = 0
    slice_facts = {}
    cex41 = []
    cex42 = []
    for M in gen_seqs(maxlen, maxval):
        if not is_RT(M) or not is_PT(M):
            continue
        j1 = Lng(M) - 1
        if j1 <= 1 or not hasParent(M, 0, j1):
            continue
        j0 = parent(M, 0, j1)
        if not adm(M, j0):
            continue
        if entry(M, 1, j0) < entry(M, 1, j1):
            continue
        j0ps = [jp for jp in range(j0) if nextR(M, 0, jp, j0)]
        if len(j0ps) != 1:
            continue
        j0p = j0ps[0]
        if not (j0p + 1 < j0):
            continue
        jm1p = Adm(M, j0p)
        PM = Pred(M)
        # c1 = Mark(Pred M) j0  (jm1 == j0 by adm j0)
        c1 = Mark(PM, j0)
        # back-slice value
        slc = seg(M, jm1p, j1 - 1)
        tslc = Trans(slc)
        v = entry(M, 1, jm1p)
        body = head_peel(tslc, v)
        # slice N facts
        N = seg(M, jm1p, j0)
        tj = transJm1(N)
        key = (is_RT(N), tj == 0 if tj is not None else None,
               condI(N), condIII(N), condV(N), condVI(N))
        slice_facts[key] = slice_facts.get(key, 0) + 1
        # (4-1)
        if (jm1p == j0p) or (entry(M, 1, j0p) + 1 == entry(M, 1, j0)):
            n41 += 1
            ok = body is not None and is_suffix_addBT(body, c1)
            if not ok:
                bad41 += 1
                if len(cex41) < 3:
                    cex41.append((M, j0, j0p, jm1p, tslc, c1))
        # (4-2)
        if (jm1p < j0p) and (entry(M, 1, j0p) >= entry(M, 1, j0)):
            n42 += 1
            w = entry(M, 1, j0p)
            ok = False
            if body is not None:
                # body == t3 +B Dpt(w)(t4 +B c1) :
                # find a principal component Dpt(w)(inner) at the end of body
                # whose inner has c1 as a +B-suffix
                if body[1] and body[1][-1][0] == 'D' and body[1][-1][1] == w:
                    inner = body[1][-1][2]
                    ok = is_suffix_addBT(inner, c1)
            if not ok:
                bad42 += 1
                if len(cex42) < 3:
                    cex42.append((M, j0, j0p, jm1p, tslc, c1))
    print(f"maxlen={maxlen} maxval={maxval}")
    print(f"(4-1): {n41} cases, {bad41} bad")
    print(f"(4-2): {n42} cases, {bad42} bad")
    print("slice N facts (isRT, transJm1==0, condI,III,V,VI) -> count:")
    for k, c in sorted(slice_facts.items(), key=lambda x: -x[1]):
        print("   ", k, c)
    for e in cex41:
        print("  CEX41:", e[:4], "tslc=", e[4], "c1=", e[5])
    for e in cex42:
        print("  CEX42:", e[:4], "tslc=", e[4], "c1=", e[5])


if __name__ == '__main__':
    import sys
    ml = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    mv = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    audit(ml, mv)
