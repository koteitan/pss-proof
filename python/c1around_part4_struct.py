"""Structural facts for §8.1 (4-1)/(4-2) formal proof design.

For each RT∩PT M satisfying the (4) hypotheses, record:
 - jm1 == j0  (adm j0)
 - Mark(Pred M) jm1' = Trans(seg M jm1' (j1-1))   [Mark_Trans_repr]
 - c1 = Trans(seg M j0 (j1-1))
 - the slice N = seg M jm1' j0 :  is it RT? PT? transJm1 N == 0?  cond?
 - Trans N relation to Mark(Pred M) jm1'
 - (4-1): Mark(Pred M) jm1' = Dpt(e1 jm1')(t2' +B c1), with c1 a true +B-suffix
 - (4-2): two-layer form, c1 a true suffix of the inner body
Search smarter: build sequences that are reduced+monoT directly via small enum,
but allow longer lengths by maxval=1 (so 4^(n-1) base seqs).
"""
import itertools
from trans_model import (Trans, Mark, Adm, Dpt, addBT, flatBT, ZB, condI,
                         condIII, condV, condVI)
import trans_model as tm
from red_model import (Lng, entry, seg, parent, Pred, reduced, monoT,
                       hasParent, nextR, adm, Adm as rAdm)
import red_model as rm


def is_RT(M):
    return reduced(M)


def is_PT(M):
    return monoT(M)


def untrm(t):
    return t[1]


def suffix_form_t2(val, v, c1):
    if val[1] == [] or len(val[1]) != 1:
        return False
    p = val[1][0]
    if p[1] != v:
        return False
    bps = p[2][1]
    cps = c1[1]
    return len(cps) <= len(bps) and bps[len(bps) - len(cps):] == cps


def suffix_form_t34(val, v, w, c1):
    if val[1] == [] or len(val[1]) != 1:
        return False
    p = val[1][0]
    if p[1] != v:
        return False
    body = p[2]
    if body[1] == []:
        return False
    lastp = body[1][-1]
    if lastp[0] != 'D' or lastp[1] != w:
        return False
    ips = lastp[2][1]
    cps = c1[1]
    return len(cps) <= len(ips) and ips[len(ips) - len(cps):] == cps


def transJm1(N):
    # transJm1 N = Adm_N(parent N 0 (Lng N - 1))
    j1 = Lng(N) - 1
    if not hasParent(N, 0, j1):
        return None
    jp = parent(N, 0, j1)
    return rAdm(N, jp)


def gen_seqs(maxlen, maxval):
    pairs = [(a, b) for a in range(maxval + 1) for b in range(maxval + 1)]
    for n in range(3, maxlen + 1):
        for tup in itertools.product(pairs, repeat=n - 1):
            yield [(0, 0)] + list(tup)


def audit(maxlen, maxval):
    n41 = bad41 = 0
    n42 = bad42 = 0
    repr_bad = 0
    c1_bad = 0
    slice_notRT = 0
    slice_jm1_nonzero = 0
    ex42 = []
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
        jm1 = Adm(M, j0)
        jm1p = Adm(M, j0p)
        PM = Pred(M)
        c1 = Mark(PM, jm1)
        # repr check
        if jm1p < Lng(PM) - 1:
            if Mark(PM, jm1p) != Trans(seg(M, jm1p, j1 - 1)):
                repr_bad += 1
        if c1 != Trans(seg(M, j0, j1 - 1)):
            c1_bad += 1
        # slice N = seg M jm1' j0
        N = seg(M, jm1p, j0)
        if not is_RT(N):
            slice_notRT += 1
        tj = transJm1(N)
        if tj is not None and tj != 0:
            slice_jm1_nonzero += 1
        mval = Mark(PM, jm1p)
        if (jm1p == j0p) or (entry(M, 1, j0p) + 1 == entry(M, 1, j0)):
            n41 += 1
            v = entry(M, 1, jm1p)
            if not suffix_form_t2(mval, v, c1):
                bad41 += 1
        if (jm1p < j0p) and (entry(M, 1, j0p) >= entry(M, 1, j0)):
            n42 += 1
            v = entry(M, 1, jm1p)
            w = entry(M, 1, j0p)
            if not suffix_form_t34(mval, v, w, c1):
                bad42 += 1
            elif len(ex42) < 3:
                ex42.append((M, j0, j0p, jm1p, mval, v, w, c1))
    print(f"(4-1): {n41} cases, {bad41} bad")
    print(f"(4-2): {n42} cases, {bad42} bad")
    print(f"repr_bad={repr_bad} c1_bad={c1_bad} "
          f"slice_notRT={slice_notRT} slice_jm1_nonzero={slice_jm1_nonzero}")
    for e in ex42:
        print("  ok42:", e[:4])


if __name__ == '__main__':
    import sys
    ml = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    mv = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    print(f"maxlen={ml} maxval={mv}")
    audit(ml, mv)
