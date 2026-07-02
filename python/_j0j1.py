"""For (4-1)/(4-2): is j0 == j1-1 ? what is the slice seg M j0 (j1-1) (=c1's slice)?
And: does Trans(seg M jm1' (j1-1)) front-peel at jm1' DIRECTLY into
Dpt(e1 jm1')(transT2(N) +B c1) where N = seg M jm1' j0 ?
i.e. is the back-slice's transC2-with-c1 the SAME as N's transC2-with-c1-substituted?

Compare:
  LHS = Trans(seg M jm1' (j1-1))
  Build RHS_41 = Dpt(e1 jm1')(transT2(N) +B c1)   [N = seg M jm1' j0]
  check LHS == RHS_41.
"""
import itertools
from trans_model import (Trans, Mark, Adm, Dpt, addBT, ZB, condI, condIII,
                         condV, condVI, bpHeadT, bpHeadV)
import trans_model as tm
from red_model import (Lng, entry, seg, parent, Pred, reduced, monoT,
                       hasParent, nextR, adm, Adm as rAdm)


def transJm1(N):
    j1 = Lng(N) - 1
    if not hasParent(N, 0, j1):
        return None
    jp = parent(N, 0, j1)
    return rAdm(N, jp)


def transT2(N):
    # transT2 N = bpHeadT(transC1 N); transC1 N = Mark(Pred N)(transJm1 N)
    j1 = Lng(N) - 1
    jp = parent(N, 0, j1)
    jm1 = rAdm(N, jp)
    c1 = Mark(Pred(N), jm1)
    return bpHeadT(c1)


def run(maxlen, maxval):
    n = bad = 0
    eqj = 0
    rhs_ok = 0
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
            is41 = (Adm(M, j0p) == j0p) or (entry(M, 1, j0p) + 1 == entry(M, 1, j0))
            if not is41:
                continue
            n += 1
            jm1p = Adm(M, j0p)
            PM = Pred(M)
            c1 = Mark(PM, j0)
            LHS = Trans(seg(M, jm1p, j1 - 1))
            N = seg(M, jm1p, j0)
            t2N = transT2(N)
            v = entry(M, 1, jm1p)
            RHS = Dpt(v, addBT(t2N, c1))
            if j0 == j1 - 1:
                eqj += 1
            if LHS == RHS:
                rhs_ok += 1
            else:
                bad += 1
                if len(cex) < 4:
                    cex.append((M, j0, j1, j0p, jm1p, LHS, RHS, t2N, c1))
    print(f"maxlen={maxlen} maxval={maxval}: 41 {n} cases; "
          f"j0==j1-1: {eqj}; RHS_41(==Dpt v (t2N +B c1)) match: {rhs_ok}; bad {bad}")
    for e in cex:
        print("  CEX:", e[:5])
        print("    LHS=", e[5])
        print("    RHS=", e[6])
        print("    t2N=", e[7], " c1=", e[8])


if __name__ == '__main__':
    import sys
    ml = int(sys.argv[1]); mv = int(sys.argv[2])
    run(ml, mv)
