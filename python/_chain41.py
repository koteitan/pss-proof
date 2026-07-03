"""Validate the FULL (4-1) proof chain via m_7_4_Trans_Mark_seg geometry.

Let S = seg M jm1' (j1-1), mS = j0 - jm1' (position of j0 inside S).
Claims to validate:
 (A) (S, mS) in Marked,  0 < mS < Lng S - 1
 (B) entry S 1 mS = entry M 1 j0
 (C) Mark S mS = c1  = Mark(Pred M) j0  = Trans(seg M j0 (j1-1))
 (D) seg S 0 mS = seg M jm1' j0  (= N)
 (E) Trans N = Dpt(transV N)(transT2 N +B Dpt(entry M 1 j0) 0B)   [transC2, condI/III/V]
 (F) Trans S = Dpt(entry M 1 jm1')(transT2 N +B c1)               [final 4-1 RHS]
"""
import itertools
from trans_model import (Trans, Mark, Adm, Dpt, addBT, ZB, condI, condIII,
                         condV, condVI, bpHeadT, bpHeadV)
import trans_model as tm
from red_model import (Lng, entry, seg, parent, Pred, reduced, monoT,
                       hasParent, nextR, adm, Adm as rAdm, marked)


def transJm1(N):
    j1 = Lng(N) - 1
    if not hasParent(N, 0, j1):
        return None
    return rAdm(N, parent(N, 0, j1))


def transT2(N):
    j1 = Lng(N) - 1
    jp = parent(N, 0, j1)
    jm1 = rAdm(N, jp)
    return bpHeadT(Mark(Pred(N), jm1))


def transV(N):
    j1 = Lng(N) - 1
    jp = parent(N, 0, j1)
    jm1 = rAdm(N, jp)
    return bpHeadV(Mark(Pred(N), jm1))


def run(maxlen, maxval):
    n = 0
    failA = failB = failC = failD = failE = failF = 0
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
            if not ((jm1p == j0p) or (entry(M, 1, j0p) + 1 == entry(M, 1, j0))):
                continue
            n += 1
            PM = Pred(M)
            c1 = Mark(PM, j0)
            S = seg(M, jm1p, j1 - 1)
            mS = j0 - jm1p
            N = seg(M, jm1p, j0)
            # (A)
            if not (marked(S, mS) and 0 < mS < Lng(S) - 1):
                failA += 1
            # (B)
            if entry(S, 1, mS) != entry(M, 1, j0):
                failB += 1
            # (C)
            if Mark(S, mS) != c1:
                failC += 1
            # (D)
            if seg(S, 0, mS) != N:
                failD += 1
            # (E) transC2 form of N
            if transJm1(N) == 0 and (condI(N) or condIII(N) or condV(N)):
                rhsE = Dpt(transV(N), addBT(transT2(N),
                                            Dpt(entry(M, 1, j0), ZB)))
                if Trans(N) != rhsE:
                    failE += 1
            else:
                failE += 1  # we rely on this branch
            # (F)
            rhsF = Dpt(entry(M, 1, jm1p), addBT(transT2(N), c1))
            if Trans(S) != rhsF:
                failF += 1
    print(f"maxlen={maxlen} maxval={maxval}: {n} (4-1) cases")
    print(f"  failA(marked/pos)={failA} failB(entry)={failB} "
          f"failC(MarkS=c1)={failC}")
    print(f"  failD(segN)={failD} failE(transC2 N)={failE} failF(final)={failF}")


if __name__ == '__main__':
    import sys
    ml = int(sys.argv[1]); mv = int(sys.argv[2])
    run(ml, mv)
