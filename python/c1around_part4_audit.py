"""Empirical audit of §8.1 (4-1) and (4-2) existence claims.

(4-1): j0'+1 < j0, (jm1'=j0' or e1 j0'+1 = e1 j0)
   ==> EXISTS t2'. Mark(Pred M) jm1' = Dpt(e1 jm1')(t2' +B c1)
(4-2): j0'+1 < j0, (jm1' < j0' and e1 j0' >= e1 j0)
   ==> EXISTS (t3',t4'). Mark(Pred M) jm1'
         = Dpt(e1 jm1')(t3' +B Dpt(e1 j0')(t4' +B c1))
where c1 = Mark(Pred M) jm1, jm1=Adm M j0, j0=parent M 0 j1, j1=Lng M-1.

Also separately verify the chain pieces:
  (a) c1 = Trans(seg M j0 (j1-1))   [=Mark(Pred M) jm1, jm1=j0 under adm j0]
  (b) Mark(Pred M) jm1' = Trans(seg M jm1' (j1-1))     [Mark_Trans_repr]
  (c) the head + prefix structure
"""
import itertools
from trans_model import Trans, Mark, Adm, Dpt, addBT, flatBT, ZB
from red_model import (Lng, entry, seg, parent, Pred, reduced, monoT,
                       hasParent, nextR, adm)
import red_model as rm


def is_RT(M):
    return reduced(M)


def is_PT(M):
    # PT_PS = T_PS with monoT M (mono on row 0 over the whole sequence)
    return monoT(M)


def gen_seqs(maxlen, maxval):
    # generate candidate pairseqs as tuples of (a,b); fix M[0]=(0,0).
    pairs = [(a, b) for a in range(maxval + 1) for b in range(maxval + 1)]
    for n in range(3, maxlen + 1):
        for tup in itertools.product(pairs, repeat=n - 1):
            M = [(0, 0)] + list(tup)
            yield M


def has_t2_form(val, v, c1):
    # val == Dpt(v)(t2 +B c1) for some t2.  c1 is a single principal.
    # +B concatenates principal lists, so body's principal list must END with
    # c1's principal list (= [the one principal of c1]).
    if val[1] == [] or len(val[1]) != 1:
        return False
    p = val[1][0]  # ('D', vv, body)
    if p[1] != v:
        return False
    body = p[2]
    bps = body[1]      # principal list of body
    cps = c1[1]        # principal list of c1 (length 1)
    if len(cps) > len(bps):
        return False
    return bps[len(bps) - len(cps):] == cps


def has_t34_form(val, v, w, c1):
    # val == Dpt(v)(t3 +B Dpt(w)(t4 +B c1))
    if val[1] == [] or len(val[1]) != 1:
        return False
    p = val[1][0]
    if p[1] != v:
        return False
    body = p[2]
    if body[1] == []:
        return False
    lastp = body[1][-1]  # the LAST principal of body must be Dpt(w)(t4+B c1)
    if lastp[0] != 'D' or lastp[1] != w:
        return False
    inner = lastp[2]
    ips = inner[1]
    cps = c1[1]
    if len(cps) > len(ips):
        return False
    return ips[len(ips) - len(cps):] == cps


def audit(maxlen=6, maxval=3):
    n41 = n42 = 0
    bad41 = bad42 = 0
    chainbad = 0
    examples41 = []
    examples42 = []
    for M in gen_seqs(maxlen, maxval):
        if not is_RT(M) or not is_PT(M):
            continue
        j1 = Lng(M) - 1
        if not (j1 > 1):
            continue
        if not hasParent(M, 0, j1):
            continue
        j0 = parent(M, 0, j1)
        if not adm(M, j0):
            continue
        if not (entry(M, 1, j0) >= entry(M, 1, j1)):
            continue
        # unique next parent j0' of j0
        j0ps = [jp for jp in range(j0) if nextR(M, 0, jp, j0)]
        if len(j0ps) != 1:
            continue
        j0p = j0ps[0]
        jm1 = Adm(M, j0)
        jm1p = Adm(M, j0p)
        c1 = Mark(Pred(M), jm1)
        # chain piece (a): jm1 == j0 (adm j0) and c1 = Trans(seg M j0 (j1-1))
        if jm1 != j0:
            chainbad += 1
        if jm1 < Lng(Pred(M)) - 1:
            if c1 != Trans(seg(M, j0, j1 - 1)):
                chainbad += 1
        if not (j0p + 1 < j0):
            continue
        # (4-1) guard
        if (jm1p == j0p) or (entry(M, 1, j0p) + 1 == entry(M, 1, j0)):
            n41 += 1
            mval = Mark(Pred(M), jm1p)
            v = entry(M, 1, jm1p)
            if not has_t2_form(mval, v, c1):
                bad41 += 1
                if len(examples41) < 5:
                    examples41.append((M, j0, j0p, jm1p, mval, v, c1))
        # (4-2) guard
        if (jm1p < j0p) and (entry(M, 1, j0p) >= entry(M, 1, j0)):
            n42 += 1
            mval = Mark(Pred(M), jm1p)
            v = entry(M, 1, jm1p)
            w = entry(M, 1, j0p)
            if not has_t34_form(mval, v, w, c1):
                bad42 += 1
                if len(examples42) < 5:
                    examples42.append((M, j0, j0p, jm1p, mval, v, w, c1))
    print(f"(4-1): {n41} cases, {bad41} violations")
    print(f"(4-2): {n42} cases, {bad42} violations")
    print(f"chain (a/c1) violations: {chainbad}")
    for e in examples41:
        print("  CEX41:", e)
    for e in examples42:
        print("  CEX42:", e)


if __name__ == '__main__':
    import sys
    ml = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    mv = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    print(f"maxlen={ml} maxval={mv}")
    audit(ml, mv)
