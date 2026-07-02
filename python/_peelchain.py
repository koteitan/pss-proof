"""For (4-1)/(4-2): on Pred M, what are the marked indices in [jm1', j0]?
And does Mark(Pred M) jm1' telescope down to Mark(Pred M) j0 via adjacency/gap?

Record: marked indices of Pred M in [jm1', j0]; admissible indices in (jm1', j0).
Check the form of Mark(Pred M) jm1' as a nested D-peel ending in c1=Mark(Pred M)j0.
"""
import itertools
from trans_model import Trans, Mark, Adm, Dpt, ZB
from red_model import (Lng, entry, seg, parent, Pred, reduced, monoT,
                       hasParent, nextR, adm, Adm as rAdm)


def marked(M, m):
    # (M,m) in Marked: m admissible-anchored leq0 to last
    j1 = Lng(M) - 1
    if m > j1:
        return False
    # Marked_def: M in T_PS and adm-chain le0 to last. Use rm.Marked via Mark?
    # In trans_model, Mark is only defined on marked indices; use Marked test.
    import red_model as rm
    return rm.marked(M, m) if hasattr(rm, 'Marked') else None


def run(maxlen, maxval):
    import red_model as rm
    has_marked = hasattr(rm, 'marked')
    pairs = [(a, b) for a in range(maxval + 1) for b in range(maxval + 1)]
    rows = {}
    cnt = 0
    for n in range(4, maxlen + 1):
        for tup in itertools.product(pairs, repeat=n - 1):
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
            # which k in [jm1p, j0] are marked on PM?
            if has_marked:
                mk = [k for k in range(jm1p, j0 + 1) if rm.marked(PM, k)]
            else:
                mk = '?'
            admk = [k for k in range(jm1p + 1, j0) if adm(PM, k)]
            is41 = (jm1p == j0p) or (entry(M, 1, j0p) + 1 == entry(M, 1, j0))
            is42 = (jm1p < j0p) and (entry(M, 1, j0p) >= entry(M, 1, j0))
            tag = '41' if is41 else ('42' if is42 else 'other')
            key = (tag, tuple(x - jm1p for x in mk) if mk != '?' else '?',
                   tuple(x - jm1p for x in admk), j0 - j0p, j0p - jm1p)
            rows[key] = rows.get(key, 0) + 1
            cnt += 1
    print(f"maxlen={maxlen} maxval={maxval}: {cnt} (4) cases")
    print("(tag, markedPM-jm1p, admPM-in-gap-jm1p, j0-j0p, j0p-jm1p) -> count")
    for k, c in sorted(rows.items(), key=lambda x: (x[0][0], -x[1])):
        print("   ", k, c)


if __name__ == '__main__':
    import sys
    ml = int(sys.argv[1]); mv = int(sys.argv[2])
    run(ml, mv)
