"""Is seg M a (Lng M -1) reduced when (M,a) in Marked, for M in RT cap PT?
(general test, not restricted to (4-1)).
"""
import itertools
from trans_model import Mark
from red_model import (Lng, entry, seg, reduced, monoT, adm, leR,
                       Adm as rAdm, marked)


def run(maxlen):
    n = 0
    bad = 0
    bads = []
    pairs = [(a, b) for a in range(3) for b in range(3)]
    for nn in range(2, maxlen + 1):
        for tup in itertools.product(pairs, repeat=nn - 1):
            M = [(0, 0)] + list(tup)
            if not reduced(M) or not monoT(M):
                continue
            for a in range(Lng(M)):
                if marked(M, a) and a < Lng(M) - 1:
                    S = seg(M, a, Lng(M) - 1)
                    n += 1
                    if not (reduced(S) and monoT(S)):
                        bad += 1
                        if len(bads) < 5:
                            bads.append((M, a, S))
    print(f"maxlen={maxlen}: marked-start-to-end slice reduced&mono: "
          f"{n} cases {bad} bad")
    for b in bads:
        print("  CEX", b)


if __name__ == '__main__':
    import sys
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 5)
