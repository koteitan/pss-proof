#!/usr/bin/env python3
"""Finite model audit for §8.6 ``const2nd_Trans``.

Enumerate all ``0 <= m,u,j1 <= 4``.  Independently check both the normal-form
bridge ``Red ((m+j,u)) = ((u+j,u))`` and the executable §7.3 translation
against the iterated Buchholz principal term from the theorem.
"""

from red_model import Red
from trans_model import Dpt, Trans, ZB


def const2nd_seq(m, u, j1):
    return [(m + j, u) for j in range(j1 + 1)]


def tower(u, height):
    out = ZB
    for _ in range(height):
        out = Dpt(u, out)
    return out


def audit(limit=4):
    zero_cases = 0
    tower_cases = 0
    red_failures = []
    trans_failures = []

    for m in range(limit + 1):
        for u in range(limit + 1):
            for j1 in range(limit + 1):
                seq = const2nd_seq(m, u, j1)
                canonical = const2nd_seq(u, u, j1)
                reduced = Red(seq)
                if reduced != canonical:
                    red_failures.append((m, u, j1, reduced, canonical))

                got = Trans(seq)
                if j1 == 0 and u == 0:
                    zero_cases += 1
                    want = ZB
                else:
                    tower_cases += 1
                    want = tower(u, j1 + 1)
                if got != want:
                    trans_failures.append((m, u, j1, got, want))

    return zero_cases, tower_cases, red_failures, trans_failures


if __name__ == "__main__":
    zeros, towers, red_bad, trans_bad = audit()
    print("case counts:", zeros, towers, "total:", zeros + towers)
    print("Red failures:", len(red_bad))
    print("Trans failures:", len(trans_bad))
    if red_bad or trans_bad:
        for failure in (red_bad + trans_bad)[:10]:
            print(failure)
        raise SystemExit(1)
