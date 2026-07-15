#!/usr/bin/env python3
"""Finite model audit for §8.1 ``Pred_diagSeq_Trans``.

Enumerate every theorem branch with ``0 <= u < v <= 8`` and compare the
executable §7.3 translation model with the four closed Buchholz terms stated
by the Lean theorem.
"""

from trans_model import Dpt, Trans, ZB, addBT


def diag_seq(u, v):
    return [(x, x) for x in range(u, v + 1)]


def audit(limit=8):
    checked = [0, 0, 0, 0]
    bad = []

    for u in range(limit + 1):
        for v in range(u + 1, limit + 1):
            prefix = diag_seq(u, v)

            # wp = v + 1, u < w <= v
            for w in range(u + 1, v + 1):
                got = Trans(prefix + [(v + 1, w)])
                want = Dpt(u, Dpt(v, Dpt(w, ZB)))
                checked[0] += 1
                if got != want:
                    bad.append((1, u, v, v + 1, w, got, want))

            # u < wp <= v, w = wp
            for wp in range(u + 1, v + 1):
                got = Trans(prefix + [(wp, wp)])
                want = Dpt(u, addBT(Dpt(v, ZB), Dpt(wp, ZB)))
                checked[1] += 1
                if got != want:
                    bad.append((2, u, v, wp, wp, got, want))

            # u + 1 < wp <= v, w < wp
            for wp in range(u + 2, v + 1):
                for w in range(wp):
                    got = Trans(prefix + [(wp, w)])
                    want = Dpt(
                        u,
                        addBT(
                            Dpt(v, ZB),
                            Dpt(wp - 1, addBT(Dpt(v, ZB), Dpt(w, ZB))),
                        ),
                    )
                    checked[2] += 1
                    if got != want:
                        bad.append((3, u, v, wp, w, got, want))

            # wp = u + 1, w < wp
            for w in range(u + 1):
                got = Trans(prefix + [(u + 1, w)])
                want = Dpt(u, addBT(Dpt(v, ZB), Dpt(w, ZB)))
                checked[3] += 1
                if got != want:
                    bad.append((4, u, v, u + 1, w, got, want))

    return checked, bad


if __name__ == "__main__":
    counts, failures = audit()
    print("case counts:", *counts, "total:", sum(counts))
    print("failures:", len(failures))
    if failures:
        for failure in failures[:10]:
            print(failure)
        raise SystemExit(1)
