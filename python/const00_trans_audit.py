#!/usr/bin/env python3
"""Finite model audit for §8.7 ``const00_Trans`` (article 5857).

Enumerate all ``0 <= u <= 8``, ``0 <= j1 <= 8``.  Check the executable §7.3
translation of the constant sequence ``M = ((u,u))_{j=0}^{j1}`` against the
theorem's k-fold ``+_B`` multiple:

    Trans(M) = (D_0 0) x j1       if u = 0
             = (D_u 0) x (j1+1)   if u > 0

Also audit the structural facts the Lean proof relies on:
  * ``M`` is reduced (``Red M = M``),
  * for ``j1 > 0`` ``M`` is multi (neither zeroT nor monoT),
  * ``Pcut M = j1`` for ``j1 > 0`` (so take/drop split off one column).
"""

from red_model import Red, Pcut, monoT, zeroT
from trans_model import Dpt, Trans, ZB


def multBT(a, n):
    return ('T', a[1] * n)


def audit(limit=8):
    checked = 0
    failures = []
    for u in range(limit + 1):
        for j1 in range(limit + 1):
            seq = [(u, u)] * (j1 + 1)

            if Red(seq) != [tuple(p) for p in seq] and Red(seq) != seq:
                failures.append(('Red', u, j1, Red(seq)))
            if j1 > 0:
                if zeroT(seq) or monoT(seq):
                    failures.append(('multi', u, j1))
                if Pcut(seq) != j1:
                    failures.append(('Pcut', u, j1, Pcut(seq)))

            want = multBT(Dpt(u, ZB), j1 if u == 0 else j1 + 1)
            got = Trans(seq)
            if got != want:
                failures.append(('Trans', u, j1, got, want))
            checked += 1
    return checked, failures


if __name__ == "__main__":
    checked, failures = audit()
    print("cases checked:", checked)
    print("failures:", len(failures))
    if failures:
        for failure in failures[:10]:
            print(failure)
        raise SystemExit(1)
