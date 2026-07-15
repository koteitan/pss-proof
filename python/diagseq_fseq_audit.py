#!/usr/bin/env python3
"""Finite model audit for §8.6 ``diagSeq_Trans_fseq``.

Enumerate ``0 <= u <= 4``, ``2 <= j1 <= 6`` and ``1 <= n <= 4``.
Independently check the ``oper``/``runSeq`` bridge, reducedness of the expanded
run, and its executable §7.3 translation against ``D_u(D_(u+j1-1)^n 0)``.
"""

from red_model import Red, diagSeq, oper
from trans_model import Dpt, Trans, ZB


def run_seq(u, p, n):
    return [(u + j, min(u + j, p)) for j in range(p - u + n)]


def tower(p, height):
    out = ZB
    for _ in range(height):
        out = Dpt(p, out)
    return out


def audit(u_limit=4, j1_limit=6, n_limit=4):
    bridge_failures = []
    red_failures = []
    trans_failures = []
    cases = 0

    for u in range(u_limit + 1):
        for j1 in range(2, j1_limit + 1):
            p = u + j1 - 1
            source = diagSeq(u, u + j1)
            for n in range(1, n_limit + 1):
                cases += 1
                expanded = oper(source, n)
                canonical = run_seq(u, p, n)
                if expanded != canonical:
                    bridge_failures.append((u, j1, n, expanded, canonical))
                if Red(canonical) != canonical:
                    red_failures.append((u, j1, n, Red(canonical), canonical))
                got = Trans(expanded)
                want = Dpt(u, tower(p, n))
                if got != want:
                    trans_failures.append((u, j1, n, got, want))

    return cases, bridge_failures, red_failures, trans_failures


if __name__ == "__main__":
    total, bridge_bad, red_bad, trans_bad = audit()
    print("case count:", total)
    print("oper/runSeq failures:", len(bridge_bad))
    print("Red failures:", len(red_bad))
    print("Trans failures:", len(trans_bad))
    if bridge_bad or red_bad or trans_bad:
        for failure in (bridge_bad + red_bad + trans_bad)[:10]:
            print(failure)
        raise SystemExit(1)
