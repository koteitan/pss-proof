#!/usr/bin/env python3
"""Finite model audit for §7.3 ``Pred_Trans_descend``.

Enumerate every nonempty pair sequence of length at most four whose entries
are below three.  For each sequence with at least two columns, independently
evaluate the executable Python model and check

    Trans(Pred M) <_B Trans(M).

This covers both reduced and non-reduced inputs and therefore also exercises
the two-step ``Red`` transport used by the Lean theorem.
"""

from itertools import product

from trans_model import Pred, Trans


def less_bp(p, q):
    _, u, a = p
    _, v, b = q
    return u < v or (u == v and less_bt(a, b))


def less_bt(a, b):
    aps, bps = a[1], b[1]
    for p, q in zip(aps, bps):
        if p == q:
            continue
        return less_bp(p, q)
    return len(aps) < len(bps)


def audit(k=3, max_length=4):
    pairs = list(product(range(k), repeat=2))
    tested = 0
    failures = []
    for length in range(2, max_length + 1):
        for raw in product(pairs, repeat=length):
            m = list(raw)
            tested += 1
            lhs = Trans(Pred(m))
            rhs = Trans(m)
            if not less_bt(lhs, rhs):
                failures.append((m, lhs, rhs))
                if len(failures) == 10:
                    return tested, failures
    return tested, failures


if __name__ == "__main__":
    tested, failures = audit()
    print(f"Pred/Trans descent: {tested} cases, {len(failures)} failures")
    for failure in failures:
        print(failure)
    raise SystemExit(bool(failures))
