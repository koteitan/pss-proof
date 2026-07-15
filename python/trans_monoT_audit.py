#!/usr/bin/env python3
"""Finite model audit for corrected A16 (`Trans` preserves monoT)."""

from itertools import product

from red_model import P, monoT, zeroT
from trans_model import PB, Trans, reduced


def audit(k=3, max_length=4):
    pairs = list(product(range(k), repeat=2))
    reduced_inputs = 0
    targets = 0
    failures = []
    for length in range(1, max_length + 1):
        for raw in product(pairs, repeat=length):
            m = list(raw)
            if not reduced(m):
                continue
            reduced_inputs += 1
            components = P(m)
            if zeroT(components[0]):
                continue
            targets += 1
            if monoT(m) != (len(PB(Trans(m))) == 1):
                failures.append((m, monoT(m), Trans(m), components))
                if len(failures) == 10:
                    return reduced_inputs, targets, failures

    cex = [(0, 0), (0, 0)]
    if monoT(cex) or len(PB(Trans(cex))) != 1:
        failures.append(("A16-counterexample", cex, Trans(cex)))
    return reduced_inputs, targets, failures


if __name__ == "__main__":
    reduced_inputs, targets, failures = audit()
    print(
        f"Trans/monoT A16: {reduced_inputs} reduced inputs, "
        f"{targets} corrected targets, {len(failures)} failures"
    )
    for failure in failures:
        print(failure)
    raise SystemExit(bool(failures))
