#!/usr/bin/env python3
"""Finite-model audit for §7.4 ``Adm_nextAdm``.

Enumerate every nonempty pair sequence of length at most four with entries
below three.  For both rows, whenever the final column has a unique parent,
check that admissibilizing that parent gives its admissible parent.
"""

from itertools import product

from red_model import Adm, hasParent, nextAdm, parent


def audit(k=3, max_length=4):
    pairs = list(product(range(k), repeat=2))
    inputs = 0
    targets = 0
    row_targets = [0, 0]
    failures = []

    for length in range(1, max_length + 1):
        for raw in product(pairs, repeat=length):
            m = list(raw)
            inputs += 1
            last = length - 1
            for i in range(2):
                if not hasParent(m, i, last):
                    continue
                targets += 1
                row_targets[i] += 1
                p = parent(m, i, last)
                a = Adm(m, p)
                if not nextAdm(m, i, a, last):
                    failures.append((m, i, p, a, last))
                    if len(failures) == 10:
                        return inputs, targets, row_targets, failures

    return inputs, targets, row_targets, failures


if __name__ == "__main__":
    inputs, targets, row_targets, failures = audit()
    print(
        f"Adm/nextAdm: {inputs} inputs, {targets} parent targets "
        f"(row0={row_targets[0]}, row1={row_targets[1]}), "
        f"{len(failures)} failures"
    )
    for failure in failures:
        print(failure)
    raise SystemExit(bool(failures))
