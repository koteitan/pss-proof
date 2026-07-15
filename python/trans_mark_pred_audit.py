#!/usr/bin/env python3
"""Finite independent audit for corrected §7.4 A45/A46.

Enumerate every nonempty pair sequence of length at most four with entries
below three.  On reduced inputs, check that the two scb problems in
``Trans_Mark_Pred`` have exactly one common context for every proper marked
column, and specialize the same check to every unique final ``nextAdm``
parent.  Also verify that A45/A46's shared non-reduced witness has disjoint
context sets.
"""

from itertools import product

from red_model import Lng, leR, nextAdm
from trans_model import Mark, Pred, Trans, adm, flatBT, reduced, scb_decomps


def marked(m, i):
    return adm(m, i) and leR(m, 0, i, Lng(m) - 1)


def common_contexts(m, i):
    pred = scb_decomps(Trans(Pred(m)), flatBT(Mark(Pred(m), i)))
    whole = scb_decomps(Trans(m), flatBT(Mark(m, i)))
    return [context for context in pred if context in whole]


def audit(k=3, max_length=4):
    pairs = list(product(range(k), repeat=2))
    all_inputs = 0
    reduced_inputs = 0
    a46_targets = 0
    a45_targets = 0
    failures = []

    for length in range(1, max_length + 1):
        for raw in product(pairs, repeat=length):
            m = list(raw)
            all_inputs += 1
            if not reduced(m):
                continue
            reduced_inputs += 1
            last = length - 1

            for i in range(last):
                if not marked(m, i):
                    continue
                a46_targets += 1
                common = common_contexts(m, i)
                if len(common) != 1:
                    failures.append(("A46", m, i, common))

            parents = [i for i in range(length) if nextAdm(m, 0, i, last)]
            if len(parents) == 1:
                a45_targets += 1
                i = parents[0]
                common = common_contexts(m, i)
                if len(common) != 1:
                    failures.append(("A45", m, i, common))

            if len(failures) >= 10:
                return all_inputs, reduced_inputs, a46_targets, a45_targets, failures

    bad = [(0, 0), (0, 1), (1, 2), (1, 0)]
    bad_parents = [i for i in range(len(bad)) if nextAdm(bad, 0, i, 3)]
    if reduced(bad) or bad_parents != [1] or common_contexts(bad, 1):
        failures.append(("A45/A46-counterexample", bad, bad_parents,
                         common_contexts(bad, 1)))

    return all_inputs, reduced_inputs, a46_targets, a45_targets, failures


if __name__ == "__main__":
    counts = audit()
    all_inputs, reduced_inputs, a46_targets, a45_targets, failures = counts
    print(
        "Trans/Mark/Pred + nextAdm: "
        f"{all_inputs} inputs, {reduced_inputs} reduced, "
        f"A46 {a46_targets} targets, A45 {a45_targets} targets, "
        f"{len(failures)} failures"
    )
    for failure in failures:
        print(failure)
    raise SystemExit(bool(failures))
