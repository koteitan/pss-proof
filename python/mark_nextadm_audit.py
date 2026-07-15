#!/usr/bin/env python3
"""Independent finite audit for corrected §7.4 A18/A47.

Enumerate every nonempty pair sequence of length at most four with entries
below three.  On reduced inputs, check both the reusable marked-nesting lemma
and its specialization to the unique final ``nextAdm`` parent.  Finally replay
the explicit A18 domain witness and A47 non-reduced counterexample.
"""

from itertools import product

from red_model import Lng, leR, nextAdm
from trans_model import Mark, Pred, adm, flatBT, reduced, scb_decomps


def marked(m, i):
    return adm(m, i) and leR(m, 0, i, Lng(m) - 1)


def common_nest_contexts(m, i, j):
    pred = scb_decomps(Mark(Pred(m), i), flatBT(Mark(Pred(m), j)))
    whole = scb_decomps(Mark(m, i), flatBT(Mark(m, j)))
    return [context for context in pred if context in whole]


def audit(k=3, max_length=4):
    pairs = list(product(range(k), repeat=2))
    all_inputs = 0
    reduced_inputs = 0
    nest_targets = 0
    nextadm_targets = 0
    failures = []

    for length in range(1, max_length + 1):
        for raw in product(pairs, repeat=length):
            m = list(raw)
            all_inputs += 1
            if not reduced(m):
                continue
            reduced_inputs += 1
            last = length - 1

            proper_marked = [i for i in range(last) if marked(m, i)]
            for j in proper_marked:
                for i in proper_marked:
                    if i <= j:
                        nest_targets += 1
                        common = common_nest_contexts(m, i, j)
                        if len(common) != 1:
                            failures.append(("nest", m, i, j, common))

            parents = [i for i in range(length) if nextAdm(m, 0, i, last)]
            if len(parents) == 1:
                j0 = parents[0]
                for i in range(length):
                    if marked(m, i) and leR(m, 0, i, j0):
                        nextadm_targets += 1
                        common = common_nest_contexts(m, i, j0)
                        if len(common) != 1:
                            failures.append(("A47", m, i, j0, common))

            if len(failures) >= 10:
                return (all_inputs, reduced_inputs, nest_targets,
                        nextadm_targets, failures)

    bad18 = [(0, 0), (1, 1), (2, 2), (3, 1)]
    bad18_parents = [i for i in range(4) if nextAdm(bad18, 0, i, 3)]
    if (not reduced(bad18) or bad18_parents != [2]
            or not leR(bad18, 0, 1, 2) or marked(bad18, 1)):
        failures.append(("A18-witness", bad18, bad18_parents))

    bad47 = [(0, 0), (4, 2), (2, 6), (4, 2), (8, 4), (6, 4)]
    bad47_parents = [i for i in range(6) if nextAdm(bad47, 0, i, 5)]
    bad47_common = common_nest_contexts(bad47, 0, 3)
    if (reduced(bad47) or bad47_parents != [3] or not marked(bad47, 0)
            or not leR(bad47, 0, 0, 3) or bad47_common):
        failures.append(("A47-witness", bad47, bad47_parents, bad47_common))

    return all_inputs, reduced_inputs, nest_targets, nextadm_targets, failures


if __name__ == "__main__":
    counts = audit()
    all_inputs, reduced_inputs, nest_targets, nextadm_targets, failures = counts
    print(
        "Mark nesting + nextAdm: "
        f"{all_inputs} inputs, {reduced_inputs} reduced, "
        f"nest {nest_targets} targets, A47 {nextadm_targets} targets, "
        f"{len(failures)} failures"
    )
    for failure in failures:
        print(failure)
    raise SystemExit(bool(failures))
