#!/usr/bin/env python3
"""Finite model audit for §7.3 ``Mark_rightmost1`` (correction A17).

Enumerate every nonempty reduced pair sequence of length at most four whose
entries are below three.  Independently check the final-column formula, the
corrected iff on every marked column, its strict-tail lemma, and the stronger
marked-component nesting lemma used by the Lean proof.
"""

from itertools import product

from red_model import Lng, entry, le0, zeroT
from trans_model import Dpt, Mark, ZB, adm, flatBT, reduced, scb_decomps


def marked(m, i):
    return adm(m, i) and le0(m, i, Lng(m) - 1)


def audit(k=3, max_length=4):
    pairs = list(product(range(k), repeat=2))
    reduced_inputs = 0
    marked_targets = 0
    nesting_targets = 0
    failures = []

    for length in range(1, max_length + 1):
        for raw in product(pairs, repeat=length):
            m = list(raw)
            if not reduced(m):
                continue
            reduced_inputs += 1
            last = length - 1
            marks = [i for i in range(length) if marked(m, i)]

            if not zeroT(m):
                expected_last = Dpt(entry(m, 1, last), ZB)
                if Mark(m, last) != expected_last:
                    failures.append(("forward", m, last, Mark(m, last), expected_last))

                for i in marks:
                    marked_targets += 1
                    expected = Dpt(entry(m, 1, i), ZB)
                    if (i == last) != (Mark(m, i) == expected):
                        failures.append(("iff", m, i, Mark(m, i), expected))
                    if i < last and Mark(m, i) == expected:
                        failures.append(("tail", m, i, Mark(m, i), expected))

            for a in marks:
                for b in marks:
                    if a > b:
                        continue
                    nesting_targets += 1
                    outer, inner = Mark(m, a), Mark(m, b)
                    if not scb_decomps(outer, flatBT(inner)):
                        failures.append(("nest", m, a, b, outer, inner))

            if len(failures) >= 10:
                return reduced_inputs, marked_targets, nesting_targets, failures

    zero = [(0, 0)]
    original_fails = (
        marked(zero, 0)
        and reduced(zero)
        and Mark(zero, 0) != Dpt(entry(zero, 1, 0), ZB)
    )
    if not original_fails:
        failures.append(("A17-counterexample", zero))

    return reduced_inputs, marked_targets, nesting_targets, failures


if __name__ == "__main__":
    reduced_inputs, marked_targets, nesting_targets, failures = audit()
    print(
        "Mark/rightmost1: "
        f"{reduced_inputs} reduced inputs, "
        f"{marked_targets} marked targets, "
        f"{nesting_targets} nesting targets, "
        f"{len(failures)} failures"
    )
    for failure in failures:
        print(failure)
    raise SystemExit(bool(failures))
