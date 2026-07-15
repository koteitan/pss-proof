#!/usr/bin/env python3
"""Finite model audit for §8.6 trailing-principal annihilation.

The marked core is ``D_u(t' + D_v 0)``.  It is embedded in one or two
arbitrary right-spine wrappers, with optional summands before every hole and
at the top level.  For each generated ``T_B`` term this independently checks
both the paper's one-step dichotomy and annihilation within ``v+1`` zero
fundamental-sequence steps under the corrected A23 Buchholz rule.
"""

from itertools import product

from buchholz import D, ZERO, add, bracket, in_TB


def principal(v, body=ZERO):
    return [D(v, body)]


PREFIX = principal(3, principal(1))


def embed(core, layers, top_prefix):
    """Embed a principal core along the last-principal/right spine."""
    out = core
    for head, has_prefix in layers:
        out = principal(head, add(PREFIX if has_prefix else ZERO, out))
    return add(PREFIX if top_prefix else ZERO, out)


def contexts():
    yield (), False
    yield (), True
    for depth in (1, 2):
        for heads in product(range(4), repeat=depth):
            for prefixes in product((False, True), repeat=depth):
                layers = tuple(zip(heads, prefixes))
                yield layers, False
                yield layers, True


T_PRIMES = (
    ZERO,
    principal(0),
    principal(1),
    principal(2),
    principal(1, principal(1)),
    add(principal(2), principal(0)),
)


def audit():
    cases = 0
    step_failures = []
    annihilation_failures = []

    for t_prime in T_PRIMES:
        for u in range(5):
            for v in range(5):
                core = principal(u, add(t_prime, principal(v)))
                deleted = principal(u, t_prime)
                lowered = (
                    principal(u, add(t_prime, principal(v - 1)))
                    if v > 0
                    else None
                )
                for layers, top_prefix in contexts():
                    cases += 1
                    source = embed(core, layers, top_prefix)
                    target = embed(deleted, layers, top_prefix)
                    lower_target = (
                        embed(lowered, layers, top_prefix) if lowered else None
                    )
                    assert in_TB(source) and in_TB(target)

                    current = bracket(source, ZERO)
                    allowed = (target,) if v == 0 else (target, lower_target)
                    if current not in allowed:
                        step_failures.append((t_prime, u, v, layers, top_prefix))

                    found = current == target
                    for _ in range(2, v + 2):
                        if found:
                            break
                        current = bracket(current, ZERO)
                        found = current == target
                    if not found:
                        annihilation_failures.append(
                            (t_prime, u, v, layers, top_prefix)
                        )

    # Regression for the example once misreported under the withdrawn A25:
    # the corrected A23 rule lowers the final D_1 0 first, then deletes it.
    old_example = principal(0, add(principal(1), principal(1)))
    old_step1 = principal(0, add(principal(1), principal(0)))
    old_step2 = principal(0, principal(1))
    assert bracket(old_example, ZERO) == old_step1
    assert bracket(old_step1, ZERO) == old_step2

    return cases, step_failures, annihilation_failures


if __name__ == "__main__":
    total, step_bad, annihilation_bad = audit()
    print("case count:", total)
    print("one-step dichotomy failures:", len(step_bad))
    print("bounded annihilation failures:", len(annihilation_bad))
    print("withdrawn-A25 regression failures: 0")
    if step_bad or annihilation_bad:
        for failure in (step_bad + annihilation_bad)[:10]:
            print(failure)
        raise SystemExit(1)
