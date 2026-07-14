#!/usr/bin/env python3
"""Finite checksum audit for PSS.Trans against trans_model.py.

The matching Lean program is trans_checksum.lean.  It enumerates every
nonempty pair sequence of length at most 3 with both entries below 3 and hashes
Trans, every Mark value in the index range, and conditions (I)--(VI).
"""

from itertools import product
from trans_model import Trans, Mark, flatBT

MOD = 1_000_000_007


def mix(acc, value):
    return (acc * 31 + value) % MOD


def hash_bt(t):
    acc = 1
    for x in flatBT(t):
        if isinstance(x, tuple):
            code = x[1] + 100
        else:
            code = {'Z': 1, '(': 2, ',': 3, ')': 4}[x]
        acc = mix(acc, code)
    return acc


def conds(m):
    j1 = len(m) - 1
    from trans_model import adm, parent, entry
    jp = parent(m, 0, j1)
    if jp is None:
        jp = 0
    c1 = entry(m, 1, j1) == 0 and adm(m, jp)
    c2 = entry(m, 1, j1) == 0 and not adm(m, jp)
    c3 = (entry(m, 1, j1) > 0 and
          entry(m, 1, jp) >= entry(m, 1, j1) and adm(m, jp))
    c4 = (entry(m, 1, j1) > 0 and
          entry(m, 1, jp) >= entry(m, 1, j1) and not adm(m, jp))
    c5 = (entry(m, 1, j1) > 0 and
          entry(m, 1, jp) + 1 == entry(m, 1, j1) and jp + 1 < j1)
    c6 = (entry(m, 1, j1) > 0 and
          entry(m, 1, jp) + 1 == entry(m, 1, j1) and jp + 1 == j1)
    return [c1, c2, c3, c4, c5, c6]


def all_sequences(k=3, max_length=3):
    pairs = list(product(range(k), repeat=2))
    for length in range(1, max_length + 1):
        yield from product(pairs, repeat=length)


def checksum(k=3, max_length=3):
    acc = 0
    count = 0
    for raw in all_sequences(k, max_length):
        m = list(raw)
        count += 1
        acc = mix(acc, hash_bt(Trans(m)))
        for i in range(len(m)):
            acc = mix(acc, hash_bt(Mark(m, i)))
        for c in conds(m):
            acc = mix(acc, int(c))
    return count, acc


if __name__ == "__main__":
    print(*checksum())
