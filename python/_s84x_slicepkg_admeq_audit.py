#!/usr/bin/env python3
"""Audit for the §8.4 slicepkg / admeq-condIV gate question.

Investigate whether the ∃-witness form of `Exch84_condIIIIV_slicepkg`
(lean/8/8.4-exch84-producer.lean; NO `ltJ` hypothesis) is satisfiable on the
condIV hosts of the ST_PS pool, given that Isabelle `oi5_IIIIV_pkg` needs
`ltJ : s84x_jm3 M < transJm1 M`, which FAILS on admeq-condIV
(`Adm M (s84x_jm2 M) = transJm1 M`, i.e. `s84x_jm3 M = transJm1 M`).

Checks on the ST_PS pool (diagSeq seeds closed under M[n]):
  (A) VACUITY: among condIV hosts with hasParent M 1 j1, how many are
      non-admeq (jm3 < jm1, where oi5 applies) vs admeq (jm3 = jm1, where
      oi5 does NOT apply and the article's c4cx2 route is used)?
  (B) d3 IDENTITY on admeq-condIV: the forced slicepkg witness seed is
      A0 = transT2 M (mnform pins it), and Isabelle `cpx_d3_condIV` gives
      Trans(Pred(s84x_Np M)) = D_{M1,jm2}(transT2 M), i.e.
      bpHeadT(Trans(Pred(s84x_Np M))) == transT2 M  — the SAME A0-shape that
      oi5 produces via s84x_Np.  Confirm it holds.

Run:  python3 python/_s84x_slicepkg_admeq_audit.py
"""
import signal
import sys

import red_model as rm
from red_model import diagSeq, oper, Lng, entry, parent, hasParent, reduced, monoT
from trans_model import Trans, Mark, bpHeadT, bpHeadV, Pred, Adm, condI, condIII, condV, condVI


def condIV(M):
    j1 = Lng(M) - 1
    jp = parent(M, 0, j1)
    return (entry(M, 1, j1) > 0 and entry(M, 1, jp) >= entry(M, 1, j1)
            and not rm_adm(M, jp))


def rm_adm(M, j):
    # adm M j  (trans_model.adm): j not made non-admissible by a row-1 run
    from trans_model import adm as _adm
    return _adm(M, j)


class _TO(Exception):
    pass


def _alarm(signum, frame):
    raise _TO()


def guarded(fn, *a, timeout=5):
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(timeout)
    try:
        return fn(*a)
    finally:
        signal.alarm(0)


def build_pool(seeds, depth, ns):
    seen = set()
    pool = []
    frontier = list(seeds)
    for M in frontier:
        key = tuple(M)
        if key not in seen:
            seen.add(key)
            pool.append(M)
    for _ in range(depth):
        nxt = []
        for M in list(pool):
            for n in ns:
                try:
                    Mp = guarded(oper, M, n, timeout=3)
                except _TO:
                    continue
                if not Mp:
                    continue
                key = tuple(Mp)
                if key not in seen and Lng(Mp) <= 22:
                    seen.add(key)
                    pool.append(Mp)
                    nxt.append(Mp)
        if not nxt:
            break
    return pool


def main():
    seeds = []
    for u in range(0, 3):
        for v in range(u, u + 8):
            seeds.append(diagSeq(u, v))
    pool = build_pool(seeds, depth=5, ns=[1, 2, 3, 4])
    # keep genuine ST_PS reduced+mono hosts with j1 > 1 and hasParent M 1 j1
    hosts = []
    for M in pool:
        if Lng(M) < 3:
            continue
        j1 = Lng(M) - 1
        if not (reduced(M) and monoT(M)):
            continue
        if not hasParent(M, 1, j1):
            continue
        hosts.append(M)

    n_condIV = 0
    n_admeq = 0
    n_nonadmeq = 0
    d3_ok = 0
    d3_bad = 0
    nonadmeq_examples = []
    d3_bad_examples = []
    skipped = 0

    for M in hosts:
        j1 = Lng(M) - 1
        try:
            cIV = guarded(condIV, M, timeout=3)
        except _TO:
            skipped += 1
            continue
        if not cIV:
            continue
        n_condIV += 1
        jm2 = parent(M, 1, j1)
        j0 = parent(M, 0, j1)
        jm1 = Adm(M, j0)          # transJm1 M
        jm3 = Adm(M, jm2)         # s84x_jm3 M
        admeq = (jm3 == jm1)
        if admeq:
            n_admeq += 1
        else:
            n_nonadmeq += 1
            if len(nonadmeq_examples) < 5:
                nonadmeq_examples.append((M, jm3, jm1))
            continue  # d3 check only meaningful on admeq
        # (B) d3 identity on admeq-condIV
        try:
            predM = Pred(M)
            c1 = guarded(Mark, predM, jm1, timeout=6)         # transC1 M
            t2 = bpHeadT(c1)                                   # transT2 M
            Np = rm.seg(M, jm2, j1)                            # s84x_Np M
            tPredNp = guarded(Trans, Pred(Np), timeout=6)      # Trans(Pred(s84x_Np M))
            head = bpHeadT(tPredNp)
        except _TO:
            skipped += 1
            continue
        except Exception:
            skipped += 1
            continue
        if head == t2:
            d3_ok += 1
        else:
            d3_bad += 1
            if len(d3_bad_examples) < 5:
                d3_bad_examples.append((M, head, t2))

    print("=" * 68)
    print("§8.4 slicepkg / admeq-condIV audit")
    print("=" * 68)
    print(f"pool size (oper-closed)          : {len(pool)}")
    print(f"ST_PS hosts (reduced&mono, j1>1, hasParent M 1 j1): {len(hosts)}")
    print(f"condIV hosts                     : {n_condIV}")
    print(f"  admeq-condIV (jm3 = jm1)       : {n_admeq}   [oi5 does NOT apply; ltJ fails]")
    print(f"  non-admeq-condIV (jm3 < jm1)   : {n_nonadmeq} [oi5 applies]")
    print(f"skipped (timeout/size)           : {skipped}")
    print("-" * 68)
    print("(A) VACUITY of non-admeq-condIV on ST_PS:")
    if n_nonadmeq == 0:
        print("    NO non-admeq-condIV host found  => on ST_PS, condIV == admeq-condIV")
        print("    => slicepkg MUST cover admeq-condIV (oi5 route unavailable there).")
    else:
        print("    non-admeq-condIV hosts EXIST; examples (M, jm3, jm1):")
        for M, a, b in nonadmeq_examples:
            print(f"      {M}  jm3={a} jm1={b}")
    print("-" * 68)
    print("(B) d3 identity on admeq-condIV  bpHeadT(Trans(Pred(s84x_Np M))) == transT2 M")
    print(f"    (= forced slicepkg witness A0 = transT2 M matches oi5 A0-shape):")
    print(f"    holds {d3_ok}/{d3_ok + d3_bad}")
    if d3_bad_examples:
        print("    COUNTEREXAMPLES:")
        for M, h, t in d3_bad_examples:
            print(f"      {M}  head={h}  transT2={t}")
    print("=" * 68)


if __name__ == "__main__":
    main()
