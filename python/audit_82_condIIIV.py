#!/usr/bin/env python3
"""Audit for lean/8/8.2-condIIIV-terminal-slice-Trans.lean.

Three questions, all about NON-VACUITY / FAITHFULNESS of the Lean port:

(1) LastStep faithfulness (correction A9).  The Lean port totalises the
    article's `min {J | ...}` as `(List.range n).find? P |>.getD J1`.
    Isabelle keeps `Min S` (junk when S = {}).  Check the two agree on every
    host where S != {} -- and record whether S = {} ever happens at all on a
    genuine DT_PS host with the guard (footnote [61] claims it cannot).

(2) The Lean theorem `condIIIV_terminal_slice_Trans_modVE` has hypotheses
    DTPS M, Br M != [], 0 < j0' < TrMax M, guard, VE2, VE3, VE4, t2 != 0B.
    Check this bundle is SATISFIABLE (else the theorem is vacuous).

(3) `LastStep_lt_Lng_Br` is claimed in the Lean port to hold UNCONDITIONALLY
    (Isabelle's vgx_LastStep_lt_Lng_Br needs `gt` + `fin`).  Check
    LastStep M < Lng(Br M) on every host with Br M != [], guard or not.

Pools: brute-force small hosts AND a real standard-form pool (diagSeq closed
under oper), per lean/memo.md par.3 ("random pair sequences are almost never
reduced -- build a genuine standard pool via diagSeq closed under oper").

Usage:  python3 python/audit_82_condIIIV.py [Lmax] [vmax] [budget_seconds]
"""
import sys, os, itertools, time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))
from red_model import (Lng, entry, monoT, seg, Br, FirstNodes, Joints, Red,
                       TrMax, diagSeq, oper, is_standard)
from trans_model import Dpt, ZB, bpHeadT, addBT, Trans


def pr(*a):
    print(*a, flush=True)


def is_reduced(M):
    return Red(list(M)) == list(M)


def descending(bs):
    for J0 in range(len(bs)):
        for J1 in range(J0, len(bs)):
            a0, b0 = bs[J0][0]
            a1, b1 = bs[J1][0]
            if not (a0 >= a1 and (a0 != a1 or b0 >= b1)):
                return False
    return True


def in_DT_PS(M):
    return is_reduced(M) and monoT(M) and descending(Br(M))


def laststep_set(M):
    """The A9 (bounded) comprehension S, as a sorted list."""
    b = Br(M)
    J1 = len(b) - 1
    return [J for J in range(len(b))
            if entry(b[J1], 0, 0) == entry(b[J], 0, 0)
            and entry(b[J], 1, 0) < entry(b[J], 0, 0)]


def LastStep_isabelle(M):
    """isabelle/pss_defs.thy:533.  Returns None where Isabelle's Min is junk."""
    b = Br(M)
    if not b:
        return 0
    J1 = len(b) - 1
    if entry(b[J1], 0, 0) == entry(b[J1], 1, 0):
        return J1
    S = laststep_set(M)
    if not S:
        return None          # Min {} = junk in Isabelle
    return min(S)


def LastStep_lean(M):
    """The Lean port: find? over List.range, default J1 (total)."""
    b = Br(M)
    if len(b) == 0:
        return 0
    J1 = len(b) - 1
    if entry(b[J1], 0, 0) == entry(b[J1], 1, 0):
        return J1
    S = laststep_set(M)
    return S[0] if S else J1   # find? returns the LEAST; getD J1 on none


def hyps_geometric(M):
    """DTPS M, Br M != [], 0 < j0' < TrMax M, guard."""
    if not in_DT_PS(M):
        return None
    b = Br(M)
    if not b:
        return None
    J1 = len(b) - 1
    j0p = Joints(M)[J1]
    j1p = FirstNodes(M)[J1]
    if j0p is None:
        return None
    if not (0 < j0p < TrMax(M)):
        return None
    if not (entry(M, 0, j1p) > entry(M, 1, j1p)):
        return None
    return (j0p, j1p, J1)


def check_host(M):
    """Full hypothesis bundle of the Lean theorem + its conclusion."""
    g = hyps_geometric(M)
    if g is None:
        return None
    j0p, j1p, J1 = g
    j1 = Lng(M) - 1
    J0 = LastStep_lean(M)
    m1 = FirstNodes(M)[J0] - 1
    N = seg(M, 0, m1)
    Np = seg(M, j0p, m1)
    Mp = seg(M, j0p, j1)
    TN, TNp, TMp, TM = Trans(N), Trans(Np), Trans(Mp), Trans(M)
    hN, hNp, hMp, hM = bpHeadT(TN), bpHeadT(TNp), bpHeadT(TMp), bpHeadT(TM)

    # VE2
    if hNp != hN:
        return ('VE2-fail', M)
    # VE3 : bpHeadT(Trans M') = bpHeadT(Trans N) +B t2, t2 != 0
    if hMp[1][:len(hN[1])] != hN[1]:
        return ('VE3-noprefix', M)
    t2 = ('T', hMp[1][len(hN[1]):])
    if t2 == ZB:
        return ('VE3-t2zero', M)
    # VE4
    if hM != addBT(hN, Dpt(entry(M, 1, j0p), hMp)):
        return ('VE4-fail', M)
    # conclusion, with t1 := bpHeadT (Trans N)
    t1 = hN
    if TN != Dpt(entry(M, 1, 0), t1):
        return ('c1-fail', M)
    if TNp != Dpt(entry(M, 1, j0p), t1):
        return ('c2-fail', M)
    if TMp != Dpt(entry(M, 1, j0p), addBT(t1, t2)):
        return ('c3-fail', M)
    if TM != Dpt(entry(M, 1, 0),
                 addBT(t1, Dpt(entry(M, 1, j0p), addBT(t1, t2)))):
        return ('c4-fail', M)
    return ('ok', M, t1, t2)


def standard_pool(depth=4, nmax=3):
    """A real standard-form pool: diagSeq closed under oper (memo par.3)."""
    seeds = [diagSeq(0, k) for k in range(1, 5)]
    pool, frontier = [], list(seeds)
    seen = set()
    for _ in range(depth):
        nxt = []
        for M in frontier:
            key = tuple(map(tuple, M))
            if key in seen:
                continue
            seen.add(key)
            pool.append(M)
            for n in range(nmax + 1):
                try:
                    nxt.append(oper(list(M), n))
                except Exception:
                    pass
        frontier = nxt
    return pool


def main():
    Lmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    vmax = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    budget = float(sys.argv[3]) if len(sys.argv) > 3 else 1e9
    t0 = time.time()

    cells = [(a, b) for a in range(vmax) for b in range(vmax)]
    pool = standard_pool()
    hosts_std = [M for M in pool if Lng(M) >= 3]

    def all_hosts():
        """Lazy: brute-force hosts then the standard pool (avoids OOM)."""
        for L in range(3, Lmax + 1):
            for tup in itertools.product(cells, repeat=L - 1):
                yield [(0, 0)] + list(tup)
        for M in hosts_std:
            yield M

    n_bf = sum(len(cells) ** (L - 1) for L in range(3, Lmax + 1))
    pr(f"[pool] brute-force hosts={n_bf} (L<={Lmax}, vmax={vmax}); "
       f"standard pool={len(hosts_std)} "
       f"(is_standard: {sum(1 for M in hosts_std if is_standard(M))})")

    # (1) LastStep faithfulness + (3) range, over ALL hosts with Br != []
    n_br, n_agree, n_emptyS, n_emptyS_guard, n_range_bad = 0, 0, 0, 0, 0
    n_seen1 = 0
    for M in all_hosts():
        if time.time() - t0 > budget * 0.5:
            pr(f"[budget] (1)/(3) stopped after {n_seen1} hosts")
            break
        n_seen1 += 1
        b = Br(M)
        if not b:
            continue
        n_br += 1
        li = LastStep_isabelle(M)
        ll = LastStep_lean(M)
        if li is None:
            n_emptyS += 1
            if hyps_geometric(M) is not None:
                n_emptyS_guard += 1     # would refute footnote [61]
        elif li == ll:
            n_agree += 1
        else:
            pr(f"[!!] LastStep MISMATCH {M}: isabelle={li} lean={ll}")
        if not (ll < len(b)):
            n_range_bad += 1
            pr(f"[!!] LastStep out of range {M}: {ll} >= {len(b)}")
    pr(f"(1) LastStep: hosts with Br!=[] : {n_br}")
    pr(f"    agree with Isabelle Min      : {n_agree}")
    pr(f"    S empty (Isabelle Min junk)  : {n_emptyS} "
       f"(of which satisfy the theorem's geometric hyps: {n_emptyS_guard})")
    pr(f"(3) LastStep < Lng(Br M) violations (unconditional claim): {n_range_bad}")

    # (2) non-vacuity + conclusion
    ok = fail = 0
    fails = []
    examples = []
    n_seen2 = 0
    for M in all_hosts():
        if time.time() - t0 > budget:
            pr(f"[budget] (2) stopped after {n_seen2} hosts")
            break
        n_seen2 += 1
        r = check_host(M)
        if r is None:
            continue
        if r[0] == 'ok':
            ok += 1
            if len(examples) < 3:
                examples.append(r)
        else:
            fail += 1
            if len(fails) < 6:
                fails.append(r)
    pr(f"(2) hosts satisfying DTPS+Br!=[]+0<j0'<TrMax+guard : {ok + fail}")
    pr(f"    VE2/VE3/VE4/t2!=0 AND conclusion hold          : {ok}")
    pr(f"    failures                                       : {fail}")
    for f in fails:
        pr(f"    [!!] {f[0]} : {f[1]}")
    for e in examples:
        pr(f"    [witness] M={e[1]}")
        pr(f"              t1={e[2]}")
        pr(f"              t2={e[3]}")
    verdict = ("NON-VACUOUS, no counterexample"
               if ok > 0 and fail == 0 and n_range_bad == 0
               else "PROBLEM -- inspect above")
    pr(f"[verdict] {verdict}")


if __name__ == '__main__':
    main()
