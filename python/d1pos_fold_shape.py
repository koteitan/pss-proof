#!/usr/bin/env python3
"""Empirically map the d0pos (i1=1) P-block-fold shape for §6.8 oper_d1pos_seg_P_*.

Context (see pss_mechanized.thy ~12790, the single residual d0pos sorry):
  For standard N with monoT(N), i1 = idx1 N (Lng N-1) = 1, hasParent N 1 (Lng N-1),
  delta = entry N 0 (Lng N-1) - entry N 0 j_2 > 0  (j_2 = parent N 1 (Lng N-1)),
  and M = oper(N, n):
    M = take j_2 N
        @ concat [ map (\\j. (entry N 0 j + k*delta, entry N 1 j)) [j_2 ..< Lng N-1]
                   | k <- [0 ..< n] ]
  Each fundamental-sequence block k occupies [j_2 + k*w, j_2 + (k+1)*w - 1]
  (w = Lng N-1 - j_2); block k's row-0 entries are shifted by +k*delta, row 1 is
  UNSHIFTED.  So blocks have row-0-INCREASING heads (0, delta, 2*delta, ...).

KEY EMPIRICAL FINDINGS (this script):

  THE PARADOX RESOLUTION.  descending(Br) needs the P-component heads of the
  *branch* to be row-0 weakly DECREASING.  delta>0 makes the BLOCK heads
  row-0 INCREASING.  These do not conflict because the d0pos block-fold does
  NOT split into one-P-component-per-block (unlike d0zero's `replicate qb blk`).

  H1 (the central structural fact).  For ANY block-start anchor a = j_2 + q*w
  (q < n) and any b with a < b < Lng M and le0 M a b:
        P (seg M a b) = [seg M a b]                       -- ONE mono component.
  The increasing-head blocks fold into a SINGLE mono component, because the
  row-0 head of each later block is dominated by its own larger entries while
  the row-1 last-node chain keeps the whole span mono.  (0 failures.)

  Consequently the genuine multi-component structure of Br(seg M j0' j1')
  comes ONLY from N's OWN pre-existing branch components (those P-pieces of
  N inside [j_2 .. Lng N-1] that sit to the LEFT of the fold), and the entire
  delta-shifted block-fold is absorbed into the SINGLE LAST mono component.
  That single last component is descending-compatible because it is one element.

  H2 (last component always mono / single).  Recorded: for every le0 slice the
  last P-component is mono-or-singleton, i.e. the fold tail never re-splits.

  J1=-1 form (article 1546).  When w = 1 (j_2 = j_0^N = j_1^N - 1), the whole
  slice tail is the fold row and
        Br (seg M j_2 (Lng M-1)) = [ map (\\k. (entry N 0 j_2 + k*delta,
                                               entry N 1 j_2)) [1 ..< n] ]
  a single component (descending vacuously).  (verified)

  descending(Br(seg M j0' j1')) holds for ALL monoT+le0 slices.
"""
import sys, itertools, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__)))
from red_model import (P, Br, seg, oper, TrMax, FirstNodes, Joints, parent,
                       idx1, monoT, multiT, entry, Lng, is_standard, IncrFirst,
                       funpow, le0, fmt, nextR)

KMAX = int(os.environ.get("KMAX", "6"))
MAXLEN = int(os.environ.get("MAXLEN", "4"))
NMAX = int(os.environ.get("NMAX", "4"))


def gen_standard(maxlen):
    out = []
    for L in range(2, maxlen + 1):
        for vals in itertools.product(range(KMAX + 1), repeat=2 * L):
            M = [(vals[2 * i], vals[2 * i + 1]) for i in range(L)]
            if M[0] != (0, 0):
                continue
            if is_standard(M):
                out.append(M)
    return out


def parent_unique(M, i, j1):
    return sum(1 for j0 in range(Lng(M)) if nextR(M, i, j0, j1)) == 1


def d0pos_witnesses(maxlen):
    out = []
    for N in gen_standard(maxlen):
        j1 = Lng(N) - 1
        if not monoT(N):
            continue
        if idx1(N, j1) != 1:
            continue
        if not parent_unique(N, 1, j1):
            continue
        j_2 = parent(N, 1, j1)
        if entry(N, 0, j1) - entry(N, 0, j_2) <= 0:
            continue
        out.append(N)
    return out


def is_descending_heads(comps):
    h0 = [entry(c, 0, 0) for c in comps]
    h1 = [entry(c, 1, 0) for c in comps]
    for i in range(len(comps) - 1):
        if not (h0[i] > h0[i + 1] or (h0[i] == h0[i + 1] and h1[i] >= h1[i + 1])):
            return False
    return True


def run():
    ws = d0pos_witnesses(MAXLEN)
    print(f"# standard d0pos witnesses (KMAX={KMAX}, len<={MAXLEN}): {len(ws)}")

    h1_tot = h1_fail = 0
    h1_fail_ex = []
    d_tot = d_fail = 0
    d_fail_ex = []
    last_tot = last_bad = 0
    j1m1_tot = j1m1_fail = 0
    j1m1_fail_ex = []

    for N in ws:
        j1N = Lng(N) - 1
        j_2 = parent(N, 1, j1N)
        w = j1N - j_2
        delta = entry(N, 0, j1N) - entry(N, 0, j_2)
        for n in range(2, NMAX + 1):
            M = oper(N, n)
            LM = Lng(M)

            # H1: block-start anchor a = j_2 + q*w, le0 -> single mono component
            for q in range(n):
                a = j_2 + q * w
                if a >= LM:
                    continue
                for b in range(a + 1, LM):
                    if not le0(M, a, b):
                        continue
                    Mp = seg(M, a, b)
                    h1_tot += 1
                    if P(Mp) != [Mp]:
                        h1_fail += 1
                        if len(h1_fail_ex) < 5:
                            h1_fail_ex.append((fmt(N), n, q, a, b, fmt(Mp),
                                               [fmt(c) for c in P(Mp)]))

            # descending(Br) + last-comp over all monoT+le0 slices
            for j0p in range(LM - 1):
                for j1p in range(j0p + 1, LM):
                    Mp = seg(M, j0p, j1p)
                    if not (monoT(Mp) and le0(M, j0p, j1p)):
                        continue
                    Brm = Br(Mp)
                    d_tot += 1
                    if not is_descending_heads(Brm):
                        d_fail += 1
                        if len(d_fail_ex) < 5:
                            d_fail_ex.append((fmt(N), n, j0p, j1p,
                                              [fmt(c) for c in Brm]))
                    Pc = P(Mp)
                    last_tot += 1
                    if not (monoT(Pc[-1]) or Lng(Pc[-1]) == 1):
                        last_bad += 1

            # J1=-1 (w=1) fold-row form
            if w == 1:
                Mp = seg(M, j_2, LM - 1)
                expected = [[(entry(N, 0, j_2) + k * delta, entry(N, 1, j_2))
                             for k in range(1, n)]]
                j1m1_tot += 1
                if Br(Mp) != expected:
                    j1m1_fail += 1
                    if len(j1m1_fail_ex) < 5:
                        j1m1_fail_ex.append((fmt(N), n, fmt(Mp),
                                             [fmt(c) for c in Br(Mp)],
                                             [fmt(c) for c in expected]))

    print(f"H1 [block-start a, le0 M a b => P(seg M a b)=[seg M a b]]: "
          f"{h1_tot} witnesses, {h1_fail} failures")
    for e in h1_fail_ex:
        print("   H1 FAIL:", e)
    print(f"descending(Br(seg M j0' j1')) over monoT+le0 slices: "
          f"{d_tot} witnesses, {d_fail} failures")
    for e in d_fail_ex:
        print("   DESC FAIL:", e)
    print(f"H2 [last P-component mono/single]: {last_tot} witnesses, "
          f"{last_bad} failures")
    print(f"J1=-1 fold-row form (w=1): {j1m1_tot} witnesses, {j1m1_fail} failures")
    for e in j1m1_fail_ex:
        print("   J1=-1 FAIL:", e)


if __name__ == "__main__":
    run()
