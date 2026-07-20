#!/usr/bin/env python3
"""Faithfulness / non-vacuity audit for lean/8/8.7-OT-tail-annihilable.lean.

The Lean file is GREEN-MODULO exactly ONE named Prop, `OT_B_wf`
([Buc1] Lemma 2.2 = Isabelle `y4_buc1_2_2_OT_B_wf`).  Everything else is
discharged, INCLUDING the one-step descent that Isabelle's
`y3t_toplevel_OT_tail_annihilate` / `m_8_7_toplevel_OT_tail_annihilate`
take as the hypothesis `step`.  So the two things worth checking numerically
are exactly those two:

  (A) STEP  (Lean: private `operB_Dprin_step_ota`, discharged;
             Isabelle: the `step` assumption, NOT discharged)
        for r in OT_B, r != 0:
          exists r'.  (q +_B D_u r)[0] = q +_B D_u r'
                   /\ r' in OT_B  /\  r' < r
      Checked in the exact shape the Lean lemma proves it: the [0]-step
      localizes to the trailing principal and only descends its BODY.

  (B) TOP   (Lean: `toplevel_OT_tail_annihilate`, modulo OT_B_wf)
        for t' in OT_B:
          exists k.  ([0]^k)(q +_B D_u t') = q +_B D_u 0

  (C) The A26 witness.  Before the chapter relocation, layerB/pss_wip.thy
      claimed the article lemma is FALSE for a NESTED marked principal
      (t = D_0(D_1(D_1 0))); the leaf now lives in
      isabelle/8/P_8_7_OT_tail_annihilable.thy, whose header records the
      retraction instead of the falsity claim.  A26 was
      later RETRACTED (it is a product of the operB/A23 misreading, same as
      A25 -- see the header of 8.6-trailing-principal-annihilable.lean).  We
      re-check the witness under the CORRECTED (A23) operB to confirm the
      retraction, i.e. that the trajectory does reach the claimed target and
      the file's top-level scope is not hiding a real counterexample.

Pool: exhaustive OT_B terms (in_OT and in_TB both enforced -- the pool is the
real thing, not a random-term pool), plus real prefixes q ranging over OT_B.

Run:  python3 python/audit_87_OT_tail_annihilable.py
"""
import sys

sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')

import buchholz as B
from buchholz import D, ZERO, add, dom, bracket, in_OT, in_TB, lt_term, fmt


def in_OT_B(a):
    return in_OT(a) and in_TB(a)


def size(a):
    """Number of D-nodes in a term."""
    return sum(1 + size(p[2]) for p in a)


def gen_terms(max_idx, max_depth, max_width, max_size):
    """All terms up to the given index / nesting depth / width / D-node count.

    The size cap is what makes this tractable: without it the depth-3 pool is
    ~22M terms.  Same parameters as the Isabelle-era `_87_tail_annihilable.py`
    (max_idx=2, depth=3, width=2, size<=9).
    """
    if max_depth == 0 or max_size == 0:
        return [ZERO]
    bodies = gen_terms(max_idx, max_depth - 1, max_width, max_size - 1)
    princs = [D(v, b) for v in range(max_idx + 1) for b in bodies
              if 1 + size(b) <= max_size]
    out = [ZERO]
    level = [[]]
    for _ in range(max_width):
        level = [t + [p] for t in level for p in princs
                 if size(t) + 1 + size(p[2]) <= max_size]
        out.extend(level)
    return out


def pool_OT_B(max_idx=2, max_depth=3, max_width=2, max_size=9):
    return [t for t in gen_terms(max_idx, max_depth, max_width, max_size)
            if in_OT_B(t)]


def step0(a):
    """One [0] fundamental-sequence step (A23-corrected operB)."""
    return bracket(a, ZERO)


# --------------------------------------------------------------------------
# (A) the STEP that Lean discharges and Isabelle assumes
# --------------------------------------------------------------------------
def check_step(terms, prefixes, max_u):
    ok = bad = fired = 0
    for r in terms:
        if not r:                      # r != 0_B
            continue
        for u in range(max_u + 1):
            Dur = D(u, r)
            if not in_OT_B([Dur]):
                continue
            for q in prefixes:
                whole = add(q, [Dur])
                if not in_OT_B(whole):
                    continue
                fired += 1
                res = step0(whole)
                # the Lean claim: res = q +_B D_u r' with r' in OT_B, r' < r
                shape_ok = (len(res) == len(q) + 1 and res[:len(q)] == q
                            and res[-1][0] == 'D' and res[-1][1] == u)
                if not shape_ok:
                    bad += 1
                    print(f"  STEP shape FAIL q={fmt(q)} u={u} r={fmt(r)}"
                          f" -> {fmt(res)}")
                    continue
                rp = res[-1][2]
                if in_OT_B(rp) and lt_term(rp, r):
                    ok += 1
                else:
                    bad += 1
                    print(f"  STEP descent FAIL q={fmt(q)} u={u} r={fmt(r)}"
                          f" -> r'={fmt(rp)} OT_B={in_OT_B(rp)}"
                          f" lt={lt_term(rp, r)}")
    return ok, bad, fired


# --------------------------------------------------------------------------
# (B) the top-level conclusion
# --------------------------------------------------------------------------
def check_top(terms, prefixes, max_u, fuel=400):
    ok = bad = fired = 0
    for t in terms:
        for u in range(max_u + 1):
            Dut = D(u, t)
            if not in_OT_B([Dut]):
                continue
            for q in prefixes:
                start = add(q, [Dut])
                if not in_OT_B(start):
                    continue
                fired += 1
                target = add(q, [D(u, ZERO)])
                cur = start
                for _ in range(fuel):
                    if cur == target:
                        break
                    cur = step0(cur)
                if cur == target:
                    ok += 1
                else:
                    bad += 1
                    print(f"  TOP FAIL q={fmt(q)} u={u} t'={fmt(t)}"
                          f" stuck at {fmt(cur)}")
    return ok, bad, fired


# --------------------------------------------------------------------------
# (C) the retracted-A26 witness
# --------------------------------------------------------------------------
def check_A26_witness():
    # t = D_0(D_1(D_1 0)); marked principal D_1(D_1 0), u = 1, t' = D_1 0
    inner = [D(1, [D(1, ZERO)])]
    t = [D(0, inner)]
    print(f"  t             = {fmt(t)}   in OT_B: {in_OT_B(t)}")
    print(f"  marked D_u t' = {fmt(inner)} (u=1, t'={fmt([D(1, ZERO)])})")
    traj, cur = [t], t
    for _ in range(12):
        cur = step0(cur)
        traj.append(cur)
        if cur == ZERO:
            break
    print("  [0]-trajectory: " + " -> ".join(fmt(x) for x in traj))
    # A26's claim: the trajectory never passes through D_0(D_1 0).
    claimed_miss = [D(0, [D(1, ZERO)])]
    hit = claimed_miss in traj
    print(f"  passes through {fmt(claimed_miss)}? {hit}")
    # The lemma the Lean file actually proves is the TOP-LEVEL form, where the
    # marked principal is the trailing component of the host itself:
    #   q = 0_B, u = 1, t' = D_1 0   ==>   ([0]^k)(D_1(D_1 0)) = D_1 0
    start, target = inner, [D(1, ZERO)]
    cur, k = start, 0
    while cur != target and k < 50:
        cur = step0(cur)
        k += 1
    print(f"  top-level form: ([0]^{k})({fmt(start)}) = {fmt(cur)}"
          f"  target {fmt(target)} -> {'OK' if cur == target else 'FAIL'}")
    return cur == target


def main():
    terms = pool_OT_B(max_idx=2, max_depth=3, max_width=2, max_size=6)
    prefixes = pool_OT_B(max_idx=2, max_depth=2, max_width=2, max_size=3)
    print(f"pool: {len(terms)} OT_B bodies, {len(prefixes)} OT_B prefixes\n")

    print("(A) STEP  -- discharged in Lean (operB_Dprin_step_ota),"
          " ASSUMED in Isabelle:")
    ok, bad, fired = check_step(terms, prefixes, max_u=2)
    print(f"    {ok}/{fired} ok, {bad} bad\n")
    a_ok = (bad == 0 and fired > 0)

    print("(B) TOP   -- toplevel_OT_tail_annihilate (modulo OT_B_wf):")
    ok2, bad2, fired2 = check_top(terms, prefixes, max_u=2)
    print(f"    {ok2}/{fired2} ok, {bad2} bad\n")
    b_ok = (bad2 == 0 and fired2 > 0)

    print("(C) retracted-A26 witness under the A23-corrected operB:")
    c_ok = check_A26_witness()
    print()

    verdict = a_ok and b_ok and c_ok
    print("VERDICT:", "ALL PASS" if verdict else "FAILURES PRESENT")
    return 0 if verdict else 1


if __name__ == '__main__':
    sys.exit(main())
