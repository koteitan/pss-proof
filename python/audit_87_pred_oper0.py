#!/usr/bin/env python3
"""Audit of §8.7 補題（Pred と [0] の関係） = pss_paper.thy:2298 (p_8_7_Pred_oper0).

Faithful statement (article 6014; article writes PT_B, a typo for PT_PS):

    M in RT_PS  and  M in PT_PS  and  Lng M - 1 > 1  and  not condVI M
    and Trans M in OT_B
      ==>  EX k. Trans(M)[0]^k = t_1     where the Trans-internal t_1 is Trans(Pred M).

Our records (isabelle/memo.md:67 REFUTED registry, lean/memo.md:601,
lean/8/8.7-termination.lean:136) still say this is FALSE on standard inputs with
counterexample M = (0,0)(1,1)(2,1).  That record is STALE: it was produced under
the A23 misreading of the fundamental sequence ([].4)(ii), and A27 was RETRACTED
on 2026-07-13 (corrections-old.md:69).  python/buchholz.py already carries the
CORRECTED fseq.

This script re-decides the question on the corrected model over the faithful
domain RT_PS cap PT_PS (NOT merely standard hosts, which is what the older probe
python/_s8_real_orbit.py tested -- it also covered only the I/III/V branch).

Run:  python3 python/audit_87_pred_oper0.py [maxlen] [maxval]
"""
import sys, itertools

sys.path.insert(0, "/home/koteitan/proofs/pss-proof/git/python")
import trans_model as TM
import red_model as rm
from red_model import Lng, monoT, fmt
import buchholz as B


def tm_to_buc(t):
    """trans_model term -> buchholz term (list of ('D', v, body))."""
    return [('D', p[1], tm_to_buc(p[2])) for p in t[1]]


def orbit_reaches(transM, t1, maxk=200):
    """Does iterating [0] on the whole Trans(M) hit t_1?  Returns (tag, k, orbit)."""
    cur = transM
    orbit = [B.fmt(cur)]
    if cur == t1:
        return ('ok', 0, orbit)
    for k in range(1, maxk + 1):
        cur = B.bracket(cur, B.ZERO)
        orbit.append(B.fmt(cur))
        if cur == t1:
            return ('ok', k, orbit)
        if B.is_zero(cur):
            return ('hit0_miss', k, orbit)   # reached 0 without meeting t_1
    return ('nofix', None, orbit)


def gen_pairseqs(maxlen, maxval):
    """All pair sequences (0,0) M_1 ... M_{n-1} with entries in [0,maxval]^2."""
    vals = [(a, b) for a in range(maxval + 1) for b in range(maxval + 1)]
    for n in range(2, maxlen + 1):
        for tail in itertools.product(vals, repeat=n - 1):
            yield [(0, 0)] + list(tail)


def branch_of(M):
    if TM.condI(M):   return 'I'
    if TM.condIII(M): return 'III'
    if TM.condV(M):   return 'V'
    if TM.condVI(M):  return 'VI'
    j1 = Lng(M) - 1; jp = rm.parent(M, 0, j1)
    if TM.entry(M, 1, j1) == 0 and not TM.adm(M, jp): return 'II'
    return 'IV'


def main():
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    maxval = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    hosts = 0
    per_branch = {}
    misses = []
    kmax = 0
    for M in gen_pairseqs(maxlen, maxval):
        if Lng(M) - 1 <= 1:            # hypothesis j_1 > 1
            continue
        if not TM.reduced(M):          # M in RT_PS
            continue
        if not monoT(M):               # M in PT_PS  (= T_PS and monoT)
            continue
        if TM.condVI(M):               # hypothesis: M fails condition (VI)
            continue
        try:
            transM = TM.Trans(M)
            t1 = TM.Trans(TM.Pred(M))
        except Exception:
            continue
        tb = tm_to_buc(transM)
        t1b = tm_to_buc(t1)
        if not B.in_OT(tb):            # hypothesis Trans M in OT_B
            continue
        hosts += 1
        br = branch_of(M)
        tag = orbit_reaches(tb, t1b)
        d = per_branch.setdefault(br, [0, 0])
        d[1] += 1
        if tag[0] == 'ok':
            d[0] += 1
            kmax = max(kmax, tag[1])
        else:
            misses.append((M, tb, t1b, tag, br))

    ok = sum(v[0] for v in per_branch.values())
    print(f"domain: M in RT_PS cap PT_PS, Lng-1>1, not condVI, Trans M in OT_B")
    print(f"enumeration: maxlen={maxlen} maxval={maxval}")
    print(f"hosts (non-vacuous): {hosts}")
    print(f"article's claim EX k. Trans(M)[0]^k = Trans(Pred M): {ok}/{hosts}")
    print(f"max k observed: {kmax}")
    print("by branch (ok/total):")
    for br in sorted(per_branch):
        o, t = per_branch[br]
        print(f"   cond {br:>3}: {o}/{t}")
    print(f"MISSES: {len(misses)}")
    for M, tb, t1b, tag, br in misses[:20]:
        print(f"  MISS [{br}] M={fmt(M)}")
        print(f"     Trans(M)     = {B.fmt(tb)}")
        print(f"     t_1=Tr(Pred) = {B.fmt(t1b)}")
        print(f"     orbit: {' -> '.join(tag[2][:8])}  [{tag[0]}]")


if __name__ == "__main__":
    main()
