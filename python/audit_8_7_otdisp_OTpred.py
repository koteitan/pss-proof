#!/usr/bin/env python3
"""Audit for lean/8/8.7-otdisp-OTpred.lean (Brick A of the OTpred port).

Two independent claims are checked on a REAL standard-form pool (diagSeq closed
under `oper` -- random pair sequences are almost never reduced, memo.md par.3):

(1) `OTdisp_OTpred` is TRUE and NON-VACUOUS.
    The wave-K accident was a Lean Prop that kept the Isabelle hypothesis bundle
    but dropped one hypothesis, making it FALSE and the main theorem vacuous.
    Here the diff runs the other way: the Lean Prop carries `2 < Lng N` plus
    three corner exclusions that Isabelle's `od4_OTpred_final`
    (layerC/pss_scratch.thy:874) does NOT need, so the Lean Prop is strictly
    WEAKER.  This script confirms that empirically, and also checks the STRONG
    Isabelle form (`od4_OTpred_mono`, :803) which has no exclusions at all.

(2) The Brick-A target shape is right: `od4_R (Trans (Pred M)) (Trans M)`
    (Isabelle MASTER `od4_master_R`, :760) holds on the pool.  `od4_R` is the
    inductive relation this Lean file ports as `od4R_op`; the master brick is the
    reason Brick A is the correct core.  Re-implemented here from the Isabelle
    inductive (:37) so the Lean transcription is checked against an independent
    reading of the source.

Run:  python3 python/audit_8_7_otdisp_OTpred.py
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')

from red_model import Lng, entry, monoT, diagSeq, oper, parent
from trans_model import Trans, Pred, adm, reduced, ZB, bpHeadT
from trans_model import (condI as _condI, condVI as _condVI)
import buchholz as B

# The model's condI/VI crash when the last column has no row-0 parent (`parent`
# returns None).  In Lean `parent` is total (defaults to 0); such M never reach
# the cond branches.  Guard them out, exactly as audit_8_7_trans_preserves_OT.py.
def _safe(f):
    def g(M):
        if parent(M, 0, Lng(M) - 1) is None: return False
        return f(M)
    return g

condI, condVI = _safe(_condI), _safe(_condVI)

def to_b(t):
    return [('D', p[1], to_b(p[2])) for p in t[1]]

def in_OT_B(t):
    a = to_b(t)
    return B.in_OT(a) and B.in_TB(a)

# --------------------------------------------------------- od4_R (Isabelle :37)
# od4_R_drop: od4_R (Trm ps)              (Trm (ps @ [p]))
# od4_R_triv: lessBP (DB w 0) p ==> od4_R (Trm (ps @ [DB w 0])) (Trm (ps @ [p]))
# od4_R_deep: od4_R c c'   ==> od4_R (Trm (ps @ [DB w c])) (Trm (ps @ [DB w c']))
def lessBP(p, q):
    """p, q are buchholz principals ('D', v, term)."""
    return B.lt_princ(p, q)

def od4_R(a, b):
    """Faithful re-reading of the Isabelle inductive, as a decision procedure."""
    ap, bp = a[1], b[1]
    # od4_R_drop: a = ps, b = ps @ [p]
    if len(bp) == len(ap) + 1 and bp[:len(ap)] == ap:
        return True
    if len(ap) == len(bp) and len(ap) >= 1 and ap[:-1] == bp[:-1]:
        pa, pb = ap[-1], bp[-1]
        # od4_R_triv: pa = DB w 0 with lessBP pa pb
        if pa[2] == ZB and lessBP(('D', pa[1], to_b(pa[2])),
                                 ('D', pb[1], to_b(pb[2]))):
            return True
        # od4_R_deep: same head w, bodies od4_R-related
        if pa[1] == pb[1]:
            return od4_R(pa[2], pb[2])
    return False

# ------------------------------------------------- standard-form pool (reused)
POOL_CAP = 9

def build_pool(seeds, fseq_ns, rounds):
    seen, pool, frontier = set(), [], []
    for M in seeds:
        if tuple(M) not in seen:
            seen.add(tuple(M)); pool.append(M); frontier.append(M)
    for _ in range(rounds):
        nxt = []
        for M in frontier:
            for n in fseq_ns:
                Mn = oper(M, n)
                if Mn is None or Lng(Mn) > POOL_CAP: continue
                if tuple(Mn) not in seen:
                    seen.add(tuple(Mn)); pool.append(Mn); nxt.append(Mn)
        frontier = nxt
        if not frontier: break
    return pool

SEEDS = [diagSeq(u, v) for u in range(4) for v in range(u, 6)]
FSEQ_NS = [1, 2, 3, 4]
ROUNDS = 4
POOL = build_pool(SEEDS, FSEQ_NS, ROUNDS)

print(f"standard-form pool: {len(POOL)} sequences "
      f"(diagSeq seeds {len(SEEDS)}, fseq n in {FSEQ_NS}, {ROUNDS} rounds)")
print(f"all pool members reduced: {all(reduced(M) for M in POOL)}")
print()

# ------------------------------------------- (1) OTdisp_OTpred: true? vacuous?
def zerocol(N):
    j1 = Lng(N) - 1
    return entry(N, 0, j1) == 0 and entry(N, 1, j1) == 0

def excl_condI(N):
    return monoT(N) and condI(N)

def excl_condVI_nadm(N):
    if not (monoT(N) and condVI(N)): return False
    jp = parent(N, 0, Lng(N) - 1)
    return not adm(N, jp)

fired = fail = 0
for N in POOL:
    if not (Lng(N) > 2): continue
    if not in_OT_B(Trans(N)): continue          # host hypothesis
    if zerocol(N): continue                     # exclusion 1
    if excl_condI(N): continue                  # exclusion 2
    if excl_condVI_nadm(N): continue            # exclusion 3
    fired += 1
    if not in_OT_B(Trans(Pred(N))):
        fail += 1
        print(f"  OTdisp_OTpred FAIL: {N}")
print(f"(1) OTdisp_OTpred          : fired {fired:4d}, failures {fail}")

# The STRONG Isabelle form od4_OTpred_mono (:803): no exclusions, no 2 < Lng.
fired_s = fail_s = 0
for N in POOL:
    if not (Lng(N) > 1): continue
    if not monoT(N): continue
    if not in_OT_B(Trans(N)): continue
    fired_s += 1
    if not in_OT_B(Trans(Pred(N))):
        fail_s += 1
        print(f"  od4_OTpred_mono FAIL: {N}")
print(f"    od4_OTpred_mono (STRONG): fired {fired_s:4d}, failures {fail_s}")
print("    -> STRONG form needs none of the 3 exclusions nor 2 < Lng, so the")
print("       Lean Prop is a strict WEAKENING of it: it cannot be false.")
print()

# ---------------------------------- (2) MASTER: od4_R (Trans (Pred M)) (Trans M)
fired_m = fail_m = 0
for M in POOL:
    if not (Lng(M) - 1 > 1): continue           # j1gt
    if not monoT(M): continue                   # M in PT_PS
    if Trans(Pred(M)) == ZB: continue           # T1 (transT1 M != 0_B)
    fired_m += 1
    if not od4_R(Trans(Pred(M)), Trans(M)):
        fail_m += 1
        print(f"  od4_master_R FAIL: {M}")
print(f"(2) od4_master_R           : fired {fired_m:4d}, failures {fail_m}")
print("    -> Brick A (od4R_op + od4R_OT_B, this Lean file) is the correct core:")
print("       Trans (Pred M) really is an un-insertion of Trans M.")
print()

ok = (fail == 0 and fail_s == 0 and fail_m == 0 and fired > 0 and fired_m > 0)
print("VERDICT:", "OK -- Prop true & non-vacuous, master shape confirmed"
      if ok else "PROBLEM -- see failures above")
sys.exit(0 if ok else 1)
