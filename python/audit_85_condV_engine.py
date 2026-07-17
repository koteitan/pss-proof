#!/usr/bin/env python3
"""Adversarial numeric audit for lean/8/8.5-TransCondV-engine.lean.

Targets (public claims re-stated 1:1 from the Lean source):

  * `TransCondV_oper1_descend`               <- the n=1 leg of Isabelle
                                                m_8_5_TransCondV_oper_descend_engine
                                                (layerB/pss_wip.thy:37496), cf. the
                                                condII twin m_8_3_TransCondII_oper1_descend
                                                (26336)
  * `TransCondV_oper_descend_engine`         <- Isabelle m_8_5_TransCondV_oper_descend_engine
                                                (37496); satisfies
                                                FseqDesc_m_8_5_TransCondV_oper_descend_engine
                                                (8.7-fseq-descend:138)

Semantics: python/red_model.py + python/trans_model.py + python/buchholz.py
(the canonical models).  Pool idiom copied from python/audit_83_condII_engine.py.

WHY THIS AUDIT EXISTS: the condition-(II) twin of this engine turned out to be
(apparently) VACUOUS on ST_PS -- 0 hosts out of 32056 standard forms.  Since the
engine is a REDUCTION, vacuity would not make it unsound, but it would make it
useless.  So before trusting the condition-(V) port, check that condition (V)
actually FIRES on ST_PS, and that the engine's conclusion holds where it does.

Checks, on the ST_PS pool (= diagSeq closed under `oper`, exactly the Lean
inductive `STPS`, PSS/Standard.lean:16), restricted to condition-(V) hosts with
`monoT M` and `Lng M - 1 > 1` (the engine's hypotheses):

  1. non-vacuity      : how many condition-(V) hosts exist at all
  2. TOT              : `Trans M in OT_B`   (the engine's `hOT`)
  3. oper1 descent    : `Trans (M[1]) < Trans M`            (the n=1 leg)
  4. exch satisfiable : `exists k <= KCAP. Trans (M[n]) <=_B operB (Trans M) (numBT k)`
                        (the engine's `hexch` -- a PREMISE, so this checks the
                        engine is not conditioned on something false)
  5. conclusion       : `Trans (M[n]) < Trans M` for all n > 0  (the engine's goal)

Exit code 0 = no counterexample found.
"""
import sys, os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.setrecursionlimit(100000)

from red_model import Lng, entry, parent, monoT, oper, diagSeq
from trans_model import Trans
import buchholz as B


# ---------------------------------------------------------------- conversions
def to_b(t):
    """trans_model BT ('T',[('D',v,BT)]) -> buchholz term (list of principals)."""
    return [('D', p[1], to_b(p[2])) for p in t[1]]


def in_OT_B(t):
    a = to_b(t)
    return B.in_OT(a) and B.in_TB(a)


def operB(t, k):
    """operB t (numBT k), as a buchholz term."""
    return B.bracket(to_b(t), B.nat(k))


def lessBT(a, b):
    return B.lt_term(to_b(a), to_b(b))


def leBT_raw(a, b_raw):
    """leBT a b where b is ALREADY a buchholz term (operB output)."""
    ab = to_b(a)
    return ab == b_raw or B.lt_term(ab, b_raw)


def condV(M):
    """Lean PSS/Trans.lean:115 transCondV, 1:1."""
    j1 = Lng(M) - 1
    jp = parent(M, 0, j1)
    if jp is None:
        return False
    return (entry(M, 1, j1) > 0
            and entry(M, 1, jp) + 1 == entry(M, 1, j1)
            and jp + 1 < j1)


STEP_CAP = 16
_tcache = {}


def T(M):
    k = tuple(M)
    if k in _tcache:
        return _tcache[k]
    if Lng(M) > STEP_CAP:
        _tcache[k] = None
        return None
    try:
        v = Trans(M)
    except Exception:
        v = None
    _tcache[k] = v
    return v


# ======================================================== POOL: ST_PS
def build_st_pool(seed_u, seed_v_off, ns, rounds, cap):
    seen, pool, fr = set(), [], []
    for u in range(0, seed_u):
        for v in range(u, u + seed_v_off):
            M = diagSeq(u, v)
            if M and tuple(M) not in seen:
                seen.add(tuple(M))
                pool.append(M)
                fr.append(M)
    for _ in range(rounds):
        nx = []
        for M in fr:
            for n in ns:
                try:
                    Mn = oper(M, n)
                except Exception:
                    continue
                if Mn and Lng(Mn) <= cap and tuple(Mn) not in seen:
                    seen.add(tuple(Mn))
                    pool.append(Mn)
                    nx.append(Mn)
        fr = nx
        if not fr:
            break
    return pool


print("=" * 78)
print("POOL: ST_PS = diagSeq closed under oper  (Lean PSS/Standard.lean:16)")
print("=" * 78)
if os.environ.get("PSS_AUDIT_FULL"):
    ST_POOL = build_st_pool(5, 8, [1, 2, 3, 4, 5], 8, 16)
else:
    ST_POOL = build_st_pool(4, 6, [1, 2, 3, 4], 6, 12)

HOSTS = []
for M in ST_POOL:
    j1 = Lng(M) - 1
    if not (1 < j1):
        continue
    try:
        if not monoT(M):
            continue
        if not condV(M):
            continue
    except Exception:
        continue
    HOSTS.append(M)

print("standard forms scanned                    :", len(ST_POOL))
print("max component value                       :",
      max(max(max(a, b) for (a, b) in M) for M in ST_POOL))
print("max Lng                                   :", max(Lng(M) for M in ST_POOL))
print("condition (V) hosts (monoT, Lng-1 > 1)    :", len(HOSTS))
for M in HOSTS[:5]:
    print("   ", M)
print()
if len(HOSTS) == 0:
    print("=> condition (V) is EMPTY on this ST_PS pool (like condition (II)).")
else:
    print("=> condition (V) DOES occur on ST_PS "
          "(unlike condition (II): engine is NOT vacuous).")
print()

NS = [1, 2, 3, 4]
KCAP = 6
results = []


def report(name, fired, bad, note=""):
    results.append((name, fired, bad, note))
    tag = "OK " if bad == 0 else "CEX"
    print("[%s] %-42s fired=%-6d cex=%d %s" % (tag, name, fired, bad, note))


print("=" * 78)
print("CLAIM CHECKS on condition-(V) hosts")
print("=" * 78)

# --- (2) TOT: Trans M in OT_B  (the engine's hOT hypothesis)
fired = bad = 0
for M in HOSTS:
    tM = T(M)
    if tM is None:
        continue
    fired += 1
    if not in_OT_B(tM):
        bad += 1
        print("   CEX TOT:", M)
report("Trans M in OT_B (hOT premise)", fired, bad)

# --- (3) oper1 descent: the engine's n=1 leg (TransCondV_oper1_descend)
fired = bad = 0
for M in HOSTS:
    tM, t1 = T(M), T(oper(M, 1))
    if tM is None or t1 is None:
        continue
    fired += 1
    if not lessBT(t1, tM):
        bad += 1
        print("   CEX oper1 descent:", M)
report("TransCondV_oper1_descend", fired, bad)

# --- (4) exch premise satisfiable: exists k. Trans(M[n]) <=_B operB(Trans M)(numBT k)
fired = bad = 0
for M in HOSTS:
    tM = T(M)
    if tM is None:
        continue
    ops = []
    for k in range(KCAP):
        try:
            ops.append(operB(tM, k))
        except Exception:
            ops.append(None)
    for n in NS:
        if n <= 1:
            continue
        tn = T(oper(M, n))
        if tn is None:
            continue
        fired += 1
        if not any(o is not None and leBT_raw(tn, o) for o in ops):
            bad += 1
            print("   CEX exch (no k<%d):" % KCAP, M, "n=", n)
report("exch premise satisfiable (k<%d)" % KCAP, fired, bad,
       "(premise, not conclusion)")

# --- (5) engine conclusion: Trans(M[n]) < Trans M for all n > 0
fired = bad = 0
for M in HOSTS:
    tM = T(M)
    if tM is None:
        continue
    for n in NS:
        tn = T(oper(M, n))
        if tn is None:
            continue
        fired += 1
        if not lessBT(tn, tM):
            bad += 1
            print("   CEX engine conclusion:", M, "n=", n)
report("TransCondV_oper_descend_engine (goal)", fired, bad)

print()
print("=" * 78)
total_bad = sum(b for (_, _, b, _) in results)
never_fired = [n for (n, f, _, _) in results if f == 0]
print("counterexamples:", total_bad)
if never_fired:
    print("NOT EXERCISED (pool too small / vacuous):", never_fired)
print("=" * 78)
sys.exit(1 if total_bad else 0)
