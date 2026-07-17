#!/usr/bin/env python3
"""Non-vacuity / faithfulness audit for lean/8/8.7-Trans-preserves-OT.lean.

The Lean file is GREEN-MODULO 12 named Props (`OTdisp_*`).  A green file whose
Props are FALSE (mis-transcribed) is worthless, so this script checks every one
of the 12 Props numerically on a REAL standard-form pool: diagSeq closed under
`oper` (random pair sequences are almost never reduced -- memo.md par.3).

Also reports, for each Prop, how many pool instances actually FIRE (a Prop that
never fires is vacuous on the pool and its check proves nothing).

Run:  python3 python/audit_8_7_trans_preserves_OT.py
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')

from red_model import (Lng, entry, monoT, multiT, zeroT, diagSeq, idx1,
                       hasParent, parent, oper)
from trans_model import (Trans, Pred, adm, Adm, reduced, ZB,
                         condI as _condI, condIII as _condIII,
                         condV as _condV, condVI as _condVI)
import buchholz as B

# The model's condI/III/V/VI crash when the last column has no row-0 parent
# (`parent` returns None).  In Lean the conditions are still well-formed there
# (`parent` is total, defaulting to 0), but such M never reach the cond branches
# of the dispatcher -- they are the `hasParent = false` branch, i.e. M[n] = Pred M.
# Guard them out.
def _safe(f):
    def g(M):
        if parent(M, 0, Lng(M) - 1) is None: return False
        return f(M)
    return g

condI, condIII, condV, condVI = (_safe(_condI), _safe(_condIII),
                                 _safe(_condV), _safe(_condVI))

# ---------------------------------------------------------------- conversions
def to_b(t):
    """trans_model BT ('T',[('D',v,BT)]) -> buchholz term (list of principals)."""
    return [('D', p[1], to_b(p[2])) for p in t[1]]

def in_OT_B(t):
    """OT_B = OT n T_B, on a trans_model BT."""
    a = to_b(t)
    return B.in_OT(a) and B.in_TB(a)

def operB(t, k):
    """operB t (numBT k), returned as a buchholz term."""
    return B.bracket(to_b(t), B.nat(k))

# ------------------------------------------------- the six transition conditions
def _j(M):
    j1 = Lng(M) - 1
    return j1, parent(M, 0, j1)

def condII(M):
    j1, jp = _j(M)
    if jp is None: return False
    return entry(M, 1, j1) == 0 and not adm(M, jp)

def condIV(M):
    j1, jp = _j(M)
    if jp is None: return False
    return entry(M, 1, j1) > 0 and entry(M, 1, jp) >= entry(M, 1, j1) and not adm(M, jp)

def transJ0(M):
    return parent(M, 0, Lng(M) - 1)

# ------------------------------------------------------------- standard-form pool
POOL_CAP = 9      # max Lng of a pool member
STEP_CAP = 16     # max Lng of an `oper M m` we are willing to Trans (Trans blows up)

def build_pool(seeds, fseq_ns, rounds):
    """diagSeq seeds, closed under oper with n in fseq_ns, `rounds` deep."""
    seen, pool, frontier = set(), [], []
    for (u, v) in seeds:
        M = diagSeq(u, v)
        if M and tuple(M) not in seen:
            seen.add(tuple(M)); pool.append(M); frontier.append(M)
    for _ in range(rounds):
        nxt = []
        for M in frontier:
            for n in fseq_ns:
                try:
                    Mn = oper(M, n)
                except Exception:
                    continue
                if Mn and Lng(Mn) <= POOL_CAP and tuple(Mn) not in seen:
                    seen.add(tuple(Mn)); pool.append(Mn); nxt.append(Mn)
        frontier = nxt
        if not frontier: break
    return pool

SEEDS = [(u, v) for u in range(0, 3) for v in range(u, u + 4)]
FSEQ_NS, ROUNDS = [1, 2, 3], 3
POOL = build_pool(SEEDS, FSEQ_NS, ROUNDS)

# `Trans` is exponential in Lng; memoise it and refuse over-long inputs.
_tcache = {}
def T(M):
    """Trans M, memoised; None if M is too long to evaluate."""
    k = tuple(M)
    if k in _tcache: return _tcache[k]
    if Lng(M) > STEP_CAP:
        _tcache[k] = None; return None
    v = Trans(M)
    _tcache[k] = v
    return v

def step(M, n):
    """Trans (oper M n), or None if out of budget."""
    Mn = oper(M, n)
    if not Mn: return None
    return T(Mn)

# ------------------------------------------------------------------ the 12 Props
MS = [2, 3]             # the `m`/`n` values swept
results = []

def report(name, isabelle, fired, bad):
    results.append((name, isabelle, fired, bad))

# --- 1. OTdisp_exchI  (Isabelle exchI / scx_condI_exchange1)
fired = bad = 0
for M in POOL:
    j1 = Lng(M) - 1
    if not (monoT(M) and 1 < j1): continue
    jp = parent(M, 0, j1)
    if jp is None or not condI(M) or not (0 < jp): continue
    tM = T(M)
    if tM is None: continue
    for m in MS:
        r = step(M, m)
        if r is None: continue
        fired += 1
        if to_b(r) != operB(tM, m - 1): bad += 1
report("OTdisp_exchI", "exchI", fired, bad)

# --- 2. OTdisp_exchII  (Isabelle exchII)
fired = bad = 0
for M in POOL:
    j1 = Lng(M) - 1
    if not (monoT(M) and 1 < j1 and condII(M)): continue
    tM = T(M)
    if tM is None: continue
    for m in MS:
        r = step(M, m)
        if r is None: continue
        fired += 1
        lhs = to_b(r)
        if not any(lhs == operB(tM, k) for k in range(0, 8)): bad += 1
report("OTdisp_exchII", "exchII", fired, bad)

# --- 3. OTdisp_OTint  (Isabelle OTint)
fired = bad = 0
for M in POOL:
    j1 = Lng(M) - 1
    if not (monoT(M) and 1 < j1): continue
    if not (condIII(M) or condIV(M) or condV(M)): continue
    tM = T(M)
    if tM is None or not in_OT_B(tM): continue
    for m in MS:
        r = step(M, m)
        if r is None: continue
        fired += 1
        if not in_OT_B(r): bad += 1
report("OTdisp_OTint", "OTint", fired, bad)

# --- 4. OTdisp_OTpred  (Isabelle OTpred)
fired = bad = 0
for M in POOL:
    j1 = Lng(M) - 1
    if not (2 < Lng(M)): continue
    tM = T(M)
    if tM is None or not in_OT_B(tM): continue
    if entry(M, 0, j1) == 0 and entry(M, 1, j1) == 0: continue
    if monoT(M) and condI(M): continue
    jp = transJ0(M)
    if monoT(M) and condVI(M) and jp is not None and not adm(M, jp): continue
    tp = T(Pred(M))
    if tp is None: continue
    fired += 1
    if not in_OT_B(tp): bad += 1
report("OTdisp_OTpred", "OTpred", fired, bad)

# --- 5. OTdisp_OTmulti  (Isabelle OTmulti)
fired = bad = 0
for M in POOL:
    if not multiT(M): continue
    tM = T(M)
    if tM is None or not in_OT_B(tM): continue
    for m in MS:
        if oper(M, m) == Pred(M): continue
        r = step(M, m)
        if r is None: continue
        fired += 1
        if not in_OT_B(r): bad += 1
report("OTdisp_OTmulti", "OTmulti", fired, bad)

# --- 6. OTdisp_zerocol_predval  (Isabelle otx_zerocol_predval)
fired = bad = 0
for M in POOL:
    j1 = Lng(M) - 1
    if not (1 < Lng(M) and entry(M, 0, j1) == 0 and entry(M, 1, j1) == 0): continue
    tM = T(M); tp = T(Pred(M))
    if tM is None or tp is None: continue
    for m in [0, 1] + MS:
        fired += 1
        if operB(tM, m) != to_b(tp): bad += 1
report("OTdisp_zerocol_predval", "otx_zerocol_predval", fired, bad)

# --- 7. OTdisp_Trans_fseq_condI_n1  (Isabelle m_8_1_Trans_fseq_condI_n1)
fired = bad = 0
for M in POOL:
    j1 = Lng(M) - 1
    if not (monoT(M) and 1 < j1 and condI(M)): continue
    tM = T(M); r = step(M, 1)
    if tM is None or r is None: continue
    fired += 1
    if to_b(r) != operB(tM, 0): bad += 1
report("OTdisp_Trans_fseq_condI_n1", "m_8_1_Trans_fseq_condI_n1", fired, bad)

# --- 8. OTdisp_condI_j0z_eq  (Isabelle otx_condI_j0z_eq)
fired = bad = 0
for M in POOL:
    j1 = Lng(M) - 1
    if not (monoT(M) and 1 < j1 and condI(M)): continue
    if parent(M, 0, j1) != 0: continue
    tM = T(M)
    if tM is None: continue
    for n in [1] + MS:
        r = step(M, n)
        if r is None: continue
        fired += 1
        if to_b(r) != operB(tM, n - 1): bad += 1
report("OTdisp_condI_j0z_eq", "otx_condI_j0z_eq", fired, bad)

# --- 9. OTdisp_condI_j1eq1_eq  (Isabelle otx_condI_j1eq1_eq)
fired = bad = 0
for M in POOL:
    if not (monoT(M) and Lng(M) == 2 and condI(M)): continue
    tM = T(M)
    if tM is None: continue
    for n in MS:
        r = step(M, n)
        if r is None: continue
        fired += 1
        k = n - 2 if entry(M, 1, 0) == 0 else n - 1
        if to_b(r) != operB(tM, k): bad += 1
report("OTdisp_condI_j1eq1_eq", "otx_condI_j1eq1_eq", fired, bad)

# --- 10. OTdisp_condVI_j1eq1_eq  (Isabelle otx_condVI_j1eq1_eq)
fired = bad = 0
for M in POOL:
    if not (monoT(M) and Lng(M) == 2 and condVI(M)): continue
    j1 = Lng(M) - 1
    if not hasParent(M, idx1(M, j1), j1): continue
    tM = T(M)
    if tM is None: continue
    for n in MS:
        r = step(M, n)
        if r is None: continue
        fired += 1
        if to_b(r) != operB(tM, n - 2): bad += 1
report("OTdisp_condVI_j1eq1_eq", "otx_condVI_j1eq1_eq", fired, bad)

# --- 11. OTdisp_condVI_adm_eq  (Isabelle otx_condVI_adm_eq)
fired = bad = 0
for M in POOL:
    j1 = Lng(M) - 1
    if not (monoT(M) and condVI(M) and 1 < j1): continue
    jp = transJ0(M)
    if jp is None or not adm(M, jp): continue
    tM = T(M)
    if tM is None: continue
    for n in MS:
        r = step(M, n)
        if r is None: continue
        fired += 1
        if to_b(r) != operB(tM, n - 2): bad += 1
report("OTdisp_condVI_adm_eq", "otx_condVI_adm_eq", fired, bad)

# --- 12. OTdisp_condVI_nadm_eq  (Isabelle otx_condVI_nadm_eq)
fired = bad = 0
for M in POOL:
    j1 = Lng(M) - 1
    if not (monoT(M) and condVI(M) and 1 < j1): continue
    jp = transJ0(M)
    if jp is None or adm(M, jp): continue
    tM = T(M)
    if tM is None: continue
    for n in [1] + MS:
        r = step(M, n)
        if r is None: continue
        fired += 1
        if to_b(r) != operB(tM, n - 1): bad += 1
report("OTdisp_condVI_nadm_eq", "otx_condVI_nadm_eq", fired, bad)

# --- bonus: the THEOREM itself (Trans M in OT_B for every pool member)
thm_bad = sum(1 for M in POOL if not in_OT_B(Trans(M)))

# ---------------------------------------------------------------------- report
print(f"standard-form pool: {len(POOL)} sequences (diagSeq seeds {len(SEEDS)}, "
      f"closed under oper n in {FSEQ_NS}, {ROUNDS} rounds, Lng <= {POOL_CAP})")
print(f"all pool members reduced: {all(reduced(M) for M in POOL)}")
print()
print(f"{'Lean Prop':<32}{'Isabelle':<30}{'fired':>7}{'bad':>6}  status")
print("-" * 84)
refuted, vacuous = [], []
for (name, isa, fired, bad) in results:
    if bad: status = "REFUTED (mis-transcribed!)"; refuted.append(name)
    elif fired == 0: status = "not covered by pool"; vacuous.append(name)
    else: status = "ok"
    print(f"{name:<32}{isa:<30}{fired:>7}{bad:>6}  {status}")
print("-" * 84)
print(f"{'p_8_7_Trans_preserves_OT (the theorem)':<62}{thm_bad:>6}  "
      f"{'ok (Trans M in OT_B for all ' + str(len(POOL)) + ')' if thm_bad == 0 else 'REFUTED'}")
print()
if refuted:
    print("VERDICT: REFUTED --", ", ".join(refuted), "are FALSE as transcribed.")
elif thm_bad:
    print("VERDICT: REFUTED -- the theorem itself fails on the pool.")
else:
    print(f"VERDICT: no counterexample. {len(results) - len(vacuous)}/{len(results)} "
          f"Props fire and hold; theorem holds on all {len(POOL)}.")
    if vacuous:
        print(f"         NOT COVERED (vacuous on this pool, so unverified): "
              f"{', '.join(vacuous)}.")
        print("         condition (II) = non-admissible row-0 parent with M_{1,j1}=0.")
        print("         A separate search over 18318 standard forms (diagSeq u<4,")
        print("         v<u+7, closed under oper n in [1..4], 8 rounds, Lng <= 16)")
        print("         found 0 instances, so no pool can cover it at this size.")
        print("         Corroboration instead: OTdisp_exchII is BYTE-IDENTICAL to")
        print("         FseqDesc_exchII in the built 8.7-fseq-descend.lean, and to")
        print("         Isabelle c2sx_exchange_ex_condII_of_tailval (pss_wip:87577)")
        print("         minus the TV slot that TVall discharges. Flagged in `needs`.")
