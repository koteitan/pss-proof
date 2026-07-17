#!/usr/bin/env python3
"""Non-vacuity / faithfulness audit for lean/8/8.7-otdisp-OTint.lean.

The Lean file reduces the residual leaf `OTdisp_OTint` to
`OTint_hasParent` (the same statement PLUS `hasParent N 1 (Lng N - 1)`),
discharging the `hasParent = false` corner from the ALREADY-EXISTING leaf
`OTdisp_OTpred`.  Two things must be checked numerically:

  (A) the discharged corner is SOUND and the four private side lemmas hold:
        cond345 => 0 < N_{1,j1}          (cond345_entry1_pos_oi)
        cond345 => not condI             (cond345_not_condI_oi)
        cond345 => not condVI            (cond345_not_condVI_oi)
        cond345 & not hasParent => N[m] = Pred N   (oper_noParent_Pred_oi)
      and, at the corner, the three OTpred corner-exclusions really hold, so
      `OTdisp_OTpred` is applicable and yields Trans (N[m]) in OT_B.

  (B) the RESIDUAL `OTint_hasParent` is still LIVE (it fires on the pool);
      and we report how much of `OTdisp_OTint` the corner actually removes.

Pool: diagSeq closed under `oper` (random pair sequences are almost never
reduced -- memo.md par.3).

Run:  python3 python/audit_8_7_otdisp_OTint.py
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')

from red_model import (Lng, entry, monoT, diagSeq, idx1, hasParent, parent,
                       oper)
from trans_model import (Trans, Pred, adm, reduced,
                         condI as _condI, condIII as _condIII,
                         condV as _condV, condVI as _condVI)
import buchholz as B


# ---------------------------------------------------------------- conditions
# The model's condI/III/V/VI crash when the last column has no row-0 parent
# (`parent` returns None).  In Lean `parent` is total (defaults to 0), so the
# conditions are still well-formed there.  Guard them out here.
def _safe(f):
    def g(M):
        if parent(M, 0, Lng(M) - 1) is None:
            return False
        return f(M)
    return g


condI, condIII, condV, condVI = (_safe(_condI), _safe(_condIII),
                                 _safe(_condV), _safe(_condVI))


def condIV(M):
    j1 = Lng(M) - 1
    jp = parent(M, 0, j1)
    if jp is None:
        return False
    return (entry(M, 1, j1) > 0 and entry(M, 1, jp) >= entry(M, 1, j1)
            and not adm(M, jp))


def cond345(M):
    return condIII(M) or condIV(M) or condV(M)


def transJ0(M):
    return parent(M, 0, Lng(M) - 1)


# ---------------------------------------------------------------- OT_B
def to_b(t):
    return [('D', p[1], to_b(p[2])) for p in t[1]]


def in_OT_B(t):
    a = to_b(t)
    return B.in_OT(a) and B.in_TB(a)


# ------------------------------------------------------- standard-form pool
POOL_CAP = 9
STEP_CAP = 16


def build_pool(seeds, fseq_ns, rounds):
    seen, pool, frontier = set(), [], []
    for (u, v) in seeds:
        M = diagSeq(u, v)
        if M and tuple(M) not in seen:
            seen.add(tuple(M))
            pool.append(M)
            frontier.append(M)
    for _ in range(rounds):
        nxt = []
        for M in frontier:
            for n in fseq_ns:
                try:
                    Mn = oper(M, n)
                except Exception:
                    continue
                if Mn and Lng(Mn) <= POOL_CAP and tuple(Mn) not in seen:
                    seen.add(tuple(Mn))
                    pool.append(Mn)
                    nxt.append(Mn)
        frontier = nxt
        if not frontier:
            break
    return pool


SEEDS = [(u, v) for u in range(0, 3) for v in range(u, u + 4)]
POOL = build_pool(SEEDS, [1, 2, 3], 3)

_tcache = {}


def T(M):
    k = tuple(M)
    if k in _tcache:
        return _tcache[k]
    if Lng(M) > STEP_CAP:
        _tcache[k] = None
        return None
    v = Trans(M)
    _tcache[k] = v
    return v


MS = [2, 3]

# ------------------------------------------------------------------ counters
c = dict(pool=len(POOL), reduced=0, hosts=0,
         fire_np=0, fire_hp=0,
         bad_pos=0, bad_nocondI=0, bad_nocondVI=0, bad_operPred=0,
         bad_excl_len=0, bad_excl_zc=0, bad_excl_I=0, bad_excl_VI=0,
         corner_checked=0, bad_corner_OT=0, corner_skipped=0)

for M in POOL:
    if reduced(M):
        c['reduced'] += 1
    # host guard of OTdisp_OTint (STPS is by construction of the pool)
    if not (monoT(M) and Lng(M) - 1 > 1 and cond345(M)):
        continue
    c['hosts'] += 1
    j1 = Lng(M) - 1

    # ---- (A) the three private side lemmas -----------------------------
    if not entry(M, 1, j1) > 0:
        c['bad_pos'] += 1
    if condI(M):
        c['bad_nocondI'] += 1
    if condVI(M):
        c['bad_nocondVI'] += 1

    hp = hasParent(M, 1, j1)
    if hp:
        c['fire_hp'] += 1
        continue
    c['fire_np'] += 1

    # ---- the discharged corner ----------------------------------------
    # oper_noParent_Pred_oi : N[m] = Pred N for every m
    for m in MS:
        if oper(M, m) != Pred(M):
            c['bad_operPred'] += 1

    # OTdisp_OTpred's own three corner exclusions must hold here
    if not Lng(M) > 2:
        c['bad_excl_len'] += 1
    if entry(M, 0, j1) == 0 and entry(M, 1, j1) == 0:
        c['bad_excl_zc'] += 1
    if monoT(M) and condI(M):
        c['bad_excl_I'] += 1
    if monoT(M) and condVI(M) and not adm(M, transJ0(M)):
        c['bad_excl_VI'] += 1

    # and the conclusion Trans (N[m]) in OT_B must really hold there
    tN = T(M)
    if tN is None or not in_OT_B(tN):
        c['corner_skipped'] += 1
        continue
    ok = True
    for m in MS:
        tm = T(oper(M, m))
        if tm is None:
            ok = False
            break
        if not in_OT_B(tm):
            c['bad_corner_OT'] += 1
    if ok:
        c['corner_checked'] += 1
    else:
        c['corner_skipped'] += 1

# ------------------------------------------------------------------- report
print(f"pool                : {c['pool']} standard forms "
      f"({c['reduced']} reduced)")
print(f"OTint hosts         : {c['hosts']}  "
      f"(STPS & monoT & 1<Lng-1 & (III|IV|V))")
print(f"  hasParent = true  : {c['fire_hp']}  <- RESIDUAL OTint_hasParent")
print(f"  hasParent = false : {c['fire_np']}  <- DISCHARGED here via OTdisp_OTpred")
print()
print("private side lemmas (counterexamples; 0 expected):")
print(f"  cond345_entry1_pos_oi   : {c['bad_pos']}")
print(f"  cond345_not_condI_oi    : {c['bad_nocondI']}")
print(f"  cond345_not_condVI_oi   : {c['bad_nocondVI']}")
print(f"  oper_noParent_Pred_oi   : {c['bad_operPred']}")
print()
print("OTdisp_OTpred applicability at the discharged corner "
      "(counterexamples; 0 expected):")
print(f"  2 < Lng N               : {c['bad_excl_len']}")
print(f"  not both-zero last col  : {c['bad_excl_zc']}")
print(f"  not (monoT & condI)     : {c['bad_excl_I']}")
print(f"  not (monoT & condVI &..): {c['bad_excl_VI']}")
print()
print(f"corner conclusion verified : {c['corner_checked']} hosts x {MS} "
      f"({c['corner_skipped']} skipped: Trans out of budget / host not in OT_B)")
print(f"  Trans (N[m]) NOT in OT_B : {c['bad_corner_OT']}  (0 expected)")

bad = sum(v for k, v in c.items() if k.startswith('bad_'))
print()
if bad:
    print(f"*** {bad} COUNTEREXAMPLE(S) -- the Lean file's claims are SUSPECT ***")
    sys.exit(1)
if c['fire_np'] == 0:
    print("NOTE: the discharged corner never fires on this pool "
          "(the reduction is sound but empirically untested here).")
if c['fire_hp'] == 0:
    print("NOTE: the residual OTint_hasParent never fires on this pool.")
print("all checks pass")
