#!/usr/bin/env python3
"""Adversarial numeric audit for lean/8/8.3-TransCondII-engine.lean.

Targets (public claims re-stated 1:1 from the Lean source):

  * `TransCondII_oper1_descend`          <- Isabelle m_8_3_TransCondII_oper1_descend
                                            (layerB/pss_wip.thy:26336)
  * `TransCondII_oper_descend_engine`    <- Isabelle m_8_3_TransCondII_oper_descend_engine
                                            (28563); satisfies
                                            FseqDesc_m_8_3_TransCondII_oper_descend_engine
                                            (8.7-fseq-descend:131)
  * `operB_marked_scb_value_c2`          <- Isabelle operB_marked_scb_value (37100)
  * `exch_of_lhs_closed_ex_c2`           <- Isabelle c2ex_exch_of_lhs_closed_ex (70717)
  * `CondII_masterCF` (green-modulo)     <- Isabelle c2sx_condII_masterCF (87430),
                                            TV discharged by y3j_condII_tailval
                                            (layerC/pss_scratch.thy:17079)
  * `exchII_of_masterCF`                 -> satisfies FseqDesc_exchII (8.7-fseq-descend:77)

Semantics: python/red_model.py + python/trans_model.py + python/buchholz.py
(the canonical models).

TWO POOLS, because the headline finding of this audit is a VACUITY question:

  (A) ST_PS pool -- diagSeq closed under `oper`, i.e. EXACTLY the Lean
      inductive `STPS` (PSS/Standard.lean:16).  This is the pool idiom of
      python/audit_8_7_trans_preserves_OT.py.
  (B) RT_PS pool -- brute-force reduced/monoT condition-(II) hosts.  Isabelle's
      `c2sx_condII_masterCF` assumes only `M in RT_PS`, so (B) is where the
      mathematical content of the exchange law can actually be exercised.

FINDINGS (2026-07-17 run):

  * condition (II) has ZERO instances on ST_PS.  32056 standard forms
    (diagSeq u<5, v<u+8, closed under oper n in [1..5], 8 rounds, Lng <= 16,
    max component 19): 8298 have `entry M 1 (Lng M - 1) = 0` and a row-0
    parent, and 0 of those have a NON-admissible parent.  So on standard forms
    `entry M 1 (Lng M -1) = 0` appears to FORCE `adm (parent M 0 (Lng M -1))`,
    i.e. condition (I) absorbs every case condition (II) was meant to catch.
    => `FseqDesc_exchII` and the condition-(II) leg of the descent dispatcher
       look VACUOUS on ST_PS.  Independently corroborated: the built
       8.7-fseq-descend's own audit (audit_8_7_trans_preserves_OT.py) reports
       `OTdisp_exchII` as "not covered by pool", 0 instances of 18318.
  * condition (II) is NOT empty on RT_PS: e.g. (0,0)(1,1)(2,2)(2,0) is
    reduced, monoT, Lng-1 = 3 > 1, condition (II).  The engine / oper1-descent
    / masterCF-witness claims all HOLD on the RT_PS host pool (no CEX), so the
    ported statements are sound, not nonsense -- only their ST_PS instantiation
    is (apparently) empty.

Exit code 0 = no counterexample found on either pool.
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.setrecursionlimit(100000)

from red_model import (Lng, entry, parent, monoT, oper, diagSeq, reduced, Pred)
from trans_model import (Trans, Mark, Adm, adm, ZB, Dpt, addBT, PB, SigmaB,
                         bpHeadV, bpHeadT, flatBT, unflatBT, scb_decomps)
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

def multBT(t, k):
    out = ZB
    for _ in range(k):
        out = addBT(out, t)
    return out

def condII(M):
    j1 = Lng(M) - 1
    jp = parent(M, 0, j1)
    if jp is None:
        return False
    return entry(M, 1, j1) == 0 and not adm(M, jp)

STEP_CAP = 16
_tcache = {}
def T(M):
    k = tuple(M)
    if k in _tcache: return _tcache[k]
    if Lng(M) > STEP_CAP:
        _tcache[k] = None; return None
    try:
        v = Trans(M)
    except Exception:
        v = None
    _tcache[k] = v
    return v

def step(M, n):
    try:
        Mn = oper(M, n)
    except Exception:
        return None
    if not Mn: return None
    return T(Mn)

results = []
def report(name, fired, bad, note=""):
    results.append((name, fired, bad, note))

# ======================================================== POOL (A): ST_PS
def build_st_pool(seed_u, seed_v_off, ns, rounds, cap):
    seen, pool, fr = set(), [], []
    for u in range(0, seed_u):
        for v in range(u, u + seed_v_off):
            M = diagSeq(u, v)
            if M and tuple(M) not in seen:
                seen.add(tuple(M)); pool.append(M); fr.append(M)
    for _ in range(rounds):
        nx = []
        for M in fr:
            for n in ns:
                try: Mn = oper(M, n)
                except Exception: continue
                if Mn and Lng(Mn) <= cap and tuple(Mn) not in seen:
                    seen.add(tuple(Mn)); pool.append(Mn); nx.append(Mn)
        fr = nx
        if not fr: break
    return pool

print("=" * 78)
print("POOL (A): ST_PS = diagSeq closed under oper  (Lean PSS/Standard.lean:16)")
print("=" * 78)
# Default params run in ~1 min.  The FINDINGS docstring above quotes the
# full-scale run (build_st_pool(5, 8, [1,2,3,4,5], 8, 16) -> 32056 forms,
# max component 19, 8298 with entry1(j1)=0, 0 condII hosts, ~10 min); set
# PSS_AUDIT_FULL=1 to reproduce it.
if os.environ.get("PSS_AUDIT_FULL"):
    ST_POOL = build_st_pool(5, 8, [1, 2, 3, 4, 5], 8, 16)
else:
    ST_POOL = build_st_pool(4, 6, [1, 2, 3, 4], 6, 12)
st_e1z = st_hosts = 0
for M in ST_POOL:
    j1 = Lng(M) - 1
    jp = parent(M, 0, j1)
    if jp is None: continue
    if entry(M, 1, j1) == 0:
        st_e1z += 1
        if not adm(M, jp): st_hosts += 1
print("standard forms scanned                    :", len(ST_POOL))
print("max component value                       :",
      max(max(max(a, b) for (a, b) in M) for M in ST_POOL))
print("max Lng                                   :", max(Lng(M) for M in ST_POOL))
print("with row-0 parent and entry1(j1)==0       :", st_e1z)
print("of those, ~adm(parent)  = condII HOSTS    :", st_hosts)
print()
print("=> condition (II) is EMPTY on this ST_PS pool." if st_hosts == 0
      else "=> condition (II) DOES occur on ST_PS!")
report("condII hosts on ST_PS", len(ST_POOL), 0,
       "hosts found: %d  (=> FseqDesc_exchII looks VACUOUS on ST_PS)" % st_hosts)

# ======================================================== POOL (B): RT_PS
# Brute-force reduced/monoT condition-(II) hosts.  Random pair sequences are
# almost never reduced, so enumerate small ones exhaustively.
print()
print("=" * 78)
print("POOL (B): RT_PS condition-(II) hosts (brute force)")
print("=" * 78)
RT_HOSTS = []
CAP = 6            # component range 0..CAP-1 (memo: do NOT scan components < 3)
LMAX = 6 if os.environ.get("PSS_AUDIT_FULL") else 5
for L in range(3, LMAX):
    # column 0 of a reduced sequence is always (0,0); only generate columns 1..L-1.
    for tail in itertools.product(range(0, CAP), repeat=2 * (L - 1)):
        Mt = [(0, 0)] + [(tail[2 * i], tail[2 * i + 1]) for i in range(L - 1)]
        j1 = Lng(Mt) - 1
        if not (1 < j1): continue
        # cheap condII prefilter before the expensive reduced()/monoT()
        if entry(Mt, 1, j1) != 0: continue
        try:
            if not reduced(Mt) or not monoT(Mt): continue
            if not condII(Mt): continue
        except Exception:
            continue
        RT_HOSTS.append(Mt)
    print("   L=%d cumulative hosts: %d" % (L, len(RT_HOSTS)))
print("RT_PS condII hosts found                  :", len(RT_HOSTS))
for M in RT_HOSTS[:5]:
    print("   ", M)

NS = [2, 3, 4]

# --- oper1 descent (the engine's n=1 leg)
fired = bad = 0
for M in RT_HOSTS:
    tM = T(M)
    t1 = step(M, 1)
    if tM is None or t1 is None: continue
    fired += 1
    if not lessBT(t1, tM):
        bad += 1
        if bad <= 3: print("  oper1_descend CEX:", M)
report("TransCondII_oper1_descend (RT)", fired, bad)

# --- the engine's conclusion
fired = bad = 0
for M in RT_HOSTS:
    tM = T(M)
    if tM is None or not in_OT_B(tM): continue
    for n in [1] + NS:
        tMn = step(M, n)
        if tMn is None: continue
        fired += 1
        if not lessBT(tMn, tM):
            bad += 1
            if bad <= 3: print("  engine CEX:", M, "n=", n)
report("engine conclusion (RT)", fired, bad)

# --- CondII_masterCF, via the Isabelle witnesses (c2sx proof / _c2 condII branch)
def masterCF_witnesses(M):
    j1 = Lng(M) - 1
    jp = parent(M, 0, j1)
    if jp is None: return None
    tPred = T(Pred(M))
    if tPred is None or tPred == ZB: return None
    try:
        c1 = Mark(Pred(M), Adm(M, jp))
    except Exception:
        return None
    va = bpHeadV(c1); t2 = bpHeadT(c1)
    v0 = entry(M, 1, jp)
    if t2 == ZB:
        t3, t4 = ZB, ZB
    else:
        Pt2 = PB(t2); pj = Pt2[-1]
        leftDj0 = (bpHeadV(pj) == v0)
        t3 = SigmaB(Pt2[:-1]) if leftDj0 else t2
        t4 = bpHeadT(pj) if leftDj0 else t2
    c2 = Dpt(va, addBT(t3, Dpt(v0, addBT(t4, Dpt(0, ZB)))))
    tM = T(M)
    if tM is None: return None
    ds = scb_decomps(tM, flatBT(c2))
    if not ds: return None
    s, b = ds[0]
    return (s, b, va, v0, t3, t4)

fired = bad = noshape = 0
for M in RT_HOSTS:
    w = masterCF_witnesses(M)
    if w is None:
        noshape += 1; continue
    s, b, va, v0, t3, t4 = w
    fired += 1
    ok = True
    for m in NS:
        tMm = step(M, m)
        if tMm is None: continue
        if not any(unflatBT(s + flatBT(Dpt(va, addBT(t3, multBT(Dpt(v0, t4), c)))) + b) == tMm
                   for c in range(1, 12)):
            ok = False
    if not ok:
        bad += 1
        if bad <= 3: print("  masterCF lhs_ex CEX:", M)
report("CondII_masterCF witnessed (RT)", fired, bad,
       "scb site not found on %d hosts" % noshape)

# --- operB_marked_scb_value / the exchII fold
fired = bad = 0
for M in RT_HOSTS:
    w = masterCF_witnesses(M)
    if w is None: continue
    s, b, va, v0, t3, t4 = w
    tM = T(M)
    for n in range(0, 4):
        lhs = operB(tM, n)
        rhs = to_b(unflatBT(s + flatBT(Dpt(va, addBT(t3, multBT(Dpt(v0, t4), n + 1)))) + b))
        fired += 1
        if lhs != rhs:
            bad += 1
            if bad <= 3: print("  operB_marked_scb_value CEX:", M, "n=", n)
report("operB_marked_scb_value_c2 (RT)", fired, bad)

# --- exchII conclusion itself on RT hosts
fired = bad = 0
for M in RT_HOSTS:
    tM = T(M)
    if tM is None: continue
    for n in NS:
        tMn = step(M, n)
        if tMn is None: continue
        fired += 1
        tgt = to_b(tMn)
        if not any(operB(tM, k) == tgt for k in range(0, 12)):
            bad += 1
            if bad <= 3: print("  exchII CEX:", M, "n=", n)
report("exchII conclusion (RT)", fired, bad)

# ------------------------------------------------------------------ summary
print()
print("%-34s %8s %6s  %s" % ("CLAIM", "FIRED", "BAD", "NOTE"))
print("-" * 78)
rc = 0
for (name, fired, bad, note) in results:
    flag = "CEX!!" if bad else ("OK" if fired else "VACUOUS")
    if bad: rc = 1
    print("%-34s %8d %6d  %s %s" % (name, fired, bad, flag, note))
print()
print("VERDICT: no counterexample." if rc == 0 else "VERDICT: COUNTEREXAMPLE FOUND.")
print("         condition (II) is EMPTY on ST_PS (%d/%d standard forms)" % (st_hosts, len(ST_POOL)))
print("         but NON-empty on RT_PS (%d hosts), where every claim holds." % len(RT_HOSTS))
sys.exit(rc)
