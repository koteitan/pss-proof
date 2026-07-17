#!/usr/bin/env python3
"""Adversarial audit for lean/8/8.3-condII-masterCF.lean.

THE QUESTION THIS SCRIPT EXISTS TO ANSWER
-----------------------------------------
The built «8».«8.3-TransCondII-engine» declares

    def CondII_masterCF : Prop :=
      forall M, RTPS M -> monoT M -> 1 < Lng M - 1 -> transCondII M -> <witnesses>

i.e. on RT_PS and with NO tail-value hypothesis.  The Isabelle original

    c2sx_condII_masterCF   (isabelle/layerB/pss_wip.thy:87430)

carries the EXTRA hypothesis  TV : c2sx_tailval M,  and TV's only discharger

    y3j_condII_tailval     (isabelle/layerC/pss_scratch.thy:17079)
      assumes MST: "M : ST_PS" ...

needs M in ST_PS, NOT M in RT_PS.  So the Lean Prop as declared is NOT
underwritten by the Isabelle corpus at RT_PS level.  Either
  (a) c2sx_tailval happens to hold on all of RT_PS (Prop true, chain portable
      only after strengthening y3j_condII_tailval from ST_PS to RT_PS), or
  (b) it fails somewhere on RT_PS (Prop FALSE as declared => undischargeable).

Semantics: python/red_model.py + python/trans_model.py (the canonical models).

Definitions mirrored 1:1 from pss_wip.thy:86431-86451:
    c2sx_pj M      = PB (transT2 M) ! (Lng (PB (transT2 M)) - 1)
    c2sx_ldj M    <-> bpHeadV (c2sx_pj M) = enat (entry M 1 (transJ0 M))
    c2sx_t3 M      = if ldj then SigmaB (take (len-1) (PB (transT2 M))) else transT2 M
    c2sx_t4 M      = if ldj then bpHeadT (c2sx_pj M) else transT2 M
    c2sx_tailval M <-> Trans (seg M (parent M 0 (Lng M-1)) (Lng M-2))
                       = Dpt (enat (entry M 1 (parent M 0 (Lng M-1)))) (c2sx_t4 M)

Exit code 0 = no counterexample found.
"""
import sys, os, itertools

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.setrecursionlimit(100000)

from red_model import (Lng, entry, parent, monoT, oper, diagSeq, seg)
from trans_model import (Trans, Mark, Adm, adm, ZB, Dpt, addBT, PB, SigmaB,
                         bpHeadV, bpHeadT, flatBT, unflatBT, scb_decomps,
                         reduced, Pred)

# ------------------------------------------------------- Isabelle transJ/transC
def transJ1(M): return Lng(M) - 1
def transJ0(M): return parent(M, 0, Lng(M) - 1)
def transJm1(M): return Adm(M, transJ0(M))
def transC1(M): return Mark(Pred(M), transJm1(M))
def transT2(M): return bpHeadT(transC1(M))

def condII(M):
    j1 = Lng(M) - 1
    jp = parent(M, 0, j1)
    if jp is None:
        return False
    return entry(M, 1, j1) == 0 and not adm(M, jp)

# ------------------------------------------------------- the c2sx branch data
def c2sx_pj(M):
    ps = PB(transT2(M))
    return ps[len(ps) - 1] if ps else ZB   # Isabelle `!` on [] is unspecified

def c2sx_ldj(M):
    return bpHeadV(c2sx_pj(M)) == entry(M, 1, transJ0(M))

def c2sx_t3(M):
    t2 = transT2(M)
    if c2sx_ldj(M):
        ps = PB(t2)
        return SigmaB(ps[:len(ps) - 1])
    return t2

def c2sx_t4(M):
    return bpHeadT(c2sx_pj(M)) if c2sx_ldj(M) else transT2(M)

def c2sx_W(M):
    """the appended block's tail-slice value  W = Trans (seg M j0 (Lng M - 2))"""
    return Trans(seg(M, transJ0(M), Lng(M) - 2))

def c2sx_tailval(M):
    return c2sx_W(M) == Dpt(entry(M, 1, transJ0(M)), c2sx_t4(M))

def multBT(t, k):
    out = ZB
    for _ in range(k):
        out = addBT(out, t)
    return out

# ------------------------------------------------------- pools
def build_rt_hosts(cap, lmax):
    """brute-force reduced/monoT condition-(II) hosts, components in [0,cap)."""
    hosts = []
    for L in range(3, lmax + 1):
        # column 0 of a reduced sequence is always (0,0)
        for tail in itertools.product(range(0, cap), repeat=2 * (L - 1)):
            M = [(0, 0)] + [(tail[2 * i], tail[2 * i + 1]) for i in range(L - 1)]
            if not (1 < Lng(M) - 1):
                continue
            if entry(M, 1, Lng(M) - 1) != 0:      # cheap condII prefilter
                continue
            try:
                if not reduced(M) or not monoT(M):
                    continue
                if not condII(M):
                    continue
            except Exception:
                continue
            hosts.append(M)
        print("   L=%d cumulative RT condII hosts: %d" % (L, len(hosts)))
    return hosts

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
                try:
                    Mn = oper(M, n)
                except Exception:
                    continue
                if Mn and Lng(Mn) <= cap and tuple(Mn) not in seen:
                    seen.add(tuple(Mn)); pool.append(Mn); nx.append(Mn)
        fr = nx
        if not fr:
            break
    return pool

FULL = bool(os.environ.get("PSS_AUDIT_FULL"))
CAP = 7 if FULL else 6            # memo: do NOT scan components < 3
LMAX = 6 if FULL else 5

print("=" * 78)
print("RT_PS condition-(II) hosts (brute force, components < %d, Lng <= %d)"
      % (CAP, LMAX))
print("=" * 78)
RT_HOSTS = build_rt_hosts(CAP, LMAX)
print("hosts:", len(RT_HOSTS))
for M in RT_HOSTS:
    print("   ", M, " ldj =", c2sx_ldj(M))
print()

fails = 0

# ---- (1) THE RESIDUAL: does c2sx_tailval hold on RT_PS?
print("=" * 78)
print("(1) c2sx_tailval on RT_PS condition-(II) hosts")
print("    (Isabelle proves this only for ST_PS: y3j_condII_tailval, MST : M in ST_PS)")
print("=" * 78)
tv_ok = tv_bad = 0
for M in RT_HOSTS:
    try:
        ok = c2sx_tailval(M)
    except Exception as e:
        print("   EXC", M, e); continue
    if ok:
        tv_ok += 1
    else:
        tv_bad += 1
        print("   CEX tailval FAILS:", M)
        print("      W  =", c2sx_W(M))
        print("      D  =", Dpt(entry(M, 1, transJ0(M)), c2sx_t4(M)))
        print("      ldj=", c2sx_ldj(M), " t2 =", transT2(M))
print("   holds: %d   fails: %d" % (tv_ok, tv_bad))
fails += tv_bad

# ---- (2) the masterCF conclusion itself, with the Isabelle witnesses
print()
print("=" * 78)
print("(2) CondII_masterCF conclusion with Isabelle witnesses")
print("    s,b = scb of transC1 in Trans(Pred M);  u=va, v=v0, t0=t3, t1=t4")
print("=" * 78)
MS = [2, 3, 4]
cf_ok = cf_bad = cf_skip = 0
for M in RT_HOSTS:
    try:
        va = entry(M, 1, transJm1(M))
        v0 = entry(M, 1, transJ0(M))
        t3, t4 = c2sx_t3(M), c2sx_t4(M)
        # dM : scb_decomp (Trans M) s (flatBT (Dpt va (t3 + Dpt v0 (t4 + Dpt 0 0)))) b
        c2 = Dpt(va, addBT(t3, Dpt(v0, addBT(t4, Dpt(0, ZB)))))
        ds = scb_decomps(Trans(M), flatBT(c2))
        if not ds:
            cf_skip += 1
            print("   SKIP (no scb of the c2 shape in Trans M):", M)
            continue
        s1, b1 = ds[0]
        good = True
        for m in MS:
            Mm = oper(M, m)
            if not Mm or Lng(Mm) > 16:
                continue
            Tm = Trans(Mm)
            hit = None
            for c in range(1, 8):
                cand = unflatBT(s1 + flatBT(Dpt(va, addBT(t3, multBT(Dpt(v0, t4), c)))) + b1)
                if cand == Tm:
                    hit = c
                    break
            if hit is None:
                good = False
                print("   CEX lhs_ex FAILS: M=%s m=%d" % (M, m))
                break
        if good:
            cf_ok += 1
        else:
            cf_bad += 1
    except Exception as e:
        print("   EXC", M, e)
        cf_skip += 1
print("   holds: %d   fails: %d   skipped: %d" % (cf_ok, cf_bad, cf_skip))
fails += cf_bad

# ---- (2b) NON-VACUITY of CondII_step (the 1st of the two residuals)
# A hypothesis Prop that is unsatisfiable would make condII_masterCF_of_tailval
# worthless.  Check the invariant it asserts on real hosts:
#   Mark (M[n]) jm1 = D_va (t2 +B W*(n-1))  AND  the scb of Trans (M[n]) at it
print()
print("=" * 78)
print("(2b) CondII_step non-vacuity: the double-track invariant on RT_PS hosts")
print("=" * 78)
sv_ok = sv_bad = sv_skip = 0
for M in RT_HOSTS:
    try:
        jm1 = transJm1(M)
        va = entry(M, 1, jm1)
        t2 = transT2(M)
        W = c2sx_W(M)
        # (s1,b1) = scb of c1 = Mark (Pred M) jm1 inside Trans (Pred M)
        c1 = Mark(Pred(M), jm1)
        ds = scb_decomps(Trans(Pred(M)), flatBT(c1))
        if not ds:
            sv_skip += 1
            continue
        s1, b1 = ds[0]
        for n in (2, 3):
            Mn = oper(M, n)
            if not Mn or Lng(Mn) > 16:
                continue
            lhs = Mark(Mn, jm1)
            rhs = Dpt(va, addBT(t2, multBT(W, n - 1)))
            if lhs != rhs:
                sv_bad += 1
                print("   CEX step-INV mark: M=%s n=%d" % (M, n))
                print("      Mark(M[n],jm1) =", lhs)
                print("      D_va(t2+W*(n-1)) =", rhs)
                break
            # and the scb track: Trans(M[n]) = s1 ++ flat(rhs) ++ b1
            if flatBT(Trans(Mn)) != s1 + flatBT(rhs) + b1:
                sv_bad += 1
                print("   CEX step-INV scb: M=%s n=%d" % (M, n))
                break
        else:
            sv_ok += 1
    except Exception as e:
        print("   EXC", M, e)
        sv_skip += 1
print("   holds: %d   fails: %d   skipped: %d" % (sv_ok, sv_bad, sv_skip))
print("   => CondII_step is NOT vacuous (its conclusion is true on real hosts)"
      if sv_ok and not sv_bad else "   => CHECK THE STATEMENT")
fails += sv_bad

# ---- (3) vacuity re-check on ST_PS (corroborate the engine header)
print()
print("=" * 78)
print("(3) condition (II) on ST_PS (vacuity re-check)")
print("=" * 78)
ST_POOL = (build_st_pool(5, 8, [1, 2, 3, 4, 5], 8, 16) if FULL
           else build_st_pool(4, 6, [1, 2, 3, 4], 6, 12))
st_hosts = [M for M in ST_POOL if (parent(M, 0, Lng(M) - 1) is not None and condII(M))]
print("   standard forms scanned :", len(ST_POOL))
print("   max component          :", max(max(max(a, b) for (a, b) in M) for M in ST_POOL))
print("   condition-(II) hosts   :", len(st_hosts))
print("   => condII EMPTY on this ST_PS pool" if not st_hosts
      else "   => condII occurs on ST_PS!")

print()
print("=" * 78)
print("RESULT: %s" % ("NO COUNTEREXAMPLE" if fails == 0 else "%d FAILURE(S)" % fails))
print("=" * 78)
sys.exit(1 if fails else 0)
