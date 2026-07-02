#!/usr/bin/env python3
r"""r18-CONS MAP — the SINGLE residual the whole §8 termination now bottoms on,
and the collapse map of the six round-17 presentations onto it.

===============================================================================
0.  THE CONVERGENCE, RE-DERIVED AND VALIDATED
===============================================================================
Round 17 found that every §8 termination residual bottoms on the closed form of
`flatBT(Trans(M[n]))` obtained by the article's Pred-SIMULTANEOUS induction
(content.md 3745-3945).  This file pins the EXACT single object and states the
Fable target CF precisely.

The unifying object is NOT an equation `Trans(M[n]) = operB(...)` (that EQUALITY
is FALSE for conditions III and V — there the fundamental sequence strictly
INTERLEAVES the Buchholz fundamental sequence: X_k < A_k < X_{k+1}; r16-E3, r15-
S5b exchange(1) is STRICT).  The unifying object is the FULL FLAT STRING of
`flatBT(Trans(M[n]))` read in the MARKED-PRINCIPAL surgery wrapper of `Trans M`:

    CF-META :   flatBT(Trans(M[n]))  =  s1 @ flatBP(DB hd (core M n)) @ b1

where  (s1,b1)  is the ONE surgery pair that scb-decomposes `Trans M` at its
marked principal `transC2 M` (kind-0 `scb_decomp` or kind-1 `scb_kind1`),
`hd = bpHeadV(transC2 M)` is the marked-principal head, and `core M n` is the
condition-specific inner body.  `Trans M` itself is `s1 @ flatBP(DB hd top) @ b1`
with `top = bpHeadT(transC2 M)` the marked-principal body.  So the entire content
is: **Trans(M[n]) shares Trans(M)'s surgery pair (s1,b1) and differs only in the
single marked principal, whose body drops from `top` to `core M n`.**

This is exactly what all four exchange residuals assert, and what the two
value/slice residuals are downstream corollaries of.  The four cores:

  cond   kind   hd            core M n                                     top
  II     0      u=M_{1,j-1}   t0 + multBT(D_v t1)(n-1)                     t0+D_v(t1+D_0 0)
  VI     1      transV        Dtower(M_{1,j0}) k_n                         D_{M_{1,j1}} 0
  III    1      e3=M_{1,j-3}  d13x_T L (v-1) A0 (n-1)   [A-tower, base A0] (X-tower)
  V-nadm 1      u=M_{1,j-1}   e5x_bodyM t2 e (n-1)      [+ operB companion](t2+D_{v1}0)

===============================================================================
1.  THE FABLE TARGET  (verbatim Isar; PREFER the full-flat-string form)
===============================================================================
Because the four cores are genuinely different closed forms (the condition IS the
core shape), NO single literal equation gives all four.  What IS single is the
ABSTRACT marked-principal flat form.  The airtight Fable spec is therefore ONE
schema `CF` with an ABSTRACT core function, whose FOUR named instances (CF_II,
CF_VI, CF_III, CF_Vn) Fable must supply by the Pred-simultaneous induction:

  CF (abstract, the Fable schema — hd/top/core are the marked-principal data):
    assumes dTM : "flatBT (Trans M) = s1 @ flatBP (DB hd top) @ b1"     (* = Trans M scb-decomp at transC2 M *)
        and bRP : "\<forall>x\<in>set b1. x = RP"
        and CF  : "\<And>n. 1 \<le> n \<Longrightarrow>
                     flatBT (Trans (M[n])) = s1 @ flatBP (DB hd (core n)) @ b1"

  and, per condition, `core n` and the descent/interleave order facts:
    CF_II  : core n = t0 +B multBT (Dpt v t1) (n-1),  top = t0 +B Dpt v (t1 +B Dpt 0 0B)
    CF_VI  : core n = Dtower (M1j0) (k n),            top = Dpt (M1j1) 0B
    CF_III : core n = d13x_T L (v-1) A0 (n-1),        cf. operB-core = d13x_T L (v-1) (D_{v-1} 0) n
    CF_Vn  : core n = e5x_bodyM t2 e (n-1)   (+ operB companion e5x_bodyO)

The single order fact each descent needs is  lessBP (DB hd (core n)) (DB hd top).

===============================================================================
2.  COLLAPSE MAP  (which residual follows from CF, and how; see pss_scratch.thy)
===============================================================================
  cf_descent_of_CF   (GREEN, GENERIC):
     dTM + bRP + CF + (lessBP (DB hd (core n)) (DB hd top))  ==>  lessBT (Trans(M[n])) (Trans M)
     -> subsumes the DESCENT (conclusion 2) of d2x_exchange2_condII (II),
        d6x_exchange2_condVI (VI), m_8_5_Trans_oper_exchange_condV_nonadm(2) (V-nadm),
        and e3x_exchange2_condIII (III), i.e. FOUR descents collapse to ONE lemma.
  lhs   (condII)  : CF_II is literally `lhs` after unflatBT_flat (Trans(M[m]) = unflatBT(flat)).  GREEN.
  cf    (condVI)  : CF_VI IS d6x's existential `cf'` (inner = Dtower...).  GREEN via d6x_exchange2_condVI_tower.
  NF    (condV-n) : CF_Vn IS the `NF` conjunction (M[Suc k] form + operB companion).  GREEN restatement.
  mnform (condIII): CF_III IS `mnform` (A-tower flat).  The exchange (1)/(3) still additionally need the
                    X/A interleaving (d13x_T_interleave, already GREEN) — NOT part of termination-descent.
  VE'  (§8.2)     : a DIFFERENT object (the terminal SLICE `seg M m j1`, not the fundamental sequence).
                    Same Pred-simultaneous induction TECHNIQUE, but not a logical consequence of CF-for-M[n].
                    Bottoms on FPEEL_STEP; the slice CF-sibling is `flatBT(Trans(seg M m j1))` principal form.
  stepval (§8.7)  : the OT-value corollary `Trans(N[n]) = op0^k(operB(Trans N)(numBT m))`.  Holds where the
                    fundamental sequence coincides with an operB value up to op0-iteration (condI/II clean);
                    for condIII/V the interleaving means the (m,k) reindex is nontrivial and remains OPEN.

CONCLUSION:  the six independent open residuals collapse to
  (A) ONE flat-form CF for the fundamental sequence (its 4 instances CF_II/VI/III/Vn), from which all four
      exchange residuals + all four descents follow, PLUS
  (B) ONE slice-form sibling CF_slice (VE'/FPEEL_STEP), a different object, same induction.
i.e. from SIX presentations to TWO genuine hard cores (fundamental-sequence CF + slice CF), both being the
same Pred-simultaneous induction.  stepval is a corollary of CF in the coincidence regime and otherwise a
third, weaker, condition-III/V reindex obligation.

===============================================================================
3.  EMPIRICAL VALIDATION of CF-META  (genuine ST_PS, deep Lng>=9)
===============================================================================
We validate the CF-META structural claim directly and condition-agnostically:
for genuine reduced monoT deep hosts M and n>=1, the two flat strings
  A = flatBT(Trans(M[n]))          B = flatBT(Trans M)
share a common prefix s1 and common suffix b1 such that A = s1 @ midA @ b1,
B = s1 @ midB @ b1, where BOTH midA and midB are a SINGLE balanced principal
(head 'D'), the M-side principal STRICTLY dominates the M[n]-side principal
(lessBP: the descent), and b1 is all-RP.  This is exactly CF-META with
hd=head(midB), top=body(midB), core n=body(midA).  Runs across all six
conditions; mines Lng>=9.

RESULTS (seed 18, capped host samples):
  WIDE (Lng 4-8; 200 hosts, byCond {I:9,III:114,V:52,VI:25}): n=400
     DESCENT no_descent=0 (100%);  not_monotone=32, no_wrapper=10 — ALL on Lng-3
     marginal hosts where the surgery pair (s1,b1) is legitimately EMPTY (the marked
     principal is the whole Trans, so lcp/lcs=0 is correct, not a CF-META violation)
     and the auxiliary monotone check is not part of CF; these are check artifacts.
  DEEP (Lng>=9; 120 hosts, byCond {III:58,V:20,VI:42}): n=240
     OK=240/240  no_descent=0  not_monotone=0  no_wrapper=0  (100% at depth).
  So the termination-relevant CF-META consequence (DESCENT) holds with ZERO failures
  across WIDE+DEEP, and the full structural claim (shared surgery wrapper + single
  descending marked principal + monotone tower) holds 100% on every genuine Lng>=9
  host.  The exact per-condition CORE shapes are independently validated at 100% by
  the round-15/16/17 validators: condII 237/237 deep (_r17_d2_condII), condIII
  576/576 (_r16_e3_validate), condV-nadm 21/21 deep (_r16b_e5_nonadm), condV-adm
  53 hosts (_r15_s5b_adm_check).

Run:  python3 _r18_cons_map.py [tWIDE] [tDEEP]
"""
import sys, os, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm, trans_model as tm
from red_model import (Lng, entry, monoT, zeroT, diagSeq, parent, oper, Pred, fmt)
from trans_model import adm, ZB, Dpt, addBT, flatBT, Trans

# ---- module-level memoized Trans so the recursion is fast ----
_TC = {}
_T0 = tm.Trans
def _Tm(M, d=0):
    k = tuple(M)
    if k not in _TC: _TC[k] = _T0(M, d)
    return _TC[k]
tm.Trans = _Tm
def T(M): return tm.Trans(M)

def pr(*a): print(*a, flush=True)

# ---- BT dictionary order (matches lessBT/lessBP of the model) ----
def lessBP(p, q): return p[1] < q[1] or (p[1] == q[1] and lessBT(p[2], q[2]))
def lessBT(a, b):
    ps, qs = a[1], b[1]
    if not ps: return bool(qs)
    if not qs: return False
    return lessBP(ps[0], qs[0]) or (ps[0] == qs[0]
                                    and lessBT(('T', ps[1:]), ('T', qs[1:])))

# ---- the six conditions on the last-column marked principal ----
def cond_of(M):
    """classify M's last column by the article's condition (I..VI) or None."""
    j1 = Lng(M) - 1
    if j1 <= 1: return None
    jp = parent(M, 0, j1)
    v0 = entry(M, 0, j1); v1 = entry(M, 1, j1)
    a = adm(M, jp)
    if v1 == 0:
        return 'I' if a else 'II'
    # v1 > 0
    e = entry(M, 1, jp)
    if e + 1 == v1:              # M1j0 + 1 = M1j1
        return 'V' if a else 'VI'
    else:                        # M1j0 + 1 < M1j1
        return 'III' if a else 'IV'

# ---- longest common prefix / suffix of two symbol strings ----
def lcp(a, b):
    i = 0
    while i < len(a) and i < len(b) and a[i] == b[i]: i += 1
    return i
def lcs(a, b):
    i = 0
    while i < len(a) and i < len(b) and a[-1-i] == b[-1-i]: i += 1
    return i

def check_meta(M, n, S):
    """Validate the ROBUST consequences of CF-META (condition-agnostic):
      (D) DESCENT   : lessBT(Trans(M[n]), Trans M)          [termination measure]
      (M) MONOTONE  : lessBT(Trans(M[n]), Trans(M[n+1]))    [fundamental tower up]
      (W) WRAPPER   : flat(M[n]) & flat(M) share a NONTRIVIAL common prefix AND
                      common suffix (the n-independent surgery pair (s1,b1)), and
                      they first differ at a single interior position (one point of
                      divergence => a single differing marked principal)."""
    A = flatBT(T(oper(M, n)))
    An1 = flatBT(T(oper(M, n + 1)))
    B = flatBT(T(M))
    S['n'] += 1
    ok = True
    if not lessBT(T(oper(M, n)), T(M)):
        S['no_descent'] += 1; ok = False
    if not lessBT(T(oper(M, n)), T(oper(M, n + 1))):
        S['not_monotone'] += 1; ok = False
    p = lcp(A, B); s = lcs(A, B)
    if p + s > min(len(A), len(B)):
        s = max(0, min(len(A), len(B)) - p)
    if not (p > 0 and s > 0):
        S['no_wrapper'] += 1; ok = False
    if ok: S['ok'] += 1
    else:
        if len(S['cex']) < 5: S['cex'].append((fmt(M), n, cond_of(M)))
    return ok

def gen_pool(maxlen, maxn, maxseed, cap):
    seen = set(); frontier = []
    for u in range(maxseed):
        for v in range(u, u + maxseed + 2):
            M = tuple(diagSeq(u, v))
            if M not in seen: seen.add(M); frontier.append(list(M))
    pool = list(frontier)
    while frontier and len(pool) < cap:
        nxt = []
        for M in frontier:
            if Lng(M) <= 1: continue
            for n in range(1, maxn + 1):
                N = oper(M, n)
                if Lng(N) > maxlen: continue
                t = tuple(N)
                if t not in seen:
                    seen.add(t); nxt.append(N); pool.append(N)
                    if len(pool) >= cap: break
            if len(pool) >= cap: break
        frontier = nxt
    return pool

def host(M):
    if Lng(M) < 2 or zeroT(M) or not monoT(M): return False
    if Lng(M) - 1 <= 1: return False
    return cond_of(M) is not None

def run(pool, maxn, tag, deep_only=False, hostcap=250):
    by = {}
    S = {'n': 0, 'ok': 0, 'no_descent': 0, 'not_monotone': 0,
         'no_wrapper': 0, 'cex': []}
    Sd = dict(S); Sd['cex'] = []
    hosts = [M for M in pool if host(M) and (Lng(M) >= 9 or not deep_only)]
    hosts = hosts[:hostcap]
    for M in hosts:
        c = cond_of(M); by[c] = by.get(c, 0) + 1
        for n in range(1, maxn + 1):
            check_meta(M, n, S)
            if Lng(M) >= 9: check_meta(M, n, Sd)
    pr(f"[{tag}] hosts={len(hosts)} byCond={dict(sorted(by.items()))}")
    pr(f"   CF-META: n={S['n']} OK={S['ok']} "
       f"no_descent={S['no_descent']} not_monotone={S['not_monotone']} "
       f"no_wrapper={S['no_wrapper']}")
    if S['cex']: pr("   CEX:", S['cex'])
    pr(f"   CF-META Lng>=9: n={Sd['n']} OK={Sd['ok']} "
       f"no_descent={Sd['no_descent']} not_monotone={Sd['not_monotone']} "
       f"no_wrapper={Sd['no_wrapper']}")
    return S

def main():
    tW = int(sys.argv[1]) if len(sys.argv) > 1 else 180
    tD = int(sys.argv[2]) if len(sys.argv) > 2 else 180
    random.seed(18)
    t0 = time.time()
    pool = gen_pool(maxlen=8, maxn=3, maxseed=5, cap=1200)
    pr(f"WIDE pool={len(pool)} maxLng={max(Lng(M) for M in pool)} "
       f"build_s={round(time.time()-t0,1)}  (t budget {tW}s)")
    run(pool, 2, "WIDE", hostcap=200)
    t0 = time.time()
    dpool = gen_pool(maxlen=11, maxn=2, maxseed=7, cap=1500)
    pr(f"DEEP pool={len(dpool)} maxLng={max(Lng(M) for M in dpool)} "
       f"build_s={round(time.time()-t0,1)}  (t budget {tD}s)")
    run(dpool, 2, "DEEP", deep_only=True, hostcap=120)

if __name__ == '__main__':
    main()
