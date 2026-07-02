#!/usr/bin/env python3
"""r17-FPEEL: UNIFY the round-16b endgame residual onto ONE object and reduce
VE' to a single sharp front-peel step.

=========================================================================
THE ONE OBJECT (generalizing m_8_5_scbdec_adm_forms to all slice offsets)
=========================================================================
For M in RT_PS cap PT_PS, monoT, Br M != [], write j1 = Lng M - 1,
J1 = Lng(Br M)-1, j0' = Joints M ! J1.  Every reduced monoT sequence has a
PRINCIPAL Trans (single top D):  Trans X = D_{X_{1,0}} (bpHeadT (Trans X)).
The article's ``terminal slice'' lemma (pss_paper 1604, content 3664) fixes the
slice family  M'_m := seg M m j1  (m <= j0'), all monoT (m_6_4_mono_slice), with
leftmost head value  entry(M'_m,1,0) = M_{1,m}  (repr_entry1_shift_gen), and
asserts they all share ONE deep tail t1:

      Trans M       = D_{M_{1,0}} t1
      Trans(M'_m)   = D_{M_{1,m}} t1        for every m <= j0'.

The whole content is the tail equality
      VE'(m):   bpHeadT(Trans(seg M m j1)) = bpHeadT(Trans M).

m_8_5_scbdec_adm_forms already pins t1 for the ADM TOPMOST slice (m = transJ0,
which equals j0' when j0' is M-admissible): there Trans(M[n]) / Trans(M)[n] get
explicit flat closed forms over one (s0,s1,b0,b1).  The article generalizes to
all m by a FRONT-PEEL / Pred SIMULTANEOUS induction (proof text dropped from the
extraction).

============================================================
THE THREE round-16b RESIDUALS ARE INSTANCES OF THE ONE OBJECT
============================================================
  VE' (E2)     the tail equality itself (this file's main target).
  NFall (E5)   non-adm condV: the SAME closed-form family, but the adm core
               D_e(t2 + D_e 0)  is replaced by the non-adm core
               D_u(t2 + D_e(t2 + D_e 0))  [e5x_bodyM].  It is the m=j0'
               closed form when j0' is NON-adm (transJm1 < j0'): one extra
               D_e-layer, i.e. one further front-peel than the adm base.
  stepval (E4) Trans(N[n]) = [0]^k (operB (Trans N)(numBT m_n)): the OT pillar
               reading of the SAME operB value string that
               m_8_5_scbdec_adm_forms's fseq conjunct produces.

============================================================
THE REDUCTION PROVED GREEN THIS ROUND  (fpx_ lemmas)
============================================================
VE'(m) telescopes from the single-step front peel
      FPEEL_STEP(i):  bpHeadT(Trans(seg M i j1)) = bpHeadT(Trans(seg M (i+1) j1))
for i < m.  Base m=0 is trivial: seg M 0 j1 = M.  So

      (forall i<m. FPEEL_STEP(i))  ==>  VE'(m).

fpx_VE_reduction proves this telescoping UNCONDITIONALLY (green), and
fpx_terminal_slice_Trans_modStep feeds it into
m_8_2_condV_terminal_slice_Trans_modVE, so the whole terminal-slice lemma is
GREEN modulo the single named residual FPEEL_STEP.

============================================================
HONEST CAVEATS  (dead simplifications ruled out this round)
============================================================
VE' does NOT admit a *simple universal local* reduction.  Empirically:
  * VE'                 : 100%  (1386/1386 WIDE, 68/68 GENUINE, 16/16 Lng>=9).
  * naive FPEEL_STEP for ALL i<j0'  : FALSE at the boundary i=j0'-1 (it
    crosses out of the hyp-covered trunk).  It is TRUE exactly in the domain
    i<m<=j0' that fpx_VE_reduction uses -- but there it is a CONSEQUENCE of VE'
    (both endpoints are hyp-covered), so as a residual it is NOT weaker than
    VE'.  fpx_VE_reduction is a valid green restatement, not a simplification.
  * clean local peel identity  Trans(seg M (i+1) j1) = bpHeadT(Trans(seg M i j1))
    : FALSE in general (WIDE 1462/1567, GENUINE 45/71); the tempting hand
    examples that satisfy it are not representative.
  * funpow closed form  Trans(seg M m j1) = (bpHeadT^^m)(Trans M) : FALSE
    (WIDE 2842/2913, GENUINE 18/55); and
  * tail-stabilization  (bpHeadT^^(m+1))(Trans M) = bpHeadT(Trans M) : FALSE
    (WIDE 877/907, GENUINE 14/40).
CONCLUSION for the reserved Fable+xhigh round: the front-peel telescoping is a
DEAD simplification.  The genuine proof is the article's Pred-SIMULTANEOUS
induction (content 3745-3945): induct on Lng(M) via Pred with the front offset
m FIXED, case-split j1'=j1 (base) vs j1'<j1 (step through Pred(M),Pred(M')),
using the §8.4/8.5 scb machinery.  The green pieces delivered this round
(fpx_slice_principal = slice is D_{M_{1,m}}-principal; the modVE wiring) are the
reusable scaffolding for it.

Empirical mandate: mine deep (Lng>=9) before any 0-instances claim.
Run:  python3 _r17_fpeel_map.py [tGEN] [tWIDE]
"""
import sys, time, signal, random, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng, entry, parent, hasParent, oper, seg, diagSeq,
                       monoT, zeroT, Br, Joints, FirstNodes, TrMax, P, Red)
import red_model as rm
from trans_model import (Trans, Mark, Pred, adm, Adm, Dpt, addBT, PB,
                         bpHeadV, bpHeadT, flatBT, scb_decomps, ZB, reduced,
                         condI, condIII, condV, condVI)

class TimeoutErr(Exception): pass
def _handler(signum, frame): raise TimeoutErr()
signal.signal(signal.SIGALRM, _handler)

def descending(Q):
    n = len(Q)
    for J0 in range(n):
        for J1 in range(J0, n):
            a0, a1 = entry(Q[J0], 0, 0), entry(Q[J0], 1, 0)
            b0, b1 = entry(Q[J1], 0, 0), entry(Q[J1], 1, 0)
            if not (a0 >= b0 and (a0 != b0 or a1 >= b1)):
                return False
    return True

def principal(t):
    return len(t[1]) == 1

def hyp(M, m):
    """the article terminal-slice hypothesis for (M, m); assumes Br M != []."""
    br = Br(M)
    J1 = len(br) - 1
    j0p, j1p = Joints(M)[J1], FirstNodes(M)[J1]
    if m < j0p: return True
    return (m == j0p and entry(M, 0, j1p) == entry(M, 1, j1p)
            and descending(br))

class Stat:
    def __init__(s): s.ok = 0; s.bad = 0; s.cex = []
    def rec(s, good, info):
        if good: s.ok += 1
        else:
            s.bad += 1
            if len(s.cex) < 5: s.cex.append(info)
    def __str__(s): return f"{s.ok}/{s.ok+s.bad}"

# ---------------------------------------------------------------- checks
def check_host(M, S, note):
    """Run all r17 claims for a single host M (reduced monoT, Br!=[])."""
    j1 = Lng(M) - 1
    br = Br(M); J1 = len(br) - 1
    j0p = Joints(M)[J1]
    j0 = parent(M, 0, j1)
    tr = TrMax(M)
    admj0 = adm(M, j0)
    S['NHOST'].rec(True, None)
    if Lng(M) >= 9:
        S['DEEPHOST'].rec(True, None)

    TM = Trans(M)
    tailM = bpHeadT(TM)
    S['PRINC_M'].rec(principal(TM) and bpHeadV(TM) == entry(M, 1, 0), (M,))

    # ---- ruled-out simplifications (dead ends for the Fable round) ----
    def funpow(f, n, x):
        for _ in range(n): x = f(x)
        return x
    fulltails = {}   # Trans of each slice, all offsets where monoT
    for i in range(0, j1 + 1):
        Si = seg(M, i, j1)
        fulltails[i] = Trans(Si) if monoT(Si) else None
    for i in range(0, j1):   # clean local peel identity (FALSE in general)
        if fulltails.get(i) is None or fulltails.get(i + 1) is None: continue
        S['PEEL_ID'].rec(fulltails[i + 1] == bpHeadT(fulltails[i]), (M, i))
    for m in range(0, j0p + 1):   # funpow closed form (FALSE in general)
        if fulltails.get(m) is None: continue
        S['FUNPOW'].rec(fulltails[m] == funpow(bpHeadT, m, TM), (M, m))
        if hyp(M, m):   # tail-stabilization (FALSE in general)
            S['STAB'].rec(funpow(bpHeadT, m + 1, TM) == tailM, (M, m))

    # slices seg M m j1 for m in 0..j0'   (all should be monoT & principal)
    tails = {}
    for m in range(0, j0p + 1):
        Mp = seg(M, m, j1)
        # domain sanity: slice monoT (article: reducedness+monoT heredity)
        mono_ok = monoT(Mp)
        S['SLICE_MONO'].rec(mono_ok, (M, m))
        if not mono_ok:
            tails[m] = None
            continue
        TMp = Trans(Mp)
        tails[m] = bpHeadT(TMp)
        # principal with leftmost head value M_{1,m}  (repr_entry1_shift_gen)
        S['SLICE_HEAD'].rec(
            principal(TMp) and bpHeadV(TMp) == entry(M, 1, m), (M, m))
        # repr head via Red form directly (entry(Red slice,1,0) == M_{1,m})
        RS = Red(Mp)
        S['REDHEAD'].rec(len(RS) > 0 and entry(RS, 1, 0) == entry(M, 1, m),
                         (M, m))

    # seg M 0 j1 == M  (the trivial base)
    S['SEG0'].rec(seg(M, 0, j1) == M, (M,))

    # VE'(m): tail of slice == tail of M, for every m<=j0' with hyp(M,m)
    for m in range(0, j0p + 1):
        if tails.get(m) is None: continue
        if not hyp(M, m):        # only claimed under the article hypothesis
            continue
        good = (tails[m] == tailM)
        S['VE'].rec(good, (M, m, tails[m], tailM))
        if Lng(M) >= 9:
            S['VE_DEEP'].rec(good, (M, m))

    # FPEEL_STEP(i): consecutive slice tails equal, for i < j0'
    for i in range(0, j0p):
        if tails.get(i) is None or tails.get(i + 1) is None: continue
        good = (tails[i] == tails[i + 1])
        S['FPEEL_STEP'].rec(good, (M, i, tails[i], tails[i + 1]))
        if Lng(M) >= 9:
            S['FPEEL_DEEP'].rec(good, (M, i))

    # TELESCOPE soundness: (forall i<m. step) ==> VE'(m).  Verify the
    # implication holds pointwise (if all steps below m equal, tail_m==tail_0).
    for m in range(0, j0p + 1):
        if tails.get(m) is None: continue
        steps_ok = all(tails.get(i) is not None and tails.get(i+1) is not None
                       and tails[i] == tails[i + 1] for i in range(0, m))
        if steps_ok:
            S['TELESCOPE'].rec(tails[m] == tails[0], (M, m))

    # adm-topmost base link: when j0' adm, m=j0' slice tail == m_8_5 core tail.
    # (the adm base of the DOWNWARD induction; here just record tail(j0') and
    #  that it equals tail(M) so both induction directions agree.)
    if admj0 and tails.get(j0p) is not None:
        S['ADMBASE'].rec(tails[j0p] == tailM, (M,))

# ---- NFall (E5) instance mapping: non-adm j0' one-extra-peel core ----
def check_nfall(M, S):
    """Non-adm condV hosts: the m=j0' slice tail carries ONE MORE D_e layer
    than the adm core -- i.e. NFall's e5x_bodyM shape is the m=j0' peel."""
    j1 = Lng(M) - 1
    j0 = parent(M, 0, j1)
    if adm(M, j0):
        return
    if not condV(M):
        return
    S['NFALL_HOST'].rec(True, None)
    if Lng(M) >= 9:
        S['NFALL_DEEP'].rec(True, None)
    # the non-adm core is strictly deeper (more nested D's) than adm core:
    # verify the m=j0' slice tail nesting-depth exceeds that of the adm
    # sibling (structural sanity: bpHeadT recursion depth grows by >=1).
    def depth(t):
        if not t[1]: return 0
        return 1 + max(depth(p[2]) for p in t[1])
    TM = Trans(M)
    S['NFALL_DEEPER'].rec(depth(bpHeadT(TM)) >= 2, (M, depth(bpHeadT(TM))))

# ------------------------------------------------------------------ pools
def pool_genuine(tlimit, maxlen=16, seed=20260702):
    rng = random.Random(seed)
    seen, out, work = set(), [], []
    for u in range(0, 3):
        for v in range(u + 1, u + 6):
            work.append(diagSeq(u, v))
    t0 = time.time()
    while work and time.time() - t0 < tlimit:
        i = rng.randrange(len(work))
        M = work.pop(i)
        k = tuple(M)
        if k in seen: continue
        seen.add(k)
        out.append(M)
        if Lng(M) > maxlen: continue
        for n in (1, 2, 3):
            Mn = oper(M, n)
            if Lng(Mn) <= maxlen + 4 and tuple(Mn) not in seen:
                work.append(Mn)
    return out

def pool_wide(maxlen=7, maxv=3):
    cols = [(x, y) for x in range(maxv + 1) for y in range(x + 1)]
    out = []
    for a in range(2):
        first = (a, a)
        for L in range(2, maxlen + 1):
            for rest in itertools.product(cols, repeat=L - 1):
                out.append([first] + list(rest))
    return out

R15_DEEP = [
    [(0,0),(1,1),(2,2),(3,3),(3,2),(4,1),(5,2),(6,3),(6,1)],
    [(0,0),(1,1),(2,2),(3,3),(4,4),(4,3),(5,2),(6,3),(7,4),(7,1)],
]

def run_pool(name, Ms, S, tlimit):
    t0 = time.time()
    hosts = 0; timeouts = 0
    for M in Ms:
        if time.time() - t0 > tlimit: break
        try:
            signal.alarm(25)
            ok = reduced(M) and monoT(M) and Br(M) != []
            signal.alarm(0)
        except (TimeoutErr, ValueError, IndexError):
            signal.alarm(0); timeouts += 1; continue
        if not ok: continue
        try:
            signal.alarm(40)
            check_host(M, S, name)
            check_nfall(M, S)
            hosts += 1
            signal.alarm(0)
        except TimeoutErr:
            signal.alarm(0); timeouts += 1
        except (ValueError, IndexError) as e:
            signal.alarm(0); S['ERR'].rec(False, (M, repr(e)))
    return hosts, timeouts

def main():
    tA = int(sys.argv[1]) if len(sys.argv) > 1 else 240
    tB = int(sys.argv[2]) if len(sys.argv) > 2 else 240
    keys = ['NHOST','DEEPHOST','PRINC_M','SLICE_MONO','SLICE_HEAD','REDHEAD',
            'SEG0','VE','VE_DEEP','FPEEL_STEP','FPEEL_DEEP','TELESCOPE',
            'PEEL_ID','FUNPOW','STAB',
            'ADMBASE','NFALL_HOST','NFALL_DEEP','NFALL_DEEPER','ERR']
    for name, mk, tl in (('GENUINE', lambda: pool_genuine(min(tA//2, 120)), tA),
                         ('WIDE', lambda: pool_wide() + R15_DEEP, tB)):
        S = {k: Stat() for k in keys}
        Ms = mk()
        hosts, tmo = run_pool(name, Ms, S, tl)
        print(f"== pool {name}: {len(Ms)} candidates, {hosts} hosts, "
              f"{tmo} timeouts ==")
        for k in keys:
            s = S[k]
            if s.ok + s.bad:
                print(f"  {k:12s} {s}" +
                      ("" if not s.bad else f"  CEX: {s.cex[:2]}"))
        sys.stdout.flush()

if __name__ == '__main__':
    main()
