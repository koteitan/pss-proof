#!/usr/bin/env python3
"""Re-verification of corrections A29 / A33 / A34 / A37 / A38 under the CORRECTED
Buchholz fundamental sequence (footnote [30] read as x_i = D_u b[x_{i-1}],
a[n] = D_v b[x_n]; see _r56_operBfix_lib and pss_paper.thy 761-780).

All five entries had been verified against the OLD (wrong) operB.
Every count below is reported with its NON-VACUOUS exercise count.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _r56_operBfix_lib as fx          # patches vx.operB / vx.xseq / vx.operB_iter0
from _r56_operBfix_lib import operB, operB_iter0
import _r15_vx_lib as vx
from _r15_vx_lib import (gen_pool, mono_hosts, internals, Trans, condII, condIV,
                         numBT, lessBT, guarded, SKIP)
from red_model import (Lng, entry, oper, parent, hasParent, monoT, fmt, funpow,
                       diagSeq, P, multiT)
import red_model as rm
from trans_model import (Dpt, ZB, flatBT, scb_decomps, adm, Adm, Pred, reduced,
                         condIII, condV, condVI)

MAXN = 3

_opm = {}
def OPER(M, n):
    k = (tuple(M), n)
    if k not in _opm:
        _opm[k] = guarded(oper, M, n, budget=10)
    return _opm[k]


print("building genuine ST_PS pool (diagSeq seeds, oper closure) ...")
pool = gen_pool(maxlen=8, maxn=3, maxseed=3, cap=1500)
hosts = mono_hosts(pool)
print(f"pool={len(pool)} mono ST_PS hosts={len(hosts)}\n")


def sprime(M, iv):
    """(s'_1, b'_1) from part (1): (D_{M1,j-1} s'_1, D_{M1,j1} 0, b'_1) is an scb
    decomposition of c2."""
    center = flatBT(Dpt(entry(M, 1, iv['j1']), ZB))
    for (s, b) in scb_decomps(iv['c2'], center):
        if s and s[0] == ('D', entry(M, 1, iv['jm1'])):
            return s[1:], b
    return None


def rep(xs, n): return list(xs) * n


# ---------------------------------------------------------------- A29 (§8.5 (5))
def a29():
    lit = lit_t = ours = ours_t = 0
    p4 = p4_t = 0
    cex_lit = cex_ours = None
    for M in hosts:
        if Lng(M) < 3 or not reduced(M) or not monoT(M): continue
        if not condV(M): continue
        iv = guarded(internals, M, budget=20)
        if iv is SKIP or iv is None or iv['s1'] is None: continue
        j1, j0, jm1 = iv['j1'], iv['j0'], iv['jm1']
        if j1 <= 1 or adm(M, j0): continue         # condV + j0 NON-admissible
        sb = sprime(M, iv)
        if sb is None: continue
        s1p, b1p = sb
        s1, b1, t2 = iv['s1'], iv['b1'], iv['t2']
        Dm1 = ('D', entry(M, 1, jm1)); Dj0 = ('D', entry(M, 1, j0))
        for n in range(1, MAXN + 1):
            Mn = OPER(M, n)
            if Mn is SKIP: continue
            T = guarded(Trans, Mn, budget=30)
            if T is SKIP: continue
            f = flatBT(T)
            def form(e):
                return (list(s1) + [Dm1] + rep(list(s1p) + [Dj0], e)
                        + flatBT(t2) + rep(b1p, e) + list(b1))
            lit_t += 1
            if f == form(n): lit += 1
            elif cex_lit is None: cex_lit = (fmt(M), n)
            ours_t += 1
            if f == form(n - 1): ours += 1
            elif cex_ours is None: cex_ours = (fmt(M), n)
            # part (4): Trans(L_n) = s1 D_{jm1} (s'1 D_{j0})^{n+1} 0 (b'1)^{n+1} b1
            Ln = list(Mn) + [(entry(M, 0, j0) + n * (entry(M, 0, j1) - entry(M, 0, j0)),
                              entry(M, 1, j0))]
            TL = guarded(Trans, Ln, budget=30)
            if TL is not SKIP:
                p4_t += 1
                want = (list(s1) + [Dm1] + rep(list(s1p) + [Dj0], n + 1)
                        + flatBT(ZB) + rep(b1p, n + 1) + list(b1))
                if flatBT(TL) == want: p4 += 1
    print("== A29  §8.5 lemma (V) part (5)  [non-vacuous instances: %d]" % lit_t)
    print("   article LITERAL  exponent n   : %d/%d  %s" % (lit, lit_t, cex_lit or ''))
    print("   our 'correction' exponent n-1 : %d/%d  %s" % (ours, ours_t, cex_ours or ''))
    print("   part (4) LITERAL exponent n+1 : %d/%d" % (p4, p4_t))


# ---------------------------------------------------------------- A33 (§8.4 (2))
def a33():
    c1 = c1t = c2 = c2t = c3 = c3t = 0
    cex2 = None
    alt = {}
    for M in hosts:
        if Lng(M) < 3 or not reduced(M) or not monoT(M): continue
        if not (condIII(M) or condIV(M)): continue
        iv = guarded(internals, M, budget=20)
        if iv is SKIP or iv is None: continue
        j1 = iv['j1']
        if j1 <= 1 or not hasParent(M, 1, j1): continue
        jm2 = parent(M, 1, j1)
        TM = guarded(Trans, M, budget=30)
        if TM is SKIP: continue
        for n in range(1, MAXN + 1):
            Mn = OPER(M, n)
            Mn1 = OPER(M, n + 1)
            if Mn is SKIP or Mn1 is SKIP: continue
            # (1) M[n] = M[n+1][1]^{j1-j-2}
            X = Mn1
            ok = True
            for _ in range(j1 - jm2):
                X = OPER(X, 1)
                if X is SKIP: ok = False; break
            if ok:
                c1t += 1
                if list(X) == list(Mn): c1 += 1
            # (2) Trans(M)[n-1] = Trans(M[n+1][1]^{j1-1-j-2})
            Y = Mn1
            ok = True
            for _ in range(j1 - 1 - jm2):
                Y = OPER(Y, 1)
                if Y is SKIP: ok = False; break
            if ok:
                TY = guarded(Trans, Y, budget=30)
                if TY is not SKIP:
                    c2t += 1
                    if operB(TM, numBT(n - 1)) == TY: c2 += 1
                    elif cex2 is None: cex2 = (fmt(M), n)
            # (3) principal-pair scb  (Trans(M[n]) vs Trans(M)[n])
            T1 = guarded(Trans, Mn, budget=30)
            if T1 is not SKIP:
                c3t += 1
                if vx.principal_pair_exists(T1, operB(TM, numBT(n))): c3 += 1
        continue
        # alternative (shift, count) readings of (2)
        for n in range(1, MAXN + 1):
            for sh in (-2, -1, 0, 1):
                for it in range(0, 4):
                    Z = OPER(M, n + 1)
                    if Z is SKIP: continue
                    ok = True
                    for _ in range(it):
                        Z = OPER(Z, 1)
                        if Z is SKIP: ok = False; break
                    if not ok: continue
                    TZ = guarded(Trans, Z, budget=30)
                    if TZ is SKIP or n + sh < 0: continue
                    k = (sh, it)
                    a, b = alt.get(k, (0, 0))
                    alt[k] = (a + (operB(TM, numBT(n + sh)) == TZ), b + 1)
    print("\n== A33  §8.4 lemma (III|IV) basic props  [non-vacuous: (1) %d, (2) %d, (3) %d]"
          % (c1t, c2t, c3t))
    print("   (1) LITERAL M[n]=M[n+1][1]^{j1-j-2}          : %d/%d" % (c1, c1t))
    print("   (2) LITERAL Trans(M)[n-1]=Trans(M[n+1][1]^{j1-1-j-2}) : %d/%d  %s"
          % (c2, c2t, cex2 or ''))
    print("   (3) LITERAL principal-pair scb               : %d/%d" % (c3, c3t))
    best = sorted(alt.items(), key=lambda kv: -(kv[1][0] / max(kv[1][1], 1)))[:3]
    print("   best alternative (shift,extra[1]s) for (2):", best)


# ---------------------------------------------------------------- A34 / A37 (§8.6 (1))
def a34():
    k_ok = k_t = c2 = c2t = c3 = c3t = 0
    cex = None
    ks = {}
    for M in hosts:
        if Lng(M) < 3 or not reduced(M) or not monoT(M): continue
        if not condVI(M): continue
        iv = guarded(internals, M, budget=20)
        if iv is SKIP or iv is None: continue
        j1, j0 = iv['j1'], iv['j0']
        if j1 <= 1: continue
        TM = guarded(Trans, M, budget=30)
        if TM is SKIP: continue
        admj0 = adm(M, j0)
        bound = entry(M, 1, j1) + 1
        for n in range(1, MAXN + 1):
            mn = (n - 2) if admj0 else (n - 1)
            Mn = OPER(M, n)
            if Mn is SKIP: continue
            T = guarded(Trans, Mn, budget=30)
            if T is SKIP: continue
            if mn == -1:                      # (1)  n=1 & j0 admissible
                k_t += 1
                found = None
                for k in range(0, 12):
                    if operB_iter0(TM, k) == T:
                        found = k; break
                if found is not None and 1 < found <= bound:
                    k_ok += 1
                    ks[found] = ks.get(found, 0) + 1
                elif cex is None:
                    cex = (fmt(M), n, found, bound)
            elif mn >= 0:                     # (2)
                c2t += 1
                if operB(TM, numBT(mn)) == T: c2 += 1
            c3t += 1
            if lessBT(T, TM): c3 += 1
    print("\n== A34/A37  §8.6 prop (VI) exchange  [non-vacuous: (1) m_n=-1 legs %d, (2) %d]"
          % (k_t, c2t))
    print("   (1) LITERAL  EX k. 1<k<=M_{1,j1}+1 & Trans(M[n])=Trans(M)[0]^k : %d/%d  %s"
          % (k_ok, k_t, cex or ''))
    print("       distribution of the witnessing k:", dict(sorted(ks.items())))
    print("   (2) LITERAL  Trans(M[n])=Trans(M)[m_n]  : %d/%d" % (c2, c2t))
    print("   (3) LITERAL  Trans(M[n])<Trans(M)       : %d/%d" % (c3, c3t))


# ---------------------------------------------------------------- A38 (§8.7)
def a38():
    ok = tot = 0
    cex = None
    for N in pool:
        if Lng(N) < 2 or Lng(N) > 6: continue
        TN = guarded(Trans, N, budget=30)
        if TN is SKIP: continue
        for n in range(1, MAXN + 1):
            Nn = OPER(N, n)
            if Nn is SKIP: continue
            T = guarded(Trans, Nn, budget=30)
            if T is SKIP: continue
            tot += 1
            hit = False
            for m in range(0, n + 2):
                base = operB(TN, numBT(m))
                x = base
                for k in range(0, 8):
                    if x == T: hit = True; break
                    x = operB(x, numBT(0))
                if hit: break
            if hit: ok += 1
            elif cex is None: cex = (fmt(N), n)
    print("\n== A38  §8.7 value equation Trans(N[n]) = Trans(N)[m][0]^k")
    print("   non-vacuous instances (N in ST_PS, n>=1): %d" % tot)
    print("   EX (m<=n+1, k<=7) solving it : %d/%d  %s" % (ok, tot, cex or ''))
    # the formal CEX cited by A38
    for (N, n) in [([(1, 1)], 1), ([(0, 0), (1, 1), (2, 2), (3, 2), (4, 2)], 1)]:
        TN = guarded(Trans, N, budget=30); Nn = OPER(N, n)
        if SKIP in (TN, Nn): continue
        T = guarded(Trans, Nn, budget=30)
        sol = [(m, k) for m in range(0, 6) for k in range(0, 8)
               if operB_iter0(operB(TN, numBT(m)), k) == T]
        print("   cited CEX N=%s n=%d -> solutions (m,k): %s" % (fmt(N), n, sol[:4]))


import time
for f in (a29, a33, a34, a38):
    t0 = time.time(); f(); print('   [%.0fs]' % (time.time() - t0), flush=True)
