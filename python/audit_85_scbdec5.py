#!/usr/bin/env python3
"""Audit for lean/8/8.5-scb-decompositions.lean  (correction A29, §8.5 part (5)).

The article's §8.5 lemma (条件(V)の下での各種scb分解) part (5) (content.md 5225) claims,
for every M in ST_PS ∩ PT_PS with j1 > 1, condition (V) and j0 NON-M-admissible,
and every n ∈ N_+:

    Trans(M[n]) = s1 D_{M1,j-1} (s'1 D_{M1,j0})^n t2 (b'1)^n b1        [LITERAL]

Correction A29 says this is FALSE at n = 1 (the exponent there is 0, as the
article's own base case at content.md 5329 derives) and TRUE for n > 1:

    n = 1 : Trans(M[1]) = s1 D_{M1,j-1} t2 b1                          [exp 0]
    n > 1 : Trans(M[n]) = s1 D_{M1,j-1} (s'1 D_{M1,j0})^n t2 (b'1)^n b1

This script reports, over the genuine ST_PS pool (diagSeq seeds closed under oper):

  1. NON-VACUITY: the number of distinct hosts satisfying the full hypothesis
     (condition (V) + j0 non-admissible + j1 > 1), and prints the smallest one.
  2. The literal form's score split by n (expect 0/k at n=1, k/k at n>1).
  3. The A29-corrected form's score (expect full marks at every n).
  4. The Lean-side body identity that 8.5-scb-decompositions.lean rests on:
        flat(e5x_bodyM t2 e k) = (s0 [D_e])^(k+1) flat(t2) (b0)^(k+1)   for k >= 1
        flat(e5x_bodyM t2 e 0) = flat(t2)
     with (s0,b0) the inner scb pair, i.e. exponent = n = k+1 for n >= 2 and 0 at n = 1.
     This is the numerical statement that the corrected claim and the ported
     `ExchV_nf3x` closed form agree.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _r56_operBfix_lib as fx          # patches vx.operB / vx.xseq / vx.operB_iter0
import _r15_vx_lib as vx
from _r15_vx_lib import gen_pool, mono_hosts, internals, Trans, guarded, SKIP
from red_model import Lng, entry, oper, monoT, fmt
from trans_model import Dpt, ZB, flatBT, scb_decomps, adm, reduced, condV

MAXN = 4


def sprime(M, iv):
    """(s'1, b'1) from part (1): (D_{M1,j-1} s'1, D_{M1,j1} 0, b'1) is an scb
    decomposition of c2."""
    center = flatBT(Dpt(entry(M, 1, iv['j1']), ZB))
    for (s, b) in scb_decomps(iv['c2'], center):
        if s and s[0] == ('D', entry(M, 1, iv['jm1'])):
            return s[1:], b
    return None


def rep(xs, n):
    return list(xs) * n


def addBT(a, b):
    return ('trm', list(a[1]) + list(b[1]))


def s85b_W(u, t, c, k):
    """Isabelle s85b_W / Lean s85b_W: W_0 = D_u c, W_{k+1} = D_u (t +_B W_k)."""
    if k == 0:
        return Dpt(u, c)
    return Dpt(u, addBT(t, s85b_W(u, t, c, k - 1)))


def e5x_bodyM(t, e, k):
    """Isabelle e5x_bodyM / Lean e5x_bodyM: body of the core D_u(.) of Trans(M[k+1])."""
    if k == 0:
        return t
    return addBT(t, s85b_W(e, t, t, k))


def main():
    print("building genuine ST_PS pool (diagSeq seeds, oper closure) ...")
    pool = gen_pool(maxlen=8, maxn=3, maxseed=3, cap=1500)
    hosts = mono_hosts(pool)
    print("pool=%d mono ST_PS hosts=%d\n" % (len(pool), len(hosts)))

    good = []           # hosts satisfying the FULL hypothesis of the §8.5 lemma
    lit = {}            # n -> [ok, total]  literal (exponent n)
    corr = {}           # n -> [ok, total]  A29-corrected
    body = [0, 0]       # Lean e5x_bodyM identity

    for M in hosts:
        if Lng(M) < 3 or not reduced(M) or not monoT(M):
            continue
        if not condV(M):
            continue
        iv = guarded(internals, M, budget=20)
        if iv is SKIP or iv is None or iv['s1'] is None:
            continue
        j1, j0, jm1 = iv['j1'], iv['j0'], iv['jm1']
        if j1 <= 1 or adm(M, j0):          # condV + j0 NON-admissible + j1 > 1
            continue
        sb = sprime(M, iv)
        if sb is None:
            continue
        s1p, b1p = sb
        s1, b1, t2 = iv['s1'], iv['b1'], iv['t2']
        good.append(M)
        Dm1 = ('D', entry(M, 1, jm1))
        Dj0 = ('D', entry(M, 1, j0))
        e = entry(M, 1, j0)

        def form(x):
            return (list(s1) + [Dm1] + rep(list(s1p) + [Dj0], x)
                    + flatBT(t2) + rep(b1p, x) + list(b1))

        for n in range(1, MAXN + 1):
            Mn = guarded(oper, M, n, budget=10)
            if Mn is SKIP:
                continue
            T = guarded(Trans, Mn, budget=30)
            if T is SKIP:
                continue
            f = flatBT(T)
            lit.setdefault(n, [0, 0])
            corr.setdefault(n, [0, 0])
            lit[n][1] += 1
            if f == form(n):
                lit[n][0] += 1
            corr[n][1] += 1
            if f == form(0 if n == 1 else n):
                corr[n][0] += 1
            # Lean-side: flat(e5x_bodyM t2 e (n-1)) is the body inside D_{M1,j-1}
            body[1] += 1
            want = rep(list(s1p) + [Dj0], 0 if n == 1 else n) + flatBT(t2) + rep(b1p, 0 if n == 1 else n)
            if flatBT(e5x_bodyM(t2, e, n - 1)) == want:
                body[0] += 1

    print("== NON-VACUITY (condition (V) + j0 non-admissible + j1 > 1)")
    print("   distinct hosts satisfying the hypothesis : %d" % len(good))
    if good:
        sm = min(good, key=lambda M: (Lng(M), M))
        print("   smallest such host                       : %s   (Lng=%d)"
              % (fmt(sm), Lng(sm)))
    print()
    print("== A29  §8.5 lemma (V) part (5)")
    for n in sorted(lit):
        print("   n=%d  article LITERAL (exponent n) : %d/%d %s"
              % (n, lit[n][0], lit[n][1], "  <-- FALSE" if lit[n][0] == 0 and lit[n][1] else ""))
    for n in sorted(corr):
        print("   n=%d  A29-CORRECTED             : %d/%d" % (n, corr[n][0], corr[n][1]))
    print()
    print("== Lean `e5x_bodyM` body identity (ExchV_nf3x core == corrected (5))")
    print("   flat(e5x_bodyM t2 e (n-1)) == corrected body : %d/%d" % (body[0], body[1]))


if __name__ == '__main__':
    main()
