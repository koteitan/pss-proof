#!/usr/bin/env python3
"""Audit of the three named hypotheses of lean/8/8.6-Trans-fseq-condVI.lean.

A GREEN file conditional on named Props is only worth something if the Props are
TRUE and NON-VACUOUS.  This script exercises, on a genuine ST_PS pool (diagSeq
seeds closed under oper), under the A23-CORRECTED Buchholz fundamental sequence
(_r56_operBfix_lib):

  (A) CondVIAdmTowerScb   -- admissible-j0 condVI hosts: one (s1,b1) with
        flatBT(Trans(M[n]))              = s1 + flatBT(D_u(Dtower u (n-1))) + b1   (n>=1)
        flatBT(operB(Trans M, numBT m))  = s1 + flatBT(D_u(Dtower u (m+1))) + b1   (m>=0)
        u = M_{1,j0}, b1 all ')'
  (B) CondVIExchNadm      -- non-admissible-j0 condVI hosts, the three conclusions
        of Isabelle c6nx_condVI_exch_nadm_uncond.
  (C) the derived article conclusion (1): n=1, adm j0 =>
        exists k, 1 < k <= M_{1,j1}+1 and Trans(M[1]) = Trans(M)[0]^k.

Reports each count with its non-vacuous exercise count.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _r56_operBfix_lib as fx          # patches vx.operB / vx.xseq
from _r56_operBfix_lib import operB
import _r15_vx_lib as vx
from _r15_vx_lib import gen_pool, mono_hosts, Trans, numBT, lessBT, guarded, SKIP
from red_model import Lng, entry, oper, parent, monoT
from trans_model import Dpt, ZB, flatBT, adm, Pred, reduced, condVI

MAXN = 4


def tower(u, k):
    t = ZB
    for _ in range(k):
        t = Dpt(u, t)
    return t


def OPER(M, n):
    return guarded(oper, M, n, budget=10)


def iter0(t, k):
    for _ in range(k):
        t = operB(t, numBT(0))
    return t


print("building genuine ST_PS pool (diagSeq seeds, oper closure) ...")
pool = gen_pool(maxlen=9, maxn=3, maxseed=3, cap=2000)
hosts = mono_hosts(pool)
print(f"pool={len(pool)} mono ST_PS hosts={len(hosts)}\n")

A_ok = A_tot = 0
A_cex = None
B_ok = B_tot = 0
B_cex = None
C_ok = C_tot = 0
C_cex = None
ks = set()

for M in hosts:
    if Lng(M) < 3 or not reduced(M) or not monoT(M):
        continue
    if not condVI(M):
        continue
    j1 = Lng(M) - 1
    if not j1 > 1:
        continue
    j0 = parent(M, 0, j1)
    u = entry(M, 1, j0)
    TM = guarded(Trans, M, budget=20)
    if TM is SKIP or TM is None:
        continue

    if adm(M, j0):
        # ---- (A): read (s1,b1) off the n=1 leg, then test all n and m ----
        M1 = OPER(M, 1)
        if M1 is SKIP:
            continue
        T1 = guarded(Trans, M1, budget=20)
        if T1 is SKIP or T1 is None:
            continue
        f1 = flatBT(T1)
        center1 = flatBT(Dpt(u, tower(u, 0)))     # D_u 0
        cand = None
        for i in range(len(f1) - len(center1) + 1):
            if f1[i:i + len(center1)] == center1:
                s1, b1 = f1[:i], f1[i + len(center1):]
                if all(x == ')' for x in b1):
                    cand = (s1, b1)
                    break
        A_tot += 1
        if cand is None:
            A_cex = A_cex or ('no (s1,b1)', list(M))
            continue
        s1, b1 = cand
        good = True
        for n in range(1, MAXN + 1):
            Mn = OPER(M, n)
            if Mn is SKIP:
                good = False
                break
            Tn = guarded(Trans, Mn, budget=20)
            if Tn is SKIP or Tn is None:
                good = False
                break
            if flatBT(Tn) != s1 + flatBT(Dpt(u, tower(u, n - 1))) + b1:
                good = False
                A_cex = A_cex or ('flatMn n=%d' % n, list(M))
                break
        if good:
            for m in range(0, MAXN + 1):
                if flatBT(operB(TM, numBT(m))) != s1 + flatBT(Dpt(u, tower(u, m + 1))) + b1:
                    good = False
                    A_cex = A_cex or ('ov m=%d' % m, list(M))
                    break
        if good:
            A_ok += 1

        # ---- (C): the derived article conclusion (1) at n=1 ----
        C_tot += 1
        found = None
        for k in range(2, entry(M, 1, j1) + 2):
            if iter0(TM, k) == T1:
                found = k
                break
        if found is not None:
            C_ok += 1
            ks.add(found)
        else:
            C_cex = C_cex or list(M)
    else:
        # ---- (B): c6nx_condVI_exch_nadm_uncond, three conclusions ----
        B_tot += 1
        good = True
        for n in range(1, MAXN + 1):
            Mn, Mn1 = OPER(M, n), OPER(M, n + 1)
            if Mn is SKIP or Mn1 is SKIP:
                good = False
                break
            Tn = guarded(Trans, Mn, budget=20)
            Tn1 = guarded(Trans, Mn1, budget=20)
            if Tn is SKIP or Tn1 is SKIP or Tn is None or Tn1 is None:
                good = False
                break
            if not lessBT(Tn, operB(TM, numBT(n))):
                good = False; B_cex = B_cex or ('(1) n=%d' % n, list(M)); break
            if Tn != operB(TM, numBT(n - 1)):
                good = False; B_cex = B_cex or ('(2) n=%d' % n, list(M)); break
            if not lessBT(operB(TM, numBT(n - 1)), Tn1):
                good = False; B_cex = B_cex or ('(3) n=%d' % n, list(M)); break
        if good:
            B_ok += 1

print(f"(A) CondVIAdmTowerScb   : {A_ok}/{A_tot}   cex={A_cex}")
print(f"(B) CondVIExchNadm      : {B_ok}/{B_tot}   cex={B_cex}")
print(f"(C) article (1) at n=1  : {C_ok}/{C_tot}   cex={C_cex}   witnesses k={sorted(ks)}")
