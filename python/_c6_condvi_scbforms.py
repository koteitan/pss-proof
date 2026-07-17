#!/usr/bin/env python3
"""Audit of the TWO REDUCED residual Props of lean/8/8.6-condVI-close.lean.

That file discharges the Buchholz-side content of `CondVIAdmTowerScb` /
`CondVIExchNadm` (lean/8/8.6-Trans-fseq-condVI.lean) and leaves only the
pair-sequence-side closed forms:

  (A') CondVI_scbdec_adm_forms_v6   -- admissible j0, u = M_{1,j0}:
         exists (s1,b1) with
           flatMn : n>=1 ==> flatBT(Trans(M[n])) = s1 + flatBT(D_u(Dtower u (n-1))) + b1
           k1     : flatBT(Trans M)              = s1 + flatBT(D_u(D_{u+1} 0)) + b1
                    and kind-1, i.e. RightNodes = [u, u+1] with u < u+1  (automatic)
  (B') CondVI_scbdec_nadm_forms_v6  -- non-admissible j0:
         exists U < u+1 and (s1,b1) with
           flatMn : n>=1 ==> flatBT(Trans(M[n])) = s1 + flatBT(D_U(Dtower u n)) + b1
                             (tower index n, NOT n-1 -- the genuine outer head D_U
                              shifts the L-tower by one; Isabelle c613x_condVI_exch_nadm)
           k1     : flatBT(Trans M)              = s1 + flatBT(D_U(D_{u+1} 0)) + b1
                    and kind-1, i.e. U < u+1

The point of the audit is NON-VACUITY + TRUTH: a green-modulo file is worthless
if its Props are unsatisfiable (cf. the wave-F catch of
m_8_4_Trans_oper_exchange_corrected_condIII, 0/39 on a real pool).

Pool: genuine ST_PS (diagSeq seeds closed under oper), A23-corrected operB.
b1 is read off the n=1 (adm) / n=1 (nadm) leg and then TESTED on all other n.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _r56_operBfix_lib as fx          # patches vx.operB / vx.xseq (A23-corrected)
from _r56_operBfix_lib import operB
import _r15_vx_lib as vx
from _r15_vx_lib import gen_pool, mono_hosts, Trans, numBT, guarded, SKIP
from red_model import Lng, entry, oper, parent, monoT
from trans_model import Dpt, ZB, flatBT, adm, reduced, condVI

MAXN = 4


def tower(u, k):
    t = ZB
    for _ in range(k):
        t = Dpt(u, t)
    return t


def OPER(M, n):
    return guarded(oper, M, n, budget=10)


def TR(M):
    t = guarded(Trans, M, budget=20)
    return None if (t is SKIP) else t


def read_pair(flat, center):
    """Read off (s,b) with flat == s + center + b and b all ')'."""
    for i in range(len(flat) - len(center) + 1):
        if flat[i:i + len(center)] == center:
            s, b = flat[:i], flat[i + len(center):]
            if all(x == ')' for x in b):
                return s, b
    return None


print("building genuine ST_PS pool (diagSeq seeds, oper closure) ...")
pool = gen_pool(maxlen=9, maxn=3, maxseed=3, cap=2000)
hosts = mono_hosts(pool)
print(f"pool={len(pool)} mono ST_PS hosts={len(hosts)}\n")

A_ok = A_tot = 0
A_cex = None
B_ok = B_tot = 0
B_cex = None
Us = set()

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
    TM = TR(M)
    if TM is None:
        continue
    fM = flatBT(TM)

    if adm(M, j0):
        # ---- (A'): kind-1 core is D_u(D_{u+1} 0); read (s1,b1) off Trans M ----
        A_tot += 1
        cand = read_pair(fM, flatBT(Dpt(u, Dpt(u + 1, ZB))))
        if cand is None:
            A_cex = A_cex or ('k1: no (s1,b1) at c2=D_u(D_{u+1} 0)', list(M))
            continue
        s1, b1 = cand
        good = True
        for n in range(1, MAXN + 1):
            Mn = OPER(M, n)
            if Mn is SKIP:
                good = False
                break
            Tn = TR(Mn)
            if Tn is None:
                good = False
                break
            if flatBT(Tn) != s1 + flatBT(Dpt(u, tower(u, n - 1))) + b1:
                good = False
                A_cex = A_cex or ('flatMn n=%d' % n, list(M))
                break
        if good:
            A_ok += 1
    else:
        # ---- (B'): genuine outer head U < u+1; core is D_U(D_{u+1} 0) ----
        B_tot += 1
        found = None
        for U in range(0, u + 1):                    # U < u+1
            cand = read_pair(fM, flatBT(Dpt(U, Dpt(u + 1, ZB))))
            if cand is None:
                continue
            s1, b1 = cand
            good = True
            for n in range(1, MAXN + 1):
                Mn = OPER(M, n)
                if Mn is SKIP:
                    good = False
                    break
                Tn = TR(Mn)
                if Tn is None:
                    good = False
                    break
                # tower index n (NOT n-1)
                if flatBT(Tn) != s1 + flatBT(Dpt(U, tower(u, n))) + b1:
                    good = False
                    break
            if good:
                found = U
                break
        if found is None:
            B_cex = B_cex or ('no U < u+1 with k1 + flatMn(index n)', list(M))
        else:
            B_ok += 1
            Us.add((found, u))

print(f"(A') CondVI_scbdec_adm_forms_v6  : {A_ok}/{A_tot}   cex={A_cex}")
print(f"(B') CondVI_scbdec_nadm_forms_v6 : {B_ok}/{B_tot}   cex={B_cex}")
print(f"     (B') observed (U, u) pairs  : {sorted(Us)}")
