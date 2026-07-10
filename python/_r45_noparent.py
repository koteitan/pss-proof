#!/usr/bin/env python3
"""r45 noParentPred STEP-0 validation.

Target (cpx_exchIII_slot residual): N in ST_PS, N in PT_PS (=monoT), 1 < Lng N - 1,
transCondIII N, NOT hasParent N 1 (Lng N - 1), 1 < m ==>
    EX k. leBT (Trans (N[m])) (operB (Trans N) (numBT k)).

Also record the sharper candidates:
  (a) N[m] == Pred N                                     (oper no-parent collapse)
  (b) Trans (Pred N) == operB (Trans N) (numBT 0)        ((m,k)=(0,0) readback)
  (c) row-1 constancy: entry N 1 0 == entry N 1 j1
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _r15_vx_lib import (Trans, operB, numBT, leBT, gen_pool, mono_hosts,
                         condIII, guarded, SKIP)
from red_model import Lng, entry, hasParent, oper, Pred, fmt, monoT

pool = gen_pool(maxlen=11, maxn=5, maxseed=4, cap=9000)
hosts = mono_hosts(pool)
print("pool", len(pool), "mono hosts", len(hosts), flush=True)

n_host = 0; n_checks = 0
fail_main = []; fail_a = []; fail_b = []; fail_c = []
kmax_seen = -1
for N in hosts:
    j1 = Lng(N) - 1
    if j1 <= 1: continue
    if not monoT(N): continue
    if not condIII(N): continue
    if hasParent(N, 1, j1): continue
    n_host += 1
    TN = guarded(Trans, N, budget=8)
    if TN is SKIP: continue
    PN = Pred(N)
    TP = guarded(Trans, PN, budget=8)
    # (c) row-1 constancy at the ends
    if entry(N, 1, 0) != entry(N, 1, j1):
        fail_c.append(fmt(N))
    # (b) k=0 readback
    if TP is not SKIP:
        ob0 = guarded(operB, TN, numBT(0), budget=8)
        if ob0 is SKIP or TP != ob0:
            fail_b.append((fmt(N), "TP", TP, "ob0", ob0))
    for m in (2, 3, 4, 5):
        Nm = guarded(oper, N, m, budget=5)
        if Nm is SKIP: continue
        n_checks += 1
        # (a) collapse
        if Nm != PN:
            fail_a.append((fmt(N), m, fmt(Nm)))
        TNm = guarded(Trans, Nm, budget=8)
        if TNm is SKIP: continue
        ok = False
        for k in range(0, 8):
            ob = guarded(operB, TN, numBT(k), budget=8)
            if ob is SKIP: continue
            if leBT(TNm, ob):
                ok = True
                kmax_seen = max(kmax_seen, k)
                break
        if not ok:
            fail_main.append((fmt(N), m))
            if len(fail_main) > 5: break
    if len(fail_main) > 5: break

print("noParent condIII hosts:", n_host, " (N,m) checks:", n_checks, flush=True)
print("MAIN  EX-k leBT fails:", len(fail_main), fail_main[:5], flush=True)
print("  max k used:", kmax_seen, flush=True)
print("(a) N[m]==Pred N fails:", len(fail_a), fail_a[:5], flush=True)
print("(b) Trans(Pred N)==operB(TN,num 0) fails:", len(fail_b), fail_b[:3], flush=True)
print("(c) row1-const fails:", len(fail_c), fail_c[:5], flush=True)
