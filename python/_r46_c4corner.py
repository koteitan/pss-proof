#!/usr/bin/env python3
"""r46 dispatcher condIV corner probe.

Question: do transCondIV hosts with NOT hasParent N 1 (Lng N - 1) exist in
ST_PS (mono, 1 < Lng N - 1)?  If yes, validate the npx-analogue:
  (a) N[m] == Pred N for all m       (oper no-parent collapse, branch-generic)
  (b) Trans (Pred N) == operB (Trans N) (numBT 0)   (k=0 equality readback)
If no such host appears, that is evidence for dpx_condIV_hasParent
(transCondIV + ST_PS + PT_PS + 1 < Lng-1 ==> hasParent N 1 j1).

Side census: same question for condII hosts (exchII slot shape check).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _r15_vx_lib import (Trans, operB, numBT, leBT, gen_pool, mono_hosts,
                         condII, condIV, guarded, SKIP)
from red_model import Lng, entry, hasParent, parent, adm, oper, Pred, fmt, monoT

pool = gen_pool(maxlen=12, maxn=6, maxseed=4, cap=20000)
hosts = mono_hosts(pool)
print("pool", len(pool), "mono hosts", len(hosts), flush=True)

n_c4 = 0; n_c4_nohp = 0; n_c2 = 0; n_c2_nohp = 0
nohp_examples = []
fail_a = []; fail_b = []
# structural side-question: under condIV is entry N 1 j0' > 0 for ALL row-1
# ancestors down to 0?  and is entry N 1 (j1-1) related to hasParent?
for N in hosts:
    j1 = Lng(N) - 1
    if j1 <= 1: continue
    if not monoT(N): continue
    if condII(N):
        n_c2 += 1
        if not hasParent(N, 1, j1):
            n_c2_nohp += 1
    if not condIV(N): continue
    n_c4 += 1
    if hasParent(N, 1, j1): continue
    n_c4_nohp += 1
    if len(nohp_examples) < 8:
        nohp_examples.append(fmt(N))
    TN = guarded(Trans, N, budget=8)
    PN = Pred(N)
    TP = guarded(Trans, PN, budget=8)
    if TN is not SKIP and TP is not SKIP:
        ob0 = guarded(operB, TN, numBT(0), budget=8)
        if ob0 is SKIP or TP != ob0:
            fail_b.append((fmt(N), "TP", TP, "ob0", ob0))
    for m in (2, 3, 4):
        Nm = guarded(oper, N, m, budget=5)
        if Nm is SKIP: continue
        if Nm != PN:
            fail_a.append((fmt(N), m, fmt(Nm)))

print("condIV hosts (mono, j1>1):", n_c4, flush=True)
print("condIV hosts with NOT hasParent(1,j1):", n_c4_nohp, flush=True)
print("  examples:", nohp_examples, flush=True)
print("condII hosts:", n_c2, " with NOT hasParent(1,j1):", n_c2_nohp, flush=True)
if n_c4_nohp:
    print("(a) N[m]==Pred N fails:", len(fail_a), fail_a[:5], flush=True)
    print("(b) Trans(Pred N)==operB(TN,num 0) fails:", len(fail_b), fail_b[:3], flush=True)
