#!/usr/bin/env python3
"""r46 condIV corner, part 2: RT-level brute force + deep ST hunt + npx-analogue check.

(1) Brute-force RT_PS & PT_PS hosts (entries bounded) with condIV and
    NOT hasParent(1, j1) -- incl. the hand CEX (1,1)(2,2)(3,3)(3,1).
    On each: validate (a) M[m] == Pred M, (b) Trans(Pred M)==operB(TransM,num 0),
    (c) EX k. leBT(Trans(M[m]), operB(Trans M, numBT k)).
(2) Deep ST_PS BFS (bigger caps): do such hosts ever appear in ST_PS?
"""
import sys, os
from itertools import product
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _r15_vx_lib import (Trans, operB, numBT, leBT, gen_pool, mono_hosts,
                         condIV, guarded, SKIP)
from red_model import Lng, entry, hasParent, oper, Pred, fmt, monoT, reduced

def corner(M):
    j1 = Lng(M) - 1
    if j1 <= 1: return False
    if not condIV(M): return False          # cheap filters FIRST
    if hasParent(M, 1, j1): return False
    if not monoT(M): return False
    return reduced(M)                        # expensive last

# ---- (1) brute force RT & PT ----
found = []
for L in (3, 4):
    for cols in product(product(range(0, 5), range(0, 5)), repeat=L):
        M = [list(c) for c in cols]
        if corner(M):
            found.append([tuple(tuple(c) for c in M)])
            found[-1] = tuple(tuple(c) for c in M)
            if len(found) >= 60: break
    if len(found) >= 60: break
print("RT&PT condIV noParent corner hosts (brute, L<=5, e<5):", len(found), flush=True)
for M in found[:8]:
    print("   ", fmt(list(map(list, M))), flush=True)

fail_a = []; fail_b = []; fail_k = []; n_val = 0
for Mt in found[:20]:
    M = list(map(list, Mt))
    n_val += 1
    TM = guarded(Trans, M, budget=8)
    PM = Pred(M)
    TP = guarded(Trans, PM, budget=8)
    if TM is not SKIP and TP is not SKIP:
        ob0 = guarded(operB, TM, numBT(0), budget=8)
        if ob0 is SKIP or TP != ob0:
            fail_b.append((fmt(M), "TP", TP, "ob0", ob0))
    for m in (2, 3, 4):
        Nm = guarded(oper, M, m, budget=5)
        if Nm is SKIP: continue
        if Nm != PM:
            fail_a.append((fmt(M), m, fmt(Nm)))
        if TM is SKIP: continue
        TNm = guarded(Trans, Nm, budget=8)
        if TNm is SKIP: continue
        ok = False
        for k in range(0, 6):
            ob = guarded(operB, TM, numBT(k), budget=8)
            if ob is not SKIP and leBT(TNm, ob):
                ok = True; break
        if not ok:
            fail_k.append((fmt(M), m))
print("validated hosts:", n_val, flush=True)
print("(a) M[m]==Pred M fails:", len(fail_a), fail_a[:5], flush=True)
print("(b) k=0 equality readback fails:", len(fail_b), fail_b[:3], flush=True)
print("(c) EX-k leBT fails:", len(fail_k), fail_k[:5], flush=True)

# ---- (2) deep ST_PS hunt ----
pool = gen_pool(maxlen=10, maxn=6, maxseed=5, cap=25000)
hosts = mono_hosts(pool)
st = set(tuple(tuple(c) for c in M) for M in pool)
n_c4 = 0; n_corner = 0; ex = []
for N in hosts:
    j1 = Lng(N) - 1
    if j1 <= 1 or not monoT(N) or not condIV(N): continue
    n_c4 += 1
    if not hasParent(N, 1, j1):
        n_corner += 1
        if len(ex) < 8: ex.append(fmt(N))
print("deep ST pool", len(pool), "condIV hosts:", n_c4,
      "corner (noParent):", n_corner, ex, flush=True)
inpool = [fmt(list(map(list, M))) for M in found if tuple(M) in st]
print("brute corner hosts present in ST pool:", len(inpool), inpool[:5], flush=True)
