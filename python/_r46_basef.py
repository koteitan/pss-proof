#!/usr/bin/env python3
# r46 BASEf STEP-0: on vg7x_reg4 BASE hosts (cfbx_j1p = Lng-1) measure the
# same-head run (J1 - LastStep) and validate the run-peel design:
#   (r>0) JEQ   : Joints[J1-1] == Joints[J1]  (run branches share the joint)
#   (r>0) REGP  : reg7(Pred M) holds (run-peel regime preservation)
#   (r>0) LSST  : LastStep(Pred M) == LastStep(M), FirstNodes stable at LS,
#                 front slice stable, TrMax stable, BrLen drops by 1
#   (r>0) TERM  : terminal(Pred M) == Pred(terminal M)   (via JEQ)
#   (all) PIN   : body(Trans M) = frontHead ++ [D_{e(1,j0')} a]  (pinned form)
#   (all) TSB   : the pinned block inner a == bpHeadT(Trans Mp)  (TSPIN@base)
#   (r=0) SPLIT0: bpHeadT(Trans Mp) = frontHead ++ t2, t2 nonempty
import sys, os, itertools, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from functools import lru_cache
from red_model import (Lng, entry, monoT, Red, Br, FirstNodes, Joints, TrMax,
                       seg, fmt, oper, reduced)
import trans_model as tm

def Trans(M): return _T(tuple(M))
@lru_cache(maxsize=None)
def _T(t): return tm.Trans(list(t))
def bpHeadT(t): return t[1][0][2] if t[1] else ('T', [])
@lru_cache(maxsize=None)
def _r(t): return reduced(list(t))
@lru_cache(maxsize=None)
def _m(t): return monoT(list(t))

def LastStep(M):
    b = Br(M)
    if not b: return 0
    J1 = len(b) - 1
    h0 = entry(b[J1], 0, 0); h1 = entry(b[J1], 1, 0)
    if h0 == h1: return J1
    return min(J for J in range(len(b))
               if entry(b[J1], 0, 0) == entry(b[J], 0, 0)
               and entry(b[J], 1, 0) < entry(b[J], 0, 0))

def cj(M): return FirstNodes(M)[len(Br(M)) - 1]
def reg2(M): return _r(tuple(M)) and _m(tuple(M)) and len(Br(M)) > 0
def desc(bs):
    return all(entry(bs[i],0,0) > entry(bs[i+1],0,0)
               or (entry(bs[i],0,0) == entry(bs[i+1],0,0)
                   and entry(bs[i],1,0) >= entry(bs[i+1],1,0))
               for i in range(len(bs)-1))
def reg4(M):
    if not reg2(M): return False
    j = cj(M)
    if not entry(M,0,j) > entry(M,1,j): return False
    J1 = len(Br(M)) - 1; j0 = Joints(M)[J1]
    return j0 is not None and 0 < j0 < TrMax(M)
def reg7(M): return reg4(M) and desc(Br(M))
def Pred(M): return list(M[:-1]) if Lng(M) > 1 else list(M)

t0 = time.time()
GRID = [(x,y) for x in range(3) for y in range(3)]
seeds = set()
for L in range(3,5):
    for tup in itertools.product(GRID, repeat=L-1):
        M = [(0,0)] + list(tup)
        if reg2(M): seeds.add(tuple(M))
for h in [[(0,0),(1,1),(2,2),(3,1),(4,2)],
          [(0,0),(1,1),(2,2),(3,3),(4,1),(5,2)],
          [(0,0),(1,1),(2,2),(3,3),(4,1),(5,2),(6,2)],
          [(0,0),(1,1),(2,2),(3,3),(4,4),(5,2),(6,3)],
          [(0,0),(1,1),(2,1),(1,1),(2,1)],
          [(0,0),(1,1),(2,2),(2,1),(1,1),(2,2),(2,1)],
          [(0,0),(1,1),(2,1),(3,1),(1,1),(2,1),(3,1)]]:
    if reg2(h): seeds.add(tuple(h))
print(f"seeds={len(seeds)} ({round(time.time()-t0,1)}s)", flush=True)
seen = set(seeds); frontier = list(seeds); layer = 0
while frontier and len(seen) < 3000 and layer < 20:
    layer += 1; nxt = []
    for M in frontier:
        if Lng(M) > 9: continue
        for n in (2,3):
            try:
                inter = oper(list(M), n)
                if Lng(inter) > 18: continue
                R = Red(inter)
            except Exception: continue
            if 2 <= Lng(R) <= 11 and reg2(R):
                t = tuple(R)
                if t not in seen: seen.add(t); nxt.append(t)
            if len(seen) >= 3000: break
        if len(seen) >= 3000: break
    frontier = nxt
print(f"corpus={len(seen)} layers={layer} ({round(time.time()-t0,1)}s)", flush=True)

base_hosts = [list(M) for M in seen if reg7(list(M)) and cj(list(M)) == Lng(list(M))-1]
print(f"BASE hosts (reg7 & cfbx_j1p=Lng-1): {len(base_hosts)}", flush=True)

from collections import Counter
rundist = Counter()
fails = Counter(); oks = Counter()
CEX = {}
def chk(name, cond, M):
    if cond: oks[name] += 1
    else:
        fails[name] += 1
        if name not in CEX: CEX[name] = fmt(M) if not isinstance(M,str) else M

for M in base_hosts:
    n = Lng(M); b = Br(M); J1 = len(b)-1
    j0 = Joints(M)[J1]; LS = LastStep(M); r = J1 - LS
    rundist[r] += 1
    m1 = FirstNodes(M)[LS]
    Mp = seg(M, j0, n-1); front = seg(M, 0, m1-1)
    # last branch single-column at BASE
    chk('LASTBR1', len(b[J1]) == 1, M)
    try:
        A = bpHeadT(Trans(front)); B = bpHeadT(Trans(Mp)); TM = Trans(M)
        C = bpHeadT(TM); v = entry(M,1,j0)
        # PIN: body(Trans M) = A ++ [D_v a]
        pin = (len(C[1]) == len(A[1])+1 and C[1][:len(A[1])] == A[1]
               and C[1][-1][1] == v)
        chk('PIN', pin, M)
        if pin:
            chk('TSB', C[1][-1][2] == B, M)   # TSPIN readback at base
        if r == 0:
            # SPLIT0: B = A ++ t2, t2 nonempty
            chk('SPLIT0', len(B[1]) > len(A[1]) and B[1][:len(A[1])] == A[1], M)
            # front slice == Pred M (r=0 geometry)
            chk('FRONT0', front == Pred(M), M)
    except Exception as e:
        chk('TRANS_ERR:'+str(e)[:40], False, M)
    if r > 0:
        P = Pred(M)
        chk('JEQ', Joints(M)[J1-1] == j0, M)
        chk('BRLEN', len(Br(P)) == len(b)-1, M)
        chk('TRMAX', TrMax(P) == TrMax(M), M)
        chk('REGP', reg7(P), M)
        try:
            chk('LSST', LastStep(P) == LS, M)
            chk('FNST', FirstNodes(P)[LS] == m1, M)
            chk('FRONTST', seg(P,0,m1-1) == front, M)
            chk('TERM', seg(P, Joints(P)[len(Br(P))-1], Lng(P)-1) == Mp[:-1], M)
        except Exception as e:
            chk('PEEL_ERR:'+str(e)[:40], False, M)

print("run-length distribution:", dict(sorted(rundist.items())), flush=True)
print("--- checks (ok/fail) ---")
for k in sorted(set(list(oks)+list(fails))):
    line = f"{k}: ok={oks[k]} fail={fails[k]}"
    if k in CEX: line += f"  CEX={CEX[k]}"
    print(line)
print(f"total {round(time.time()-t0,1)}s")
