#!/usr/bin/env python3
# r46 BASEf STEP-0 (run 2): CONSTRUCTIVE reg7 BASE hosts (r38-style multi-branch),
# targeting same-head runs r>0. Same checks as _r46_basef.py.
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
    S = [J for J in range(len(b))
         if entry(b[J1], 0, 0) == entry(b[J], 0, 0)
         and entry(b[J], 1, 0) < entry(b[J], 0, 0)]
    return min(S)

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
# constructive hosts: trunk 0..t, optional big-head prefix branches, then a
# same-head run of branches ending in the single-node last branch (BASE).
hosts = []
seenh = set()
for t in range(2, 6):
    trunk = [(j, j) for j in range(t+1)]
    for h in range(2, t+1):
        for h1 in range(0, h):
            head = (h, h1)
            bodies = [[head]]
            for x in range(1, h+2):
                bodies.append([head, (h+1, x)])
                for y in range(1, h+3):
                    bodies.append([head, (h+1, x), (h+2, y)])
            # prefix branches with strictly bigger head (before the run)
            prefixes = [[]]
            if h+1 <= t:
                for px in range(0, h+2):
                    prefixes.append([(h+1, px)])
                    prefixes.append([(h+1, px), (h+2, 1)])
            for pre in prefixes:
                for B in bodies:
                    for k in (1, 2, 3):
                        M = trunk + pre + B*k + [head]
                        if Lng(M) > 12: continue
                        key = tuple(M)
                        if key in seenh: continue
                        seenh.add(key)
                        try:
                            if reg7(M) and cj(M) == Lng(M)-1:
                                hosts.append(M)
                        except Exception:
                            pass
print(f"constructive BASE hosts: {len(hosts)} ({round(time.time()-t0,1)}s)", flush=True)

from collections import Counter
rundist = Counter(); fails = Counter(); oks = Counter(); CEX = {}
def chk(name, cond, M):
    if cond: oks[name] += 1
    else:
        fails[name] += 1
        if name not in CEX: CEX[name] = fmt(M)

for M in hosts:
    n = Lng(M); b = Br(M); J1 = len(b)-1
    j0 = Joints(M)[J1]; LS = LastStep(M); r = J1 - LS
    rundist[r] += 1
    m1 = FirstNodes(M)[LS]
    Mp = seg(M, j0, n-1); front = seg(M, 0, m1-1)
    chk('LASTBR1', len(b[J1]) == 1, M)
    try:
        A = bpHeadT(Trans(front)); B = bpHeadT(Trans(Mp)); TM = Trans(M)
        C = bpHeadT(TM); v = entry(M,1,j0)
        pin = (len(C[1]) == len(A[1])+1 and C[1][:len(A[1])] == A[1]
               and C[1][-1][1] == v)
        chk('PIN', pin, M)
        if pin:
            chk('TSB', C[1][-1][2] == B, M)
        if r == 0:
            chk('SPLIT0', len(B[1]) > len(A[1]) and B[1][:len(A[1])] == A[1], M)
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
            # IH consumability: VE34 shape at Pred (growth+headshift), when reg7(P)
            if reg7(P):
                nP=Lng(P); bP=Br(P); j0P=Joints(P)[len(bP)-1]; LSP=LastStep(P)
                m1P=FirstNodes(P)[LSP]
                AP=bpHeadT(Trans(seg(P,0,m1P-1))); BP=bpHeadT(Trans(seg(P,j0P,nP-1)))
                CP=bpHeadT(Trans(P)); vP=entry(P,1,j0P)
                chk('VE34P', len(BP[1])>len(AP[1]) and BP[1][:len(AP[1])]==AP[1]
                    and CP[1]==AP[1]+[('D',vP,BP)], M)
        except Exception as e:
            chk('PEEL_ERR:'+str(e)[:40], False, M)

print("run-length distribution:", dict(sorted(rundist.items())), flush=True)
print("--- checks (ok/fail) ---")
for k in sorted(set(list(oks)+list(fails))):
    line = f"{k}: ok={oks[k]} fail={fails[k]}"
    if k in CEX: line += f"  CEX={CEX[k]}"
    print(line)
print(f"total {round(time.time()-t0,1)}s")
