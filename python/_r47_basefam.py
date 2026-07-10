#!/usr/bin/env python3
# r47 BASE-family STEP-0: on the CONSTRUCTIVE vg7x_reg4 BASE corpus
# (r33-style enumeration: GRID 4x4, L=3..6, base+guard+joint bounds+desc),
# validate the r47 proof design:
#   ADM0    : Adm(M, j0') == 0                       (vg4x_base_Adm0 sanity)
#   JPBASE  : parent(M,0,Lng-1) == j0'               (base geometry)
#   NOJUMP  : e1j1 == 0 or e1(j0') >= e1j1           (condII/IV only, no V-jump)
#   ISLEFT  : (last principal of body(Trans(Pred M)) has head e1(j0')) <-> r>0
#   HEADEQ  : bpHeadT(Trans(Pred Mp)) == bpHeadT(Trans(Pred M))
#   MPFORM  : bpHeadT(Trans Mp) == bpHeadT(Trans(Pred Mp)) ++ [D_{e1j1} 0]
#   CL2     : (not isleft) Trans M == D_{e10}( t2 ++ [D_v (t2 ++ [D_{e1j1} 0])] )
#   CL4     : (isleft)     Trans M == D_{e10}( t3 ++ [D_v (t4 ++ [D_{e1j1} 0])] )
#   FRONT0  : (r=0) front slice == Pred M
#   TSB     : deposit == bpHeadT(Trans Mp)   (TSPIN@base, derived shape)
import sys, os, itertools, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, monoT, Red, Br, FirstNodes, Joints, TrMax,
                       seg, fmt, adm, Adm, parent)
from trans_model import Trans, bpHeadT

ZB = ('T', [])
def LastStep(M):
    b = Br(M)
    if not b: return 0
    J1 = len(b) - 1
    if entry(b[J1],0,0) == entry(b[J1],1,0): return J1
    return min(J for J in range(len(b))
               if entry(b[J1],0,0) == entry(b[J],0,0)
               and entry(b[J],1,0) < entry(b[J],0,0))
def desc(bs):
    return all(entry(bs[i],0,0) > entry(bs[i+1],0,0)
               or (entry(bs[i],0,0) == entry(bs[i+1],0,0)
                   and entry(bs[i],1,0) >= entry(bs[i+1],1,0))
               for i in range(len(bs)-1))
def Pred(M): return M[:-1] if Lng(M) > 1 else M

t0 = time.time()
hosts = []
for L in range(3,7):
    g = 4 if L <= 5 else 3
    GRID = [(x,y) for x in range(g) for y in range(g)]
    for tup in itertools.product(GRID, repeat=L-1):
        M = [(0,0)] + list(tup)
        if not (monoT(M) and Red(M) == M): continue
        b = Br(M)
        if not b or not desc(b): continue
        n = Lng(M); J1 = len(b)-1; j0 = Joints(M)[J1]
        if j0 is None or not (0 < j0 < TrMax(M)): continue
        j1p = FirstNodes(M)[J1]
        if j1p != n-1: continue                            # BASE
        if not entry(M,0,j1p) > entry(M,1,j1p): continue   # GUARD
        hosts.append(M)
print(f"reg7 BASE hosts={len(hosts)} ({round(time.time()-t0,1)}s)", flush=True)

from collections import Counter
rundist = Counter(); brp0 = Counter()
fails = Counter(); oks = Counter(); CEX = {}
def chk(name, cond, M):
    if cond: oks[name] += 1
    else:
        fails[name] += 1
        if name not in CEX: CEX[name] = fmt(M)

for M in hosts:
    n = Lng(M); b = Br(M); J1 = len(b)-1
    j0 = Joints(M)[J1]; LS = LastStep(M); r = J1 - LS
    rundist[r] += 1
    v  = entry(M,1,j0); e10 = entry(M,1,0); e1j1 = entry(M,1,n-1)
    m1 = FirstNodes(M)[LS]
    Mp = seg(M, j0, n-1); PredMp = Mp[:-1]; P = Pred(M)
    front = seg(M, 0, m1-1)
    chk('ADM0', Adm(M, j0) == 0, M)
    chk('JPBASE', parent(M,0,n-1) == j0, M)
    chk('NOJUMP', e1j1 == 0 or v >= e1j1, M)
    try:
        TP = Trans(P); t2t = bpHeadT(TP); pb = t2t[1]
        isleft = bool(pb) and pb[-1][1] == v
        chk('ISLEFT<->r>0', isleft == (r > 0), M)
        if r == 0: brp0[len(Br(P))] += 1
        TMp = Trans(Mp); TPMp = Trans(PredMp); TM = Trans(M)
        hq = (bpHeadT(TPMp) == t2t)
        chk('HEADEQ' if r == 0 else 'HEADEQstep', hq, M)
        mpform = (bpHeadT(TMp) == ('T', bpHeadT(TPMp)[1] + [('D', e1j1, ZB)]))
        chk('MPFORM', mpform, M)
        if not isleft:
            want = ('T', [('D', e10, ('T', pb + [('D', v, ('T', pb + [('D', e1j1, ZB)]))]))])
            chk('CL2', TM == want, M)
            dep = ('T', pb + [('D', e1j1, ZB)])
        else:
            t3 = pb[:-1]; t4 = pb[-1][2]
            want = ('T', [('D', e10, ('T', t3 + [('D', v, ('T', t4[1] + [('D', e1j1, ZB)]))]))])
            chk('CL4', TM == want, M)
            dep = ('T', t4[1] + [('D', e1j1, ZB)])
        chk('TSB', dep == bpHeadT(TMp), M)
        if r == 0:
            chk('FRONT0', front == P, M)
            A = bpHeadT(Trans(front))
            chk('SPLIT0', len(bpHeadT(TMp)[1]) > len(A[1])
                          and bpHeadT(TMp)[1][:len(A[1])] == A[1], M)
    except Exception as e:
        chk('ERR:'+str(e)[:50], False, M)

print("run-length dist:", dict(sorted(rundist.items())), flush=True)
print("Br(Pred) length dist at r=0:", dict(sorted(brp0.items())), flush=True)
print("--- checks (ok/fail) ---")
for k in sorted(set(list(oks)+list(fails))):
    line = f"{k}: ok={oks[k]} fail={fails[k]}"
    if k in CEX: line += f"  CEX={CEX[k]}"
    print(line)
print(f"total {round(time.time()-t0,1)}s")
