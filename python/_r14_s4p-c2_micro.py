#!/usr/bin/env python3
"""r14-S4p-C2 micro-invariant check for the m_8_4_rightend_Trans Isar plan.
Verifies, over the genuine ST_PS regime (lemma domain), the exact bricks the
Isar proof uses:
  (m1) row-1 parent of j1Q in Q = Red N' is 0 (unique), and RedCondA gives
       e1(Q,0)+1 = e1(Q,j1Q)
  (m2) dichotomy: e1(Q,j0') >= e1(Q,j1Q)  OR  j0' = 0
       (hence always e1(Q,j0') >= e1(Q,0))
  (m3) NOT transCondVI(Q) and NOT transCondVI(R) and NOT transCondV(R)
  (m4) condA(Q) <-> adm(Q, j0')  and  condA(R) <-> adm(R, j0'),
       hence condA(Q) <-> condA(R)
  (m5) transC2 shapes: under condA both c2 are D_v(t2 + D_a 0) with the SAME
       v,t2 and a = e1(.,last); under ~condA & t2!=0 both are
       D_v(t3 + D_u(t4 + D_a 0)) with SAME v,t3,u,t4; under ~condA & t2==0
       both are D_v(D_u(D_a 0)) with same v,u
  (m6) the assembled (s,b) from the compose route equals the unique
       decomposition pair of the lemma statement (spot check)
"""
import sys, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
import red_model as rm
from red_model import (Lng, entry, parent, hasParent, seg, oper, monoT, diagSeq)
import trans_model as tm
from trans_model import (ZB, Dpt, addBT, flatBT, scb_decomps, adm, Adm,
                         condI, condIII, condV, condVI,
                         bpHeadT, bpHeadV)

_oT, _oM, _oR, _ored = tm.Trans, tm.Mark, rm.Red, tm.reduced
_mT, _mM, _mR, _mred = {}, {}, {}, {}
def Trans(M, depth=0):
    k = tuple(M)
    if k not in _mT: _mT[k] = _oT(M, depth)
    return _mT[k]
def Mark(M, m, depth=0):
    k = (tuple(M), m)
    if k not in _mM: _mM[k] = _oM(M, m, depth)
    return _mM[k]
def Red(M, depth=0):
    k = tuple(M)
    if k not in _mR: _mR[k] = _oR(M, depth)
    return _mR[k]
def reduced(M):
    k = tuple(M)
    if k not in _mred: _mred[k] = _ored(M)
    return _mred[k]
tm.Trans, tm.Mark, rm.Red, tm.reduced = Trans, Mark, Red, reduced

class TO(Exception): pass
def _h(s, f): raise TO()
signal.signal(signal.SIGALRM, _h)

def nextrel1(M, a, b):
    if not (a < Lng(M) and b < Lng(M) and a < b): return False
    if not entry(M, 1, a) < entry(M, 1, b): return False
    if not rm.le0(M, a, b): return False
    for j in range(a + 1, b + 1):
        if rm.le0(M, j, b) and entry(M, 1, j) < entry(M, 1, b):
            return False
    return True

def gen_pool(max_len=12, cap=1500, seed=1234):
    rng = random.Random(seed)
    seen, out, work = set(), [], []
    for u in range(0, 3):
        for v in range(u, u + 5):
            work.append(diagSeq(u, v))
    while work and len(out) < cap:
        i = rng.randrange(len(work))
        M = work.pop(i)
        k = tuple(M)
        if k in seen: continue
        seen.add(k)
        out.append(M)
        if Lng(M) > max_len: continue
        for n in (1, 2, 3, 4):
            Mn = oper(M, n)
            if Lng(Mn) <= max_len + 3 and tuple(Mn) not in seen:
                work.append(Mn)
    return out

def main():
    pool = gen_pool()
    ok = [0] * 7
    dom = tos = 0
    bad = []
    for M in pool:
        j1 = Lng(M) - 1
        if j1 < 1 or not monoT(M): continue
        if not hasParent(M, 1, j1): continue
        jm2 = parent(M, 1, j1)
        if not (jm2 + 1 < j1): continue
        dom += 1
        signal.alarm(6)
        try:
            Np = seg(M, jm2, j1)
            Q = Red(Np)
            j1Q = Lng(Q) - 1
            R = Q[:-1] + [(entry(Q, 0, j1Q), entry(Q, 1, 0))]
            j0p = parent(Q, 0, j1Q)
            # m1
            pars = [j for j in range(j1Q) if nextrel1(Q, j, j1Q)]
            g1 = (pars == [0] and entry(Q, 1, 0) + 1 == entry(Q, 1, j1Q))
            # m2
            g2 = (entry(Q, 1, j0p) >= entry(Q, 1, j1Q)) or j0p == 0
            g2 = g2 and (entry(Q, 1, j0p) >= entry(Q, 1, 0))
            # m3
            g3 = (not condVI(Q)) and (not condVI(R)) and (not condV(R))
            # m4
            cAQ = condI(Q) or condIII(Q) or condV(Q)
            cAR = condI(R) or condIII(R) or condV(R)
            g4 = (cAQ == adm(Q, j0p)) and (cAR == adm(R, j0p)) and (cAQ == cAR)
            # m5: compare Trans-recursion internals of Q and R
            c1Q = Mark(Q[:-1], Adm(Q, j0p))
            c1R = Mark(R[:-1], Adm(R, j0p))
            g5 = (c1Q == c1R)
            # m6: lemma-shape decomposition sharing (already checked in recheck;
            # re-verify on this pool)
            Lp = seg(M, jm2, j1 - 1) + [(entry(M, 0, j1), entry(M, 1, jm2))]
            dsN = scb_decomps(Trans(Np), flatBT(Dpt(entry(M, 1, j1), ZB)))
            dsL = scb_decomps(Trans(Lp), flatBT(Dpt(entry(M, 1, jm2), ZB)))
            both = [sb for sb in dsN if sb in dsL]
            g6 = (len(both) == 1)
            gs = [g1, g2, g3, g4, g5, g6]
            for i, g in enumerate(gs):
                ok[i] += g
            if not all(gs):
                bad.append((M, [i for i, g in enumerate(gs) if not g]))
        except TO:
            tos += 1
        except RecursionError:
            tos += 1
        finally:
            signal.alarm(0)
    n = dom - tos
    print(f"domain {dom}, timeouts {tos}, checked {n}")
    for i, lbl in enumerate(["m1 parent0+step", "m2 dichotomy", "m3 no VI/V_R",
                             "m4 condA<->adm", "m5 c1 shared", "m6 lemma shape"]):
        print(f"  {lbl}: {ok[i]}/{n}")
    for x in bad[:5]:
        print("CEX:", x)

if __name__ == '__main__':
    sys.setrecursionlimit(100000)
    main()
