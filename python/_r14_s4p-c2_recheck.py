#!/usr/bin/env python3
"""r14-S4p-C2 spot-recheck of m_8_4_rightend_Trans (fresh seed) + proof-plan
invariants used by the Isar proof:
  (a) the exact lemma shape: unique (s,b) with
        scb_decomp (Trans N') s (flat (D_{M1,j1} 0)) b  AND
        scb_decomp (Trans L') s (flat (D_{M1,jm2} 0)) b
  (b) R := butlast(Red N') + [(e0(RN,last), e1(RN,0))] is reduced & mono,
      L' = IncrFirst^k R with k = e0(M,jm2) - e1(M,jm2), Red L' = R
  (c) adm/Adm/transJ0/c1 agreement between RN and R; branch classification match
"""
import sys, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
import red_model as rm
from red_model import (Lng, entry, parent, hasParent, seg, oper, monoT, diagSeq)
import trans_model as tm
from trans_model import (ZB, Dpt, addBT, flatBT, scb_decomps, adm, Adm,
                         condI, condIII, condV, condVI, bpHeadT, bpHeadV)

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

def Pred(M): return M[:-1] if Lng(M) > 1 else M
def Dj(u): return Dpt(u, ZB)

def gen_pool(max_len=12, cap=1500, seed=42):
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
    okA = okB = okC = 0
    bad = []
    tos = 0
    dom = 0
    for M in pool:
        j1 = Lng(M) - 1
        if j1 < 1 or not monoT(M): continue
        if not hasParent(M, 1, j1): continue
        jm2 = parent(M, 1, j1)
        if not (jm2 + 1 < j1): continue
        dom += 1
        signal.alarm(6)
        try:
            j0 = parent(M, 0, j1)
            Np = seg(M, jm2, j1)
            Lp = seg(M, jm2, j1 - 1) + [(entry(M, 0, j1), entry(M, 1, jm2))]
            TN, TL = Trans(Np), Trans(Lp)
            # (a) exact lemma shape
            dsN = scb_decomps(TN, flatBT(Dj(entry(M, 1, j1))))
            dsL = scb_decomps(TL, flatBT(Dj(entry(M, 1, jm2))))
            both = [sb for sb in dsN if sb in dsL]
            ga = (len(both) == 1)
            okA += ga
            if not ga: bad.append((M, 'a', len(dsN), len(dsL), len(both)))
            # (b) R construction
            RN = Red(Np)
            j1p = Lng(RN) - 1
            R = RN[:-1] + [(entry(RN, 0, j1p), entry(RN, 1, 0))]
            k = entry(M, 0, jm2) - entry(M, 1, jm2)
            IFkR = [(a + k, b) for (a, b) in R]
            gb = (reduced(R) and monoT(R) and IFkR == Lp and Red(Lp) == R)
            okB += gb
            if not gb: bad.append((M, 'b'))
            # (c) agreement + branch match
            jpN = parent(RN, 0, j1p); jpR = parent(R, 0, j1p)
            admeq = adm(RN, jpN) == adm(R, jpR)
            Admeq = Adm(RN, jpN) == Adm(R, jpR)
            c1N = Mark(Pred(RN), Adm(RN, jpN)); c1R = Mark(Pred(R), Adm(R, jpR))
            b1N = condI(RN) or condIII(RN) or condV(RN)
            b1R = condI(R) or condIII(R) or condV(R)
            gc = (jpN == jpR and admeq and Admeq and c1N == c1R
                  and b1N == b1R and not condVI(RN) and not condVI(R)
                  and (b1N or bpHeadT(c1N) == bpHeadT(c1R)))
            okC += gc
            if not gc: bad.append((M, 'c', jpN, jpR, admeq, Admeq, b1N, b1R))
        except TO:
            tos += 1
        except RecursionError:
            tos += 1
        finally:
            signal.alarm(0)
    print(f"domain instances: {dom}, timeouts/skips: {tos}", flush=True)
    print(f"(a) lemma shape unique-both: {okA}/{dom - tos}")
    print(f"(b) R reduced&mono & L'=IF^k R & Red L' = R: {okB}/{dom - tos}")
    print(f"(c) agreement & branch match: {okC}/{dom - tos}")
    for x in bad[:6]: print("CEX:", x)

if __name__ == '__main__':
    sys.setrecursionlimit(100000)
    main()
