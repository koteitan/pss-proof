#!/usr/bin/env python3
"""r77: NON-VACUITY + truth check of §8.4 part (2) restricted to the condIV admeq
corner  Adm(j_-2) = j_-1  (equivalently j_-3 = j_-1, where ltJ FAILS).

Reuses the r74 harness (CORRECTED operB from buchholz.py).
Reports: how many condIII/IV hosts, how many are in the admeq corner (non-vacuity),
and whether part (2) holds there.
"""
import sys, time, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4c/python')
from red_model import Lng, entry, parent, oper, diagSeq, monoT, hasParent, reduced
from trans_model import Trans, adm, Adm
from _r74_84_operbasic import operB, condIII, condIV, op1pow
from _r15_vx_lib import guarded, SKIP


def transJ0(M):
    return parent(M, 0, Lng(M) - 1)


def transJm1(M):
    return Adm(M, transJ0(M))


def jm2(M):
    return parent(M, 1, Lng(M) - 1)


def jm3(M):
    return Adm(M, jm2(M))


def mine(tmax, rng, want):
    t0 = time.time(); seen = set(); out = []
    while time.time() - t0 < tmax and len(out) < want:
        u = rng.randrange(0, 5); v = u + rng.randrange(1, 7)
        M = diagSeq(u, v)
        for _ in range(rng.randrange(4, 30)):
            if time.time() - t0 > tmax:
                break
            k = rng.choice((1, 1, 1, 2, 2, 2, 3, 3, 4, 5))
            try:
                M2 = oper(M, k)
            except Exception:
                break
            if not M2 or M2 == M or Lng(M2) > 15:
                break
            M = M2
            key = tuple(M)
            if key in seen:
                continue
            seen.add(key)
            j1 = Lng(M) - 1
            if j1 <= 1 or not monoT(M):
                continue
            if not hasParent(M, 1, j1):
                continue
            if not (condIII(M) or condIV(M)):
                continue
            out.append(list(M))
    return [list(t) for t in dict.fromkeys(tuple(m) for m in out)]


def main():
    tmine = float(sys.argv[1]) if len(sys.argv) > 1 else 90
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 777
    rng = random.Random(seed)
    hosts = mine(tmine, rng, 400)
    print('mined condIII/IV hosts (hasParent row1, j1>1):', len(hosts), flush=True)
    n_III = n_IV = n_admeq = n_ltJ = 0
    corner = []
    for M in hosts:
        if condIII(M):
            n_III += 1
        else:
            n_IV += 1
        if jm3(M) == transJm1(M):
            n_admeq += 1
            corner.append(M)
            if condIII(M):
                print('  !! admeq under condIII (contradicts the dichotomy):', M)
        else:
            n_ltJ += 1
    print(f'condIII {n_III}  condIV {n_IV}   ltJ {n_ltJ}   ADMEQ CORNER {n_admeq}',
          flush=True)

    ok = bad = skip = 0
    cex = []
    for hi, M in enumerate(corner):
        j1 = Lng(M) - 1; e = jm2(M)
        for n in (1, 2, 3):
            Mn1 = guarded(oper, M, n + 1, budget=8)
            TM = guarded(Trans, M, budget=25)
            if Mn1 is SKIP or TM is SKIP:
                skip += 1; continue
            it2 = j1 - 1 - e if j1 - 1 >= e else None
            if it2 is None:
                skip += 1; continue
            lhs = guarded(operB, TM, n - 1, budget=25)
            L = guarded(op1pow, Mn1, it2, budget=8)
            rhs = SKIP if L is SKIP else guarded(Trans, L, budget=25)
            if lhs is SKIP or rhs is SKIP:
                skip += 1; continue
            if lhs == rhs:
                ok += 1
            else:
                bad += 1
                if len(cex) < 3:
                    cex.append((list(M), n))
    print(f'ADMEQ-CORNER part (2):  ok {ok}   BAD {bad}   skip {skip}', flush=True)
    for c in cex:
        print('  CEX', c)


if __name__ == '__main__':
    main()
