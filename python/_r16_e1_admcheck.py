#!/usr/bin/env python3
"""r16-E1: DEEP empirical validation of the condV adm-vacuity
    M in ST_PS cap PT_PS, transCondV M  ==>  adm M j0   (j0 = parent M 0 (Lng M-1))
across THREE regimes (to pick the weakest true hypothesis set for the proof):
  [ST]  genuine ST_PS (diagSeq seeds closed under oper), DEEP mining:
        ns weighted to {1,2}, long chains, maxlen up to 26, Lng>=9 tracked
        separately (verify-rank-depth lesson: condIV vacuity refuted at Lng>=9).
  [RT]  random RT_PS cap PT_PS (reduced mono, NOT nec. standard): brute
        small-tuple search (as in _r6_u_nonzero_search's reduced() route).
  [DT]  the RT pool filtered by descending(Br M) (= DT_PS).
Also tallies, on the condV instances, WHERE j0 sits (0 / interior trunk /
TrMax / above trunk) and which nadm edge would fire -- proof-route data.
Run: python3 _r16_e1_admcheck.py [secs_ST] [secs_RT] [seed]
"""
import sys, time, signal, random, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import Lng, entry, parent, hasParent, oper, seg, diagSeq, monoT, zeroT, P
import red_model as rm
from trans_model import adm, Adm, condV, reduced

class TimeoutErr(Exception): pass
def _handler(signum, frame): raise TimeoutErr()
signal.signal(signal.SIGALRM, _handler)

def safe(f, *a, budget=3):
    signal.alarm(budget)
    try:
        r = f(*a); signal.alarm(0); return r
    except Exception:
        signal.alarm(0); return None

TrMax = rm.TrMax
Br_list = rm.Br

def descending(Q):
    for J0 in range(len(Q)):
        for J1 in range(J0, len(Q)):
            a0, b0 = entry(Q[J0],0,0), entry(Q[J0],1,0)
            a1, b1 = entry(Q[J1],0,0), entry(Q[J1],1,0)
            if not (a0 >= a1 and (a0 != a1 or b0 >= b1)): return False
    return True

def classify_j0(M, j0):
    tm = TrMax(M)
    if j0 == 0: return 'zero'
    if j0 < tm: return 'trunk-int'
    if j0 == tm: return 'TrMax'
    if j0 == tm + 1: return 'TrMax+1'
    return 'branch'

STAT = {'inst':0, 'deep':0, 'adm':0, 'nonadm':0, 'nonadm_deep':0}
CLS = {}
CEX = []

def note(M, tag):
    j1 = Lng(M) - 1
    j0 = parent(M, 0, j1)
    a = adm(M, j0)
    STAT['inst'] += 1
    deep = Lng(M) >= 9
    if deep: STAT['deep'] += 1
    c = classify_j0(M, j0) + ('/adm' if a else '/NADM')
    CLS[(tag,c)] = CLS.get((tag,c), 0) + 1
    if a:
        STAT['adm'] += 1
    else:
        STAT['nonadm'] += 1
        if deep: STAT['nonadm_deep'] += 1
        if len(CEX) < 8: CEX.append((tag, M))

def run_ST(tmax, rng):
    t0 = time.time(); seen = set(); pool = 0
    while time.time() - t0 < tmax:
        u = rng.randrange(0, 6)
        vv = u + rng.randrange(1, 7)
        M = diagSeq(u, vv)
        steps = rng.randrange(6, 30)
        for _ in range(steps):
            if time.time() - t0 > tmax: break
            # weight n: mostly 1..2 (deep braiding), sometimes 3..4
            n = rng.choice((1,1,1,2,2,2,2,3,4))
            M2 = safe(oper, M, n, budget=2)
            if M2 is None or M2 == M or Lng(M2) > 26: break
            M = M2
            key = tuple(M)
            if key in seen: continue
            seen.add(key); pool += 1
            j1 = Lng(M) - 1
            if j1 <= 1 or not monoT(M): continue
            if not condV(M): continue
            note(M, 'ST')
    return pool

def run_RT(tmax, rng):
    """random reduced mono hosts (RT cap PT), condV filter; also DT tag."""
    t0 = time.time(); seen = set(); pool = 0
    maxv = 4
    while time.time() - t0 < tmax:
        L = rng.randrange(4, 11)
        M = []
        e0 = rng.randrange(0, 3); e1 = e0
        M.append((e0, e1))
        for _ in range(L-1):
            M.append((rng.randrange(0, maxv+3), rng.randrange(0, maxv+2)))
        key = tuple(M)
        if key in seen: continue
        seen.add(key)
        if not M: continue
        if not monoT(M): continue
        if not safe(reduced, M, budget=2): continue
        pool += 1
        j1 = Lng(M) - 1
        if j1 <= 1 or not condV(M): continue
        note(M, 'RT')
        if descending(Br_list(M)):
            note(M, 'DT')
    return pool

def main():
    tst = float(sys.argv[1]) if len(sys.argv) > 1 else 240
    trt = float(sys.argv[2]) if len(sys.argv) > 2 else 120
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 20260702
    rng = random.Random(seed)
    p1 = run_ST(tst, rng)
    p2 = run_RT(trt, rng)
    print('pool ST=%d RT=%d' % (p1, p2))
    print('condV instances: %(inst)d (deep Lng>=9: %(deep)d); '
          'adm=%(adm)d nonadm=%(nonadm)d (nonadm deep=%(nonadm_deep)d)' % STAT)
    for k in sorted(CLS): print('  %-24s %d' % ('%s %s' % k, CLS[k]))
    for tag, M in CEX: print('CEX [%s] %s  j0=%d TrMax=%d' %
        (tag, M, parent(M,0,Lng(M)-1), TrMax(M)))

if __name__ == '__main__':
    main()
