#!/usr/bin/env python3
"""r16-E1: chain-recording search for NON-ADM condV instances in genuine ST_PS.
Records the full oper chain (seed + n-list) of every hit; replays each chain
step-by-step, asserting reducedness (ST_PS subseteq RT_PS is a theorem: a
non-reduced intermediate would indicate a python model bug, not a genuine hit).
Run: python3 _r16_e1_chains.py [secs] [seed]
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import Lng, entry, parent, oper, diagSeq, monoT
import red_model as rm
from trans_model import adm, condV, reduced

class TimeoutErr(Exception): pass
def _handler(signum, frame): raise TimeoutErr()
signal.signal(signal.SIGALRM, _handler)

def safe(f, *a, budget=3):
    signal.alarm(budget)
    try:
        r = f(*a); signal.alarm(0); return r
    except Exception:
        signal.alarm(0); return None

def main():
    tmax = float(sys.argv[1]) if len(sys.argv) > 1 else 60
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20260702
    rng = random.Random(seed)
    t0 = time.time(); seen = set()
    hits = []
    ninst = 0
    while time.time() - t0 < tmax:
        u = rng.randrange(0, 6)
        vv = u + rng.randrange(1, 7)
        M = diagSeq(u, vv)
        chain = [('diag', u, vv)]
        steps = rng.randrange(6, 30)
        for _ in range(steps):
            if time.time() - t0 > tmax: break
            n = rng.choice((1,1,1,2,2,2,2,3,4))
            M2 = safe(oper, M, n, budget=2)
            if M2 is None or M2 == M or Lng(M2) > 26: break
            M = M2
            chain = chain + [n]
            key = tuple(M)
            if key in seen: continue
            seen.add(key)
            j1 = Lng(M) - 1
            if j1 <= 1 or not monoT(M): continue
            if not condV(M): continue
            ninst += 1
            j0 = parent(M, 0, j1)
            if not adm(M, j0):
                hits.append((list(chain), M))
                if len(hits) >= 6:
                    break
        if len(hits) >= 6: break
    print('condV instances seen: %d; non-adm hits: %d' % (ninst, len(hits)))
    for chain, M in hits:
        print('CHAIN:', chain)
        print('  M =', M)
        # replay + verify
        tag, u, vv = chain[0]
        X = diagSeq(u, vv)
        ok = True
        for n in chain[1:]:
            X = oper(X, n)
            if not reduced(X):
                print('  !! NOT REDUCED after step n=%d: %s' % (n, X))
                ok = False
                break
        if ok:
            print('  replay ok: X == M:', X == M,
                  '; all intermediates reduced; final reduced:', reduced(X))
            j1 = Lng(M)-1; j0 = parent(M,0,j1)
            print('  j0=%d e1j0=%d e1j1=%d TrMax=%d adm=%s' %
                  (j0, entry(M,1,j0), entry(M,1,j1), rm.TrMax(M), adm(M,j0)))

if __name__ == '__main__':
    main()
