#!/usr/bin/env python3
"""r14-S5: hunt for genuine ST_PS x PT_PS instances with condV and NON-adm j0
(the regime of lemma (i) 条件(V)の下での各種scb分解).  BFS over oper-expansions
of diagonal seeds."""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s5/python')
from red_model import Lng, entry, parent, oper, diagSeq, monoT
import trans_model as tm
from trans_model import Trans, Pred, adm, condV, reduced, ZB

class TimeoutErr(Exception): pass
def _handler(signum, frame): raise TimeoutErr()
signal.signal(signal.SIGALRM, _handler)

def safe(f, *a, budget=2):
    signal.alarm(budget)
    try:
        r = f(*a); signal.alarm(0); return r
    except Exception:
        signal.alarm(0); return None

def hunt(tmax=240, maxlen=18, seeds=8):
    t0 = time.time()
    found = []
    seen = set()
    frontier = [diagSeq(u, u + k) for u in range(3) for k in range(1, 4)]
    rng = random.Random(7)
    while frontier and time.time() - t0 < tmax:
        M = frontier.pop(rng.randrange(len(frontier)))
        key = tuple(M)
        if key in seen: continue
        seen.add(key)
        if Lng(M) > maxlen: continue
        # check
        j1 = Lng(M) - 1
        if j1 > 1 and monoT(M) and safe(reduced, M, budget=1) is True and condV(M):
            j0 = parent(M, 0, j1)
            if not adm(M, j0):
                t1 = safe(Trans, Pred(M), budget=2)
                if t1 is not None and t1 != ZB:
                    found.append(M)
                    print('FOUND nonadm condV:', M, flush=True)
        for n in (1, 2, 3, 4):
            M2 = safe(oper, M, n, budget=1)
            if M2 is not None and M2 != M and Lng(M2) <= maxlen:
                frontier.append(M2)
    print('total found:', len(found), 'seen:', len(seen))
    return found

if __name__ == '__main__':
    tmax = float(sys.argv[1]) if len(sys.argv) > 1 else 240
    hunt(tmax)
