#!/usr/bin/env python3
"""r40b: deep RANDOM-WALK hunter for `resid` counterexamples.

Long random oper-walks from diagSeq(u,v) seeds (u>0 included) reach orbit
regions BFS cannot; every prefix of every walk node is standard
(m_6_7_standard_prefix), so each walk yields many deep keystone hosts.
Checks C1/C2/C3 on every applicable host; reports failures + deep counts.
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import Lng, oper, diagSeq, monoT, Br, entry
import trans_model as tm
import buchholz as bu

sys.setrecursionlimit(200000)
SEED = int(sys.argv[3]) if len(sys.argv) > 3 else 4242
random.seed(SEED)

_torig, _morig = tm.Trans, tm.Mark
_tmemo, _mmemo = {}, {}
def Trans(M, depth=0):
    k = tuple(M); r = _tmemo.get(k)
    if r is None:
        r = _torig(M, depth); _tmemo[k] = r
    return r
def Mark(M, m, depth=0):
    k = (tuple(M), m); r = _mmemo.get(k)
    if r is None:
        r = _morig(M, m, depth); _mmemo[k] = r
    return r
tm.Trans, tm.Mark = Trans, Mark

def bucOf(t): return [('D', p[1], bucOf(p[2])) for p in t[1]]

class TO(Exception): pass
signal.signal(signal.SIGALRM, lambda s, f: (_ for _ in ()).throw(TO()))

T_TOTAL = float(sys.argv[1]) if len(sys.argv) > 1 else 1500.0
LCAP    = int(sys.argv[2]) if len(sys.argv) > 2 else 44

R = dict(applic=0, allok=0, d12=0, d12ok=0, d16=0, d16ok=0,
         d20=0, d20ok=0, d24=0, d24ok=0, skip=0, walks=0)
FAILS = []
checked = set()
maxLapp = 0

def check_host(M):
    global maxLapp
    v0 = entry(M, 1, 0)
    signal.alarm(12)
    try:
        TM = Trans(M); TPM = Trans(tm.Pred(M))
        signal.alarm(0)
    except (TO, Exception):
        signal.alarm(0); R['skip'] += 1; return False
    if len(TM[1]) != 1 or TM[1][0][1] != v0 or not TM[1][0][2][1] \
       or len(TPM[1]) != 1 or TPM[1][0][1] != v0:
        return True
    lM = bucOf(TM[1][0][2]); lPM = bucOf(TPM[1][0][2])
    ps = lM[:-1]; x, qq = lM[-1][1], lM[-1][2]
    if lPM[:len(ps)] != ps: return True
    L = len(M)
    signal.alarm(12)
    try:
        c1 = bu.in_OT([('D', x, qq)])
        c2 = bu.le_term([('D', x, qq)], [ps[-1]]) if ps else True
        c3 = bu.G_lt(v0, lM, lM)
        signal.alarm(0)
    except (TO, Exception):
        signal.alarm(0); R['skip'] += 1; return False
    R['applic'] += 1; maxLapp = max(maxLapp, L)
    ok = c1 and c2 and c3
    if ok: R['allok'] += 1
    else: FAILS.append((L, M, c1, c2, c3))
    for lb in (12, 16, 20, 24):
        if L >= lb:
            R['d%d' % lb] += 1
            if ok: R['d%dok' % lb] += 1
    return True

t0 = time.time()
seeds = [diagSeq(u, u + d) for u in range(0, 9) for d in range(1, 10)]
while time.time() - t0 < T_TOTAL:
    M = list(random.choice(seeds))
    R['walks'] += 1
    for step in range(300):
        if time.time() - t0 > T_TOTAL: break
        nn = random.choice([1, 1, 2, 2, 3, 3, 4, 5, 6, 7, 8])
        try: M2 = oper(M, nn)
        except Exception: break
        if len(M2) > LCAP:
            continue  # try a different n next step? just re-roll
        if M2 == M: break
        M = M2
        # walk the prefix chain of the current node (dedup)
        alive = True
        for kk in range(3, len(M) + 1):
            Mp = M[:kk]; km = tuple(Mp)
            if km in checked: continue
            checked.add(km)
            if not (len(Mp) - 1 > 1 and monoT(Mp) and Br(Mp) != []): continue
            if not check_host(Mp):
                alive = False; break
        if not alive: break

print("walks=%d hosts-uniq=%d (%.0fs, seed=%d)" %
      (R['walks'], len(checked), time.time() - t0, SEED))
print("APPLICABLE=%d maxLng=%d skips=%d" % (R['applic'], maxLapp, R['skip']))
print(" ALL ok      : %d/%d" % (R['allok'], R['applic']))
print(" DEEP >=12: %d/%d  >=16: %d/%d  >=20: %d/%d  >=24: %d/%d" %
      (R['d12ok'], R['d12'], R['d16ok'], R['d16'],
       R['d20ok'], R['d20'], R['d24ok'], R['d24']))
if FAILS:
    FAILS.sort(key=lambda t: t[0])
    print("== FAILURES: %d (minimal first)" % len(FAILS))
    for L, M, c1, c2, c3 in FAILS[:8]:
        print("   Lng=%d c1=%s c2=%s c3=%s M=%s" % (L, c1, c2, c3, M))
else:
    print("== NO FAILURES ==")
