#!/usr/bin/env python3
"""r47 STEP-0b (head-gap agent): psne-focused validation of the hgx_ residuals.

Residual set to validate on real keystone hosts (esp. ps != []):
  depdomV0 : all y in {qq} u G(v0,qq): lt(y, [D(x,qq)])   (= qltdep & depdom)
  headgap  : idx(hd qq) <= x
  deple    : ps==[] or le([D(x,qq)], [last ps])           (C2 conclusion)
  qcore/Gcore : the exact slotAppg core conclusions
Also machine-checks the two abstract counterexamples showing depOT alone
(and depOT+headgap) do NOT imply the cores.
"""
import sys, time, signal, random
from collections import deque
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
from red_model import Lng, oper, diagSeq, monoT, Br, entry
import trans_model as tm
import buchholz as bu

sys.setrecursionlimit(200000)
random.seed(147)

_torig = tm.Trans
_tmemo = {}
def Trans(M, depth=0):
    k = tuple(M); r = _tmemo.get(k)
    if r is None:
        r = _torig(M, depth); _tmemo[k] = r
    return r
tm.Trans = Trans

def bucOf(t):
    return [('D', p[1], bucOf(p[2])) for p in t[1]]

class TO(Exception): pass
signal.signal(signal.SIGALRM, lambda s, f: (_ for _ in ()).throw(TO()))

# ---- abstract CEX checks (depOT alone / depOT+headgap insufficient) ----
ZERO = []
q1 = [('D', 5, ZERO)]                       # q = D_5 0, x = 2
dep1 = [('D', 2, q1)]
print("CEX1 q=[D_5 0] x=2: in_OT(dep)=%s  qltdep=%s (expect True/False)" %
      (bu.in_OT(dep1), bu.lt_term(q1, dep1)))
q2 = [('D', 1, [('D', 9, ZERO)])]           # q = D_1(D_9 0), x = 2, v0 = 0
dep2 = [('D', 2, q2)]
g0 = bu.G(0, q2)
print("CEX2 q=[D_1[D_9 0]] x=2 v0=0: in_OT(dep)=%s headgap=%s "
      "Gdom=%s (expect True/True/False)" %
      (bu.in_OT(dep2), q2[0][1] <= 2,
       all(bu.lt_term(y, dep2) for y in g0)))

# ---- corpus ----
T_BFS   = float(sys.argv[1]) if len(sys.argv) > 1 else 90.0
T_CHECK = float(sys.argv[2]) if len(sys.argv) > 2 else 170.0
PER     = int(sys.argv[3]) if len(sys.argv) > 3 else 8

seeds = [diagSeq(u, u + d) for u in range(0, 6) for d in range(1, 7)]
seen = set(); q = deque(seeds)
t0 = time.time()
# phase 1: dense small space (cap 18), phase 2: wider (cap 40)
for cap, frac in ((18, 0.55), (40, 1.0)):
    while q and time.time() - t0 < T_BFS * frac and len(seen) < 400000:
        M = q.popleft(); k = tuple(M)
        if k in seen: continue
        seen.add(k)
        if Lng(M) <= cap - 1:
            for nn in range(1, 8):
                try: M2 = oper(M, nn)
                except Exception: continue
                if M2 != M and len(M2) <= cap and tuple(M2) not in seen:
                    q.append(M2)
    q = deque(list(seen))     # re-expand from everything with the larger cap
print("BFS visited=%d maxLng=%d (%.0fs)" %
      (len(seen), max(len(m) for m in seen), time.time() - t0), flush=True)

KEYS = ['depOT', 'headgap', 'qltdep', 'depdom', 'deple', 'qcore', 'Gcore']
R  = dict((k, 0) for k in KEYS); R.update(applic=0, skip=0, qzero=0, novle=0)
RP = dict((k, 0) for k in KEYS); RP.update(applic=0)   # psne-only tallies
failsA = []; psne_ex = []
checked = set(); maxLapp = 0; maxLpsne = 0

def check_host(M):
    global maxLapp, maxLpsne
    v0 = entry(M, 1, 0)
    signal.alarm(PER)
    try:
        TM = Trans(M); TPM = Trans(tm.Pred(M)); signal.alarm(0)
    except (TO, Exception):
        signal.alarm(0); R['skip'] += 1; return False
    if len(TM[1]) != 1 or TM[1][0][1] != v0 or not TM[1][0][2][1] \
       or len(TPM[1]) != 1 or TPM[1][0][1] != v0:
        return True
    lM = bucOf(TM[1][0][2]); lPM = bucOf(TPM[1][0][2])
    ps = lM[:-1]; x, qq = lM[-1][1], lM[-1][2]
    if lPM[:len(ps)] != ps: return True
    if not (v0 <= x): R['novle'] += 1; return True
    if not qq: R['qzero'] += 1; return True
    L = len(M)
    signal.alarm(PER)
    try:
        dep   = [('D', x, qq)]
        whole = ps + dep
        gv0   = bu.G(v0, qq)
        res = {}
        res['depOT']   = bu.in_OT(dep)
        res['headgap'] = qq[0][1] <= x
        res['qltdep']  = bu.lt_term(qq, dep)
        res['depdom']  = all(bu.lt_term(y, dep) for y in gv0)
        res['deple']   = (not ps) or bu.le_term(dep, [ps[-1]])
        res['qcore']   = bu.lt_term(qq, whole)
        res['Gcore']   = all(bu.lt_term(y, whole) for y in gv0)
        signal.alarm(0)
    except (TO, Exception):
        signal.alarm(0); R['skip'] += 1; return False
    R['applic'] += 1; maxLapp = max(maxLapp, L)
    for k in KEYS:
        if res[k]: R[k] += 1
    if ps:
        RP['applic'] += 1; maxLpsne = max(maxLpsne, L)
        for k in KEYS:
            if res[k]: RP[k] += 1
        if len(psne_ex) < 5:
            psne_ex.append((L, list(M), v0, x, len(ps), dict(res)))
    if not (res['qltdep'] and res['depdom'] and res['headgap'] and
            res['deple'] and res['qcore'] and res['Gcore']):
        if len(failsA) < 5:
            failsA.append((L, list(M), v0, x, len(ps), dict(res)))
    return True

vis = sorted(seen, key=lambda m: -len(m))
random.shuffle(vis)
tC = time.time()
for E in vis:
    if time.time() - tC > T_CHECK: break
    for kk in range(4, len(E) + 1):
        if time.time() - tC > T_CHECK + 15: break
        M = list(E[:kk]); km = tuple(M)
        if km in checked: continue
        checked.add(km)
        if not (monoT(M) and Br(M) != []): continue
        if len(M) - 1 <= 1: continue
        if not check_host(M): break

print("hosts checked(uniq)=%d in %.0fs skips=%d qzero=%d novle=%d" %
      (len(checked), time.time() - tC, R['skip'], R['qzero'], R['novle']))
print("APPLICABLE=%d maxLng=%d   PSNE(ps!=[])=%d maxLngPsne=%d" %
      (R['applic'], maxLapp, RP['applic'], maxLpsne))
for k in KEYS:
    print("  %-8s: ALL %d/%d   PSNE %d/%d" %
          (k, R[k], R['applic'], RP[k], RP['applic']))
for (L, M, v0, x, lps, res) in psne_ex:
    print("PSNE ex: Lng=%d v0=%s x=%s |ps|=%d M=%s\n   res=%s" %
          (L, v0, x, lps, M, res))
for (L, M, v0, x, lps, res) in failsA:
    print("RESID-FAIL: Lng=%d v0=%s x=%s |ps|=%d M=%s\n   res=%s" %
          (L, v0, x, lps, M, res))
