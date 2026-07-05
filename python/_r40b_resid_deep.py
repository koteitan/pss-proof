#!/usr/bin/env python3
"""r40b STEP-0: DEEP validation of the §8.7 OT keystone residual `resid`
(sole open hypothesis of m_8_7_Trans_OT_step_keystone).

For M in ST_PS, monoT M, Br M != [], Lng M - 1 > 1, with the (unique)
decomposition Trans M = D_v0(Trm (ps @ [DB x q])) and
Trans(Pred M) = D_v0(Trm (ps @ rs)):
  C1: isOT_BP (DB x q)
  C2: ps != [] --> leBT (Dpt x q) (Trm [last ps])
  C3: ALL y in GBT v0 body. lessBT y body   (body = Trm (ps@[DB x q]))

Corpus regime = the one that refuted pcompPrefix (r40): oper-BFS from
diagSeq(u,v) seeds INCLUDING u>0, deep endpoints (Lng>=16), plus prefix
closure (prefixes of standard are standard, m_6_7_standard_prefix).
Strategy: walk prefix chains of deep endpoints; memoized Trans makes each
prefix step incremental.
"""
import sys, time, signal, random
from collections import deque
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import Lng, oper, diagSeq, monoT, Br, entry
import trans_model as tm
import buchholz as bu

sys.setrecursionlimit(200000)
random.seed(40)

# ---- memoized Trans / Mark (patched into the module so recursion shares) ----
_torig, _morig = tm.Trans, tm.Mark
_tmemo, _mmemo = {}, {}
def Trans(M, depth=0):
    k = tuple(M)
    r = _tmemo.get(k)
    if r is None:
        r = _torig(M, depth)
        _tmemo[k] = r
    return r
def Mark(M, m, depth=0):
    k = (tuple(M), m)
    r = _mmemo.get(k)
    if r is None:
        r = _morig(M, m, depth)
        _mmemo[k] = r
    return r
tm.Trans, tm.Mark = Trans, Mark

def bucOf(t):
    return [('D', p[1], bucOf(p[2])) for p in t[1]]

class TO(Exception): pass
signal.signal(signal.SIGALRM, lambda s, f: (_ for _ in ()).throw(TO()))

T_BFS   = float(sys.argv[1]) if len(sys.argv) > 1 else 75.0
T_CHECK = float(sys.argv[2]) if len(sys.argv) > 2 else 480.0
LNG_CAP = int(sys.argv[3]) if len(sys.argv) > 3 else 48
PER     = int(sys.argv[4]) if len(sys.argv) > 4 else 10
VIS_CAP = 250000

# ---- BFS over TRUE ST_PS (oper closure of diagonals, u>0 included) ----
seeds = [diagSeq(u, u + d) for u in range(0, 8) for d in range(1, 9)]
seen = set(); q = deque(seeds)
t0 = time.time()
while q and time.time() - t0 < T_BFS and len(seen) < VIS_CAP:
    M = q.popleft(); k = tuple(M)
    if k in seen: continue
    seen.add(k)
    if Lng(M) <= 40:
        for nn in range(1, 7):
            try: M2 = oper(M, nn)
            except Exception: continue
            if M2 != M and len(M2) <= LNG_CAP and tuple(M2) not in seen:
                q.append(M2)
maxvis = max(len(m) for m in seen)
print("BFS: visited=%d maxLng=%d (%.0fs)" % (len(seen), maxvis, time.time() - t0),
      flush=True)

# ---- endpoint selection: deep chains first, plus a broad shallow sample ----
vis = list(seen)
deepE = [m for m in vis if len(m) >= 16]
midE  = [m for m in vis if 10 <= len(m) < 16]
shal  = [m for m in vis if 4 <= len(m) < 10]
random.shuffle(deepE); random.shuffle(midE); random.shuffle(shal)
deepE.sort(key=lambda m: -len(m))
# order: all shallow (cheap, minimal-CEX hunt) -> mid sample -> deep chains
chains = shal[:20000] + midE[:6000] + deepE[:3000]
print("chains: shallow=%d mid=%d deep=%d (deepest=%d)" %
      (min(len(shal), 20000), min(len(midE), 6000), min(len(deepE), 3000),
       deepE and len(deepE[0]) or 0), flush=True)

R = dict(applic=0, c1=0, c2=0, c3=0, allok=0,
         d12=0, d12ok=0, d16=0, d16ok=0, d20=0, d20ok=0,
         inap_shape=0, inap_pref=0, skip_to=0)
c1f, c2f, c3f = [], [], []
maxLapp = 0
checked = set()
tC = time.time()

def check_host(M):
    global maxLapp
    v0 = entry(M, 1, 0)
    signal.alarm(PER)
    try:
        TM = Trans(M); TPM = Trans(tm.Pred(M))
        signal.alarm(0)
    except (TO, Exception):
        signal.alarm(0); R['skip_to'] += 1; return False
    if len(TM[1]) != 1 or TM[1][0][1] != v0 or not TM[1][0][2][1] \
       or len(TPM[1]) != 1 or TPM[1][0][1] != v0:
        R['inap_shape'] += 1; return True
    lM = bucOf(TM[1][0][2]); lPM = bucOf(TPM[1][0][2])
    ps = lM[:-1]; x, qq = lM[-1][1], lM[-1][2]
    if lPM[:len(ps)] != ps:
        R['inap_pref'] += 1; return True
    L = len(M)
    signal.alarm(PER)
    try:
        c1 = bu.in_OT([('D', x, qq)])
        c2 = bu.le_term([('D', x, qq)], [ps[-1]]) if ps else True
        c3 = bu.G_lt(v0, lM, lM)
        signal.alarm(0)
    except (TO, Exception):
        signal.alarm(0); R['skip_to'] += 1; return False
    R['applic'] += 1; maxLapp = max(maxLapp, L)
    if c1: R['c1'] += 1
    else: c1f.append((L, M, x, qq))
    if c2: R['c2'] += 1
    else: c2f.append((L, M, x, qq, ps[-1]))
    if c3: R['c3'] += 1
    else: c3f.append((L, M))
    ok = c1 and c2 and c3
    if ok: R['allok'] += 1
    for lb, kk in ((12, 'd12'), (16, 'd16'), (20, 'd20')):
        if L >= lb:
            R[kk] += 1
            if ok: R[kk + 'ok'] += 1
    return True

nE = 0
for E in chains:
    if time.time() - tC > T_CHECK: break
    nE += 1
    dead = False
    for kk in range(3, len(E) + 1):
        M = list(E[:kk])
        km = tuple(M)
        if km in checked:
            continue
        checked.add(km)
        if not (monoT(M) and Br(M) != []):
            continue
        if len(M) - 1 <= 1:
            continue
        if not check_host(M):
            dead = True; break        # Trans timeout: longer prefixes hopeless
    if dead: continue

print("chains walked=%d  hosts checked(uniq)=%d in %.0fs  skips/timeouts=%d" %
      (nE, len(checked), time.time() - tC, R['skip_to']), flush=True)
print("inapplicable: shape=%d prefix-mismatch=%d" % (R['inap_shape'], R['inap_pref']))
print("APPLICABLE=%d maxLng=%d" % (R['applic'], maxLapp))
if R['applic']:
    print(" C1 isOT_BP  : %d/%d" % (R['c1'], R['applic']))
    print(" C2 head-step: %d/%d" % (R['c2'], R['applic']))
    print(" C3 GBT bound: %d/%d" % (R['c3'], R['applic']))
    print(" ALL         : %d/%d" % (R['allok'], R['applic']))
    print(" DEEP Lng>=12: %d/%d  Lng>=16: %d/%d  Lng>=20: %d/%d" %
          (R['d12ok'], R['d12'], R['d16ok'], R['d16'], R['d20ok'], R['d20']))
for tag, fl in (('C1', c1f), ('C2', c2f), ('C3', c3f)):
    if fl:
        fl.sort(key=lambda t: t[0])
        print("== %s FAILURES: %d (minimal first)" % (tag, len(fl)))
        for it in fl[:6]:
            print("   Lng=%d M=%s" % (it[0], it[1]), it[2:] if len(it) > 2 else '')
