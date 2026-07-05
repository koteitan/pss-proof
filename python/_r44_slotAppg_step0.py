#!/usr/bin/env python3
"""r44 STEP-0: validate slotAppg (C3 core) — the APPENDED-PRINCIPAL G_B-bound.

For M in ST_PS, monoT M, Br M != [], Lng M - 1 > 1, with decomposition
  Trans M        = D_v0(Trm (ps @ [DB x q]))          (v0 = entry M 1 0)
  Trans(Pred M)  = D_v0(Trm (ps @ rs))
slotAppg claims:
  ALL y in GBT v0 (Dpt x q). lessBT y (Trm ps +_B Dpt x q)
i.e. all y in G(v0, [('D',x,q)]) satisfy lt_term(y, ps @ [('D',x,q)]).

Also split-check (rgx_appg_split, v0<=x only):
  qlt: v0<=x --> lt_term(q, ps@[('D',x,q)])
  Gq : v0<=x, y in G(v0,q) --> lt_term(y, ps@[('D',x,q)])
"""
import sys, time, signal, random
from collections import deque
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
from red_model import Lng, oper, diagSeq, monoT, Br, entry
import trans_model as tm
import buchholz as bu

sys.setrecursionlimit(200000)
random.seed(44)

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

def bucOf(t):
    return [('D', p[1], bucOf(p[2])) for p in t[1]]

class TO(Exception): pass
signal.signal(signal.SIGALRM, lambda s, f: (_ for _ in ()).throw(TO()))

T_BFS   = float(sys.argv[1]) if len(sys.argv) > 1 else 60.0
T_CHECK = float(sys.argv[2]) if len(sys.argv) > 2 else 300.0
LNG_CAP = int(sys.argv[3]) if len(sys.argv) > 3 else 44
PER     = int(sys.argv[4]) if len(sys.argv) > 4 else 10

seeds = [diagSeq(u, u + d) for u in range(0, 8) for d in range(1, 9)]
seen = set(); q = deque(seeds)
t0 = time.time()
while q and time.time() - t0 < T_BFS and len(seen) < 250000:
    M = q.popleft(); k = tuple(M)
    if k in seen: continue
    seen.add(k)
    if Lng(M) <= 40:
        for nn in range(1, 7):
            try: M2 = oper(M, nn)
            except Exception: continue
            if M2 != M and len(M2) <= LNG_CAP and tuple(M2) not in seen:
                q.append(M2)
print("BFS visited=%d maxLng=%d (%.0fs)" %
      (len(seen), max(len(m) for m in seen), time.time()-t0), flush=True)

vis = list(seen)
deepE = [m for m in vis if len(m) >= 16]
midE  = [m for m in vis if 10 <= len(m) < 16]
shal  = [m for m in vis if 4 <= len(m) < 10]
random.shuffle(deepE); random.shuffle(midE); random.shuffle(shal)
deepE.sort(key=lambda m: -len(m))
chains = shal[:20000] + midE[:6000] + deepE[:3000]

R = dict(applic=0, appg=0, qlt=0, Gq=0, vlex=0, allok=0,
         inap_shape=0, inap_pref=0, skip=0, d16=0, d16ok=0, d20=0, d20ok=0)
fails = []; checked = set(); maxLapp = 0
tC = time.time()

def check_host(M):
    global maxLapp
    v0 = entry(M, 1, 0)
    signal.alarm(PER)
    try:
        TM = Trans(M); TPM = Trans(tm.Pred(M)); signal.alarm(0)
    except (TO, Exception):
        signal.alarm(0); R['skip'] += 1; return False
    if len(TM[1]) != 1 or TM[1][0][1] != v0 or not TM[1][0][2][1] \
       or len(TPM[1]) != 1 or TPM[1][0][1] != v0:
        R['inap_shape'] += 1; return True
    lM = bucOf(TM[1][0][2]); lPM = bucOf(TPM[1][0][2])
    ps = lM[:-1]; x, qq = lM[-1][1], lM[-1][2]     # qq is buc term (list)
    if lPM[:len(ps)] != ps:
        R['inap_pref'] += 1; return True
    L = len(M)
    signal.alarm(PER)
    try:
        appP = [('D', x, qq)]                       # Dpt x q  (buc principal-list)
        whole = ps + [('D', x, qq)]                 # Trm ps +_B Dpt x q
        gset = bu.G(v0, appP)                        # GBT v0 (Dpt x q)
        appg = all(bu.lt_term(y, whole) for y in gset)
        vle = (v0 <= x)
        qlt = (not vle) or bu.lt_term(qq, whole)
        Gq  = (not vle) or all(bu.lt_term(y, whole) for y in bu.G(v0, qq))
        signal.alarm(0)
    except (TO, Exception):
        signal.alarm(0); R['skip'] += 1; return False
    R['applic'] += 1; maxLapp = max(maxLapp, L)
    if appg: R['appg'] += 1
    if qlt:  R['qlt'] += 1
    if Gq:   R['Gq'] += 1
    if vle:  R['vlex'] += 1
    ok = appg and qlt and Gq
    if ok: R['allok'] += 1
    else: fails.append((L, M, v0, x, qq, ps, appg, qlt, Gq))
    for lb, kk in ((16, 'd16'), (20, 'd20')):
        if L >= lb:
            R[kk] += 1
            if ok: R[kk+'ok'] += 1
    return True

for E in chains:
    if time.time() - tC > T_CHECK: break
    for kk in range(3, len(E)+1):
        M = list(E[:kk]); km = tuple(M)
        if km in checked: continue
        checked.add(km)
        if not (monoT(M) and Br(M) != []): continue
        if len(M) - 1 <= 1: continue
        if not check_host(M): break

print("hosts checked(uniq)=%d in %.0fs skips=%d" %
      (len(checked), time.time()-tC, R['skip']))
print("inapplicable shape=%d prefix-mismatch=%d" % (R['inap_shape'], R['inap_pref']))
print("APPLICABLE=%d maxLng=%d  (v0<=x in %d)" % (R['applic'], maxLapp, R['vlex']))
if R['applic']:
    print(" slotAppg (appg)        : %d/%d" % (R['appg'], R['applic']))
    print(" qlt   (v0<=x -> q<whole): %d/%d" % (R['qlt'], R['applic']))
    print(" Gq    (v0<=x -> Gq<whole): %d/%d" % (R['Gq'], R['applic']))
    print(" ALL (appg&qlt&Gq)      : %d/%d" % (R['allok'], R['applic']))
    print(" DEEP Lng>=16: %d/%d  Lng>=20: %d/%d" %
          (R['d16ok'], R['d16'], R['d20ok'], R['d20']))
if fails:
    fails.sort(key=lambda t: t[0])
    print("== FAILURES: %d (minimal first)" % len(fails))
    for it in fails[:8]:
        L,M,v0,x,qq,ps,appg,qlt,Gq = it
        print("  Lng=%d appg=%s qlt=%s Gq=%s v0=%s x=%s" % (L,appg,qlt,Gq,v0,x))
        print("    M=%s" % (M,))
        print("    ps=%s q=%s" % (ps, qq))
else:
    print("NO FAILURES.")
