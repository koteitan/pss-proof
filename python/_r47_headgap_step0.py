#!/usr/bin/env python3
"""r47 STEP-0 (head-gap agent): can slotAppg's qcore/Gcore be derived from the
OT-membership of the deposit (isOT_BT (Dpt x q), via slice + a5)?

Frame (deep-insertion keystone, r44):
  Trans M       = D_v0(Trm (ps @ [DB x q]))   v0 = entry M 1 0
  Trans(Pred M) = D_v0(Trm (ps @ rs))
Needed (sax_slotAppg_modcore residuals, regime q<>0, v0<=x):
  qcore: lt(q, ps@[D x q])
  Gcore: all y in G(v0,q): lt(y, ps@[D x q])

Candidate bridge facts checked per applicable host:
  depOT   : in_OT([D(x,q)])                       (from slice+a5 -- MUST hold)
  headgap : q==[] or idx(hd q) <= x               (enables q < D_x q)
  qltdep  : lt(q, [D(x,q)])
  selfdom : all y in G(v0,q): lt(y,q)             (= G-half of isOT_BP(DB v0 q))
  depdom  : all y in G(v0,q): lt(y,[D(x,q)])
  deple   : ps==[] or le([D(x,q)], [last ps])     (C2-combined position bound)
  hhg     : hereditary head-gap inside q (every D_w b in q: b==[] or idx(hd b)<=w)
  gext    : G(v0,q) has elements outside G(x,q)   (the abstract-gap regime)
Chain candidates:
  chainA  : headgap & selfdom & (deple)           => qcore & Gcore derivable
"""
import sys, time, signal, random
from collections import deque
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
from red_model import Lng, oper, diagSeq, monoT, Br, entry
import trans_model as tm
import buchholz as bu

sys.setrecursionlimit(200000)
random.seed(47)

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

def hhg_ok(q):     # hereditary head-gap inside term q
    for (_, w, b) in q:
        if b and b[0][1] > w: return False
        if not hhg_ok(b): return False
    return True

def keyrepr(t): return repr(t)

class TO(Exception): pass
signal.signal(signal.SIGALRM, lambda s, f: (_ for _ in ()).throw(TO()))

T_BFS   = float(sys.argv[1]) if len(sys.argv) > 1 else 40.0
T_CHECK = float(sys.argv[2]) if len(sys.argv) > 2 else 180.0
LNG_CAP = int(sys.argv[3]) if len(sys.argv) > 3 else 44
PER     = int(sys.argv[4]) if len(sys.argv) > 4 else 8

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

KEYS = ['depOT','headgap','qltdep','selfdom','depdom','deple','hhg',
        'qcore','Gcore','chainA']
R = dict((k,0) for k in KEYS)
R.update(applic=0, vlex=0, novle=0, qzero=0, skip=0,
         inap_shape=0, inap_pref=0, psne=0, psnil=0, gext=0, strictv=0,
         d16=0, d16ok=0)
fails = {k: [] for k in KEYS}
checked = set(); maxLapp = 0
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
    ps = lM[:-1]; x, qq = lM[-1][1], lM[-1][2]
    if lPM[:len(ps)] != ps:
        R['inap_pref'] += 1; return True
    L = len(M)
    if not (v0 <= x):
        R['novle'] += 1; return True           # vacuous branch (closed already)
    if not qq:
        R['qzero'] += 1; return True           # trivial branch (closed already)
    signal.alarm(PER)
    try:
        dep   = [('D', x, qq)]
        whole = ps + dep
        gv0   = bu.G(v0, qq)
        gx    = bu.G(x, qq)
        res = {}
        res['depOT']   = bu.in_OT(dep)
        res['headgap'] = qq[0][1] <= x
        res['qltdep']  = bu.lt_term(qq, dep)
        res['selfdom'] = all(bu.lt_term(y, qq) for y in gv0)
        res['depdom']  = all(bu.lt_term(y, dep) for y in gv0)
        res['deple']   = (not ps) or bu.le_term(dep, [ps[-1]])
        res['hhg']     = hhg_ok(qq)
        res['qcore']   = bu.lt_term(qq, whole)
        res['Gcore']   = all(bu.lt_term(y, whole) for y in gv0)
        res['chainA']  = (res['headgap'] and res['selfdom'] and res['deple'])
        gxr = set(map(keyrepr, gx))
        gext = any(keyrepr(y) not in gxr for y in gv0)
        signal.alarm(0)
    except (TO, Exception):
        signal.alarm(0); R['skip'] += 1; return False
    R['applic'] += 1; R['vlex'] += 1; maxLapp = max(maxLapp, L)
    if ps: R['psne'] += 1
    else:  R['psnil'] += 1
    if gext: R['gext'] += 1
    if v0 < x: R['strictv'] += 1
    for k in KEYS:
        if res[k]: R[k] += 1
        elif len(fails[k]) < 6:
            fails[k].append((L, list(M), v0, x, len(ps), bool(ps),
                             gext, dict(res)))
    ok = res['qcore'] and res['Gcore']
    if L >= 16:
        R['d16'] += 1
        if ok: R['d16ok'] += 1
    return True

for E in chains:
    if time.time() - tC > T_CHECK: break
    for kk in range(3, len(E)+1):
        if time.time() - tC > T_CHECK + 20: break
        M = list(E[:kk]); km = tuple(M)
        if km in checked: continue
        checked.add(km)
        if not (monoT(M) and Br(M) != []): continue
        if len(M) - 1 <= 1: continue
        if not check_host(M): break

print("hosts checked(uniq)=%d in %.0fs skips=%d" %
      (len(checked), time.time()-tC, R['skip']))
print("inapplicable shape=%d prefix-mismatch=%d novle(v0>x)=%d qzero=%d"
      % (R['inap_shape'], R['inap_pref'], R['novle'], R['qzero']))
print("APPLICABLE(core regime v0<=x, q<>0)=%d maxLng=%d ps!=[]:%d ps==[]:%d "
      "strict v0<x:%d gext:%d" %
      (R['applic'], maxLapp, R['psne'], R['psnil'], R['strictv'], R['gext']))
if R['applic']:
    for k in KEYS:
        print("  %-8s: %d/%d" % (k, R[k], R['applic']))
    print("  DEEP Lng>=16 (qcore&Gcore): %d/%d" % (R['d16ok'], R['d16']))
for k in KEYS:
    if fails[k]:
        print("== %s FAILS (%d recorded):" % (k, len(fails[k])))
        for (L, M, v0, x, lps, psne, gext, res) in fails[k][:3]:
            print("  Lng=%d v0=%s x=%s |ps|=%d gext=%s M=%s" %
                  (L, v0, x, lps, gext, M))
            print("    res=%s" % ({kk: vv for kk, vv in res.items()},))
