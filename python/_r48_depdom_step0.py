#!/usr/bin/env python3
"""r48 STEP-0 (depdom agent): identify the v0-rooted witness slice.

For hosts M in the deep-insertion frame (mono, Br!=[], Lng-1>1,
Trans M = D_v0(Trm ps +B D_x qq), Trans(Pred M) = D_v0(Trm ps +B r),
v0<=x, qq!=0), find WHICH terminal slice seg(M,j,Lng-1) (if any) has
Trans = D_v0(D_x qq)  (the tgt).  Record j vs Joints(M)/FirstNodes(M),
entry(M,1,j), and whether the slice is in the BFS-reachable (standard)
corpus.  Also tally the ps==[] subcase (there tgt == Trans M itself).
"""
import sys, time, signal
from collections import deque
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
from red_model import Lng, oper, diagSeq, monoT, Br, entry, seg, Joints, FirstNodes, TrMax
import trans_model as tm

sys.setrecursionlimit(200000)

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

T_BFS   = float(sys.argv[1]) if len(sys.argv) > 1 else 60.0
T_CHECK = float(sys.argv[2]) if len(sys.argv) > 2 else 200.0
PER     = int(sys.argv[3]) if len(sys.argv) > 3 else 8

seeds = [diagSeq(u, u + d) for u in range(0, 6) for d in range(1, 7)]
seen = set(); q = deque(seeds)
t0 = time.time()
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
    q = deque(list(seen))
print("BFS visited=%d maxLng=%d (%.0fs)" %
      (len(seen), max(len(m) for m in seen), time.time() - t0), flush=True)

stats = dict(applic=0, psnil=0, psnil_selfeq=0, psne=0, skip=0,
             hit_any=0, hit_joint_last=0, hit_joint0=0, hit_std=0,
             hit_entry_v0=0, nohit=0)
nohit_ex = []; hit_notstd_ex = []; jpos_hist = {}
maxLapp = 0

def check_host(Mt):
    global maxLapp
    M = list(Mt)
    v0 = entry(M, 1, 0)
    signal.alarm(PER)
    try:
        TM = Trans(M); TPM = Trans(tm.Pred(M)); signal.alarm(0)
    except (TO, Exception):
        signal.alarm(0); return
    if len(TM[1]) != 1 or TM[1][0][1] != v0 or not TM[1][0][2][1] \
       or len(TPM[1]) != 1 or TPM[1][0][1] != v0:
        return
    lM = bucOf(TM[1][0][2]); lPM = bucOf(TPM[1][0][2])
    ps = lM[:-1]; x, qq = lM[-1][1], lM[-1][2]
    if lPM[:len(ps)] != ps: return
    if not (v0 <= x): return
    if not qq: return
    stats['applic'] += 1
    L = Lng(M); maxLapp = max(maxLapp, L)
    tgt = [('D', v0, [('D', x, qq)])]
    if not ps:
        stats['psnil'] += 1
        if bucOf(TM) == tgt: stats['psnil_selfeq'] += 1
        return
    stats['psne'] += 1
    # scan terminal slices
    hits = []
    for j in range(1, L):
        N = seg(M, j, L - 1)
        signal.alarm(PER)
        try:
            TN = bucOf(Trans(N)); signal.alarm(0)
        except (TO, Exception):
            signal.alarm(0); continue
        if TN == tgt:
            hits.append(j)
    try:
        js = Joints(M); fn = FirstNodes(M)
    except Exception:
        js = []; fn = []
    if hits:
        stats['hit_any'] += 1
        jh = hits[0]
        if js and jh == js[-1]: stats['hit_joint_last'] += 1
        if js and jh == js[0]: stats['hit_joint0'] += 1
        if entry(M, 1, jh) == v0: stats['hit_entry_v0'] += 1
        std = any(tuple(seg(M, j, L - 1)) in seen for j in hits)
        if std: stats['hit_std'] += 1
        elif len(hit_notstd_ex) < 5:
            hit_notstd_ex.append((M, hits, js, fn))
        # position class of first hit
        cls = ('joint%d' % js.index(jh)) if jh in js else \
              ('first%d' % fn.index(jh)) if jh in fn else 'other'
        jpos_hist[cls] = jpos_hist.get(cls, 0) + 1
    else:
        stats['nohit'] += 1
        if len(nohit_ex) < 5:
            nohit_ex.append((M, v0, x, qq, js, fn))

t1 = time.time()
hosts = sorted(seen, key=len)
for Mt in hosts:
    if time.time() - t1 > T_CHECK: break
    if len(Mt) < 4: continue
    M = list(Mt)
    try:
        if not (monoT(M) and Br(M) and Lng(M) - 1 > 1): continue
    except Exception:
        continue
    check_host(Mt)

print("checked in %.0fs  maxLngApplic=%d" % (time.time() - t1, maxLapp))
print("stats:", stats)
print("jpos_hist:", jpos_hist)
for (M, v0, x, qq, js, fn) in nohit_ex:
    print("NOHIT M=%s v0=%d x=%d qq=%s Joints=%s FirstNodes=%s" % (M, v0, x, qq, js, fn))
for (M, hits, js, fn) in hit_notstd_ex:
    print("HIT-NOTSTD M=%s hits=%s Joints=%s FirstNodes=%s" % (M, hits, js, fn))
