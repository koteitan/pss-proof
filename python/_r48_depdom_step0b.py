#!/usr/bin/env python3
"""r48 STEP-0b (depdom agent, FINAL run): global witness existence + invariant shape.

For applicable hosts (deep-insertion frame, v0<=x, qq!=0):
 (1) existence of shorter standard N (corpus index) with Trans N == D_v0(D_x qq)  [tgt]
 (2) existence of shorter standard N with Trans N == D_x qq                      [deposit]
 (3) escape-structure profile: for y in {qq} u G_v0(qq):
       classify hd(y): empty / idx<x / idx==x / idx>x ; if idx==x, is body(y) < qq?
 (4) v0-minimality of all indices in Trans M
 (5) psnil keystone shape: is r (pred body) a single principal with head x?
"""
import sys, time, signal
from collections import deque
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
from red_model import Lng, oper, diagSeq, monoT, Br, entry
import trans_model as tm
import buchholz as bu

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
def key(l):  # hashable form of buchholz list-term
    return tuple(('D', v, key(b)) for (_, v, b) in l)

class TO(Exception): pass
signal.signal(signal.SIGALRM, lambda s, f: (_ for _ in ()).throw(TO()))

T_BFS   = float(sys.argv[1]) if len(sys.argv) > 1 else 60.0
T_CHECK = float(sys.argv[2]) if len(sys.argv) > 2 else 210.0
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

# --- Trans-value index over the corpus (minimum length per value) ---
tindex = {}
t1 = time.time()
for Mt in sorted(seen, key=len):
    if time.time() - t1 > 60: break
    M = list(Mt)
    signal.alarm(PER)
    try:
        v = key(bucOf(Trans(M))); signal.alarm(0)
    except (TO, Exception):
        signal.alarm(0); continue
    if v not in tindex or len(Mt) < tindex[v][0]:
        tindex[v] = (len(Mt), Mt)
print("tindex size=%d (%.0fs)" % (len(tindex), time.time() - t1), flush=True)

def allidx_ge(l, v0):
    return all(v >= v0 and allidx_ge(b, v0) for (_, v, b) in l)

stats = dict(applic=0, psnil=0, psne=0,
             tgt_wit_nil=0, tgt_wit_ne=0, dep_wit_nil=0, dep_wit_ne=0,
             v0min=0, esc_ok_lt=0, esc_eq_bodylt=0, esc_bad=0,
             nil_predsingle=0, nil_predsingle_samehead=0,
             xeqv0=0, xgtv0=0)
tgt_wit_ex = []; esc_prof = {}
t2 = time.time()
for Mt in sorted(seen, key=len):
    if time.time() - t2 > T_CHECK: break
    if len(Mt) < 4: continue
    M = list(Mt)
    try:
        if not (monoT(M) and Br(M) and Lng(M) - 1 > 1): continue
    except Exception:
        continue
    v0 = entry(M, 1, 0)
    signal.alarm(PER)
    try:
        TM = Trans(M); TPM = Trans(tm.Pred(M)); signal.alarm(0)
    except (TO, Exception):
        signal.alarm(0); continue
    if len(TM[1]) != 1 or TM[1][0][1] != v0 or not TM[1][0][2][1] \
       or len(TPM[1]) != 1 or TPM[1][0][1] != v0:
        continue
    lM = bucOf(TM[1][0][2]); lPM = bucOf(TPM[1][0][2])
    ps = lM[:-1]; x, qq = lM[-1][1], lM[-1][2]
    if lPM[:len(ps)] != ps: continue
    if not (v0 <= x): continue
    if not qq: continue
    stats['applic'] += 1
    if x == v0: stats['xeqv0'] += 1
    else: stats['xgtv0'] += 1
    L = len(M)
    tgt = [('D', v0, [('D', x, qq)])]; dep = [('D', x, qq)]
    ktgt = key(tgt); kdep = key(dep)
    wt = tindex.get(ktgt); wd = tindex.get(kdep)
    has_wt = wt is not None and wt[0] < L
    has_wd = wd is not None and wd[0] < L
    if not ps:
        stats['psnil'] += 1
        if has_wt: stats['tgt_wit_nil'] += 1
        if has_wd: stats['dep_wit_nil'] += 1
        # keystone shape: pred body single principal, same head?
        if len(lPM) == 1:
            stats['nil_predsingle'] += 1
            if lPM[0][1] == x: stats['nil_predsingle_samehead'] += 1
    else:
        stats['psne'] += 1
        if has_wt:
            stats['tgt_wit_ne'] += 1
            if len(tgt_wit_ex) < 6: tgt_wit_ex.append((M, wt[1], v0, x))
        if has_wd: stats['dep_wit_ne'] += 1
    if allidx_ge(lM, v0): stats['v0min'] += 1
    # escape profile
    esc = [qq] + bu.G(v0, qq)
    prof = set(); bad = False
    for y in esc:
        if not y: prof.add('nil'); continue
        hi = y[0][1]
        if hi < x: prof.add('lt')
        elif hi == x:
            if bu.lt_term(y[0][2], qq): prof.add('eq_bodylt')
            else: prof.add('eq_bodyGE'); bad = True
        else: prof.add('GT'); bad = True
    pk = tuple(sorted(prof))
    esc_prof[pk] = esc_prof.get(pk, 0) + 1
    if bad: stats['esc_bad'] += 1

print("checked in %.0fs" % (time.time() - t2))
print("stats:", stats)
print("esc_prof:", esc_prof)
for (M, W, v0, x) in tgt_wit_ex:
    print("PSNE-TGT-WIT M=%s  v0=%d x=%d  witness=%s" % (M, v0, x, list(W)))
