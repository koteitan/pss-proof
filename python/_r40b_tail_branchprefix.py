#!/usr/bin/env python3
"""r40b: is the slotTail (equal-head tail leBT q qb) reduction via BRANCH
prefix-nesting (m_8_7_eqhead_tail_from_branch_prefix) viable on deep ST_PS?

For equal-head keystone hosts (x == head(last ps)):
 - read the last two branches A = Br M!J1, Bp = Br M!(J1-1) (when >= 2 branches)
 - check the read-offs  Trm [last ps] = Trans Bp  and  Dpt x q = Trans A
   (the r39 order-core assumption), and the prefix nesting  Bp = A @ C.
This is the branch analog of the REFUTED pcompPrefix — verdict needed before
any round invests in that route for slotTail.
"""
import sys, time, signal, random
from collections import deque
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import Lng, oper, diagSeq, monoT, Br, entry, TrMax, seg, IdxSum
import red_model as rm
import trans_model as tm
import buchholz as bu

sys.setrecursionlimit(200000)
random.seed(99)

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

T_TOTAL = float(sys.argv[1]) if len(sys.argv) > 1 else 900.0

def is_prefix(a, b): return len(a) <= len(b) and b[:len(a)] == a

S = dict(eq=0, ge2=0, pref=0, npref=0, roA=0, roB=0, nro=0, d12eq=0, skip=0,
         via_ok=0, via_bad=0)
NP = []; NRO = []
checked = set()
t0 = time.time()
seeds = [diagSeq(u, u + d) for u in range(0, 9) for d in range(1, 10)]
while time.time() - t0 < T_TOTAL:
    M0 = list(random.choice(seeds))
    for step in range(300):
        if time.time() - t0 > T_TOTAL: break
        nn = random.choice([1, 1, 2, 2, 3, 3, 4, 5, 6])
        try: M1 = oper(M0, nn)
        except Exception: break
        if len(M1) > 40 or M1 == M0: break
        M0 = M1
        for kk in range(3, len(M0) + 1):
            M = M0[:kk]; km = tuple(M)
            if km in checked: continue
            checked.add(km)
            if not (len(M) - 1 > 1 and monoT(M) and Br(M) != []): continue
            v0 = entry(M, 1, 0)
            signal.alarm(10)
            try:
                TM = Trans(M); TPM = Trans(tm.Pred(M))
                signal.alarm(0)
            except (TO, Exception):
                signal.alarm(0); S['skip'] += 1; break
            if len(TM[1]) != 1 or TM[1][0][1] != v0 or not TM[1][0][2][1] \
               or len(TPM[1]) != 1 or TPM[1][0][1] != v0:
                continue
            lM = bucOf(TM[1][0][2]); lPM = bucOf(TPM[1][0][2])
            ps = lM[:-1]; x, qq = lM[-1][1], lM[-1][2]
            if lPM[:len(ps)] != ps or not ps: continue
            hd, qb = ps[-1][1], ps[-1][2]
            if x != hd: continue
            S['eq'] += 1
            if len(M) >= 12: S['d12eq'] += 1
            br = Br(M)
            if len(br) < 2: continue
            S['ge2'] += 1
            A = br[-1]; Bp = br[-2]
            signal.alarm(10)
            try:
                TA = Trans(A); TB = Trans(Bp)
                signal.alarm(0)
            except (TO, Exception):
                signal.alarm(0); S['skip'] += 1; continue
            # read-offs: Dpt x q == Trans A ? Trm [last ps] == Trans Bp ?
            roA = (len(TA[1]) == 1 and TA[1][0][1] == x and bucOf(TA[1][0][2]) == qq)
            roB = (len(TB[1]) == 1 and TB[1][0][1] == hd and bucOf(TB[1][0][2]) == qb)
            if roA: S['roA'] += 1
            if roB: S['roB'] += 1
            if not (roA and roB):
                S['nro'] += 1
                if len(NRO) < 6: NRO.append((len(M), M, roA, roB))
            p = is_prefix(A, Bp)
            if p: S['pref'] += 1
            else:
                S['npref'] += 1
                if len(NP) < 10: NP.append((len(M), M, A, Bp))
            # the full route viability: read-offs AND prefix
            if roA and roB and p: S['via_ok'] += 1
            else: S['via_bad'] += 1

print("hosts-uniq=%d  equal-head=%d (deep>=12: %d)  with>=2branches=%d  skip=%d (%.0fs)"
      % (len(checked), S['eq'], S['d12eq'], S['ge2'], S['skip'], time.time() - t0))
print("read-offs: Trans A matches D_x q: %d/%d   Trans Bp matches last ps: %d/%d  both-fail-or-one=%d"
      % (S['roA'], S['ge2'], S['roB'], S['ge2'], S['nro']))
print("branch prefix nesting A<=Bp: %d ok / %d FAIL" % (S['pref'], S['npref']))
print("FULL route (readoffs+prefix): %d ok / %d fail" % (S['via_ok'], S['via_bad']))
for it in NP[:8]:
    print("  NOPREFIX Lng=%d M=%s A=%s Bp=%s" % it)
for it in NRO[:6]:
    print("  NOREADOFF Lng=%d M=%s roA=%s roB=%s" % it)
