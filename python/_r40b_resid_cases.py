#!/usr/bin/env python3
"""r40b: keystone-case classification + sub-residual empirics for `resid`.

For each applicable keystone host (Trans M = D_v0(Trm(ps@[DB x q])),
Trans(Pred M) = D_v0(Trm(ps@rs))):
 - class WB (wholebody, rs=[]) vs PP (proper-prefix, rs=[DB x qp]) vs OTHER
 - Admpos: transJm1 M > 0
 - headle: ps!=[] -> x <= head(last ps)
 - eqhead + tailEH: x = head(last ps) -> leBT q qb
 - appg parts (v0<=x): qlt: q < body; Gq: all G_{v0}(q) < body
 - PP: rs single + head==x (keystone shape); q vs qp descent direction
"""
import sys, time, signal, random
from collections import deque
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import Lng, oper, diagSeq, monoT, Br, entry, parent
import trans_model as tm
import buchholz as bu

sys.setrecursionlimit(200000)
random.seed(41)

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

T_BFS = float(sys.argv[1]) if len(sys.argv) > 1 else 120.0
T_CHK = float(sys.argv[2]) if len(sys.argv) > 2 else 600.0
SEEDSHIFT = int(sys.argv[3]) if len(sys.argv) > 3 else 0

seeds = [diagSeq(u, u + d) for u in range(0, 9) for d in range(1, 10)]
seen = set(); q = deque(seeds)
t0 = time.time()
while q and time.time() - t0 < T_BFS and len(seen) < 300000:
    M = q.popleft(); k = tuple(M)
    if k in seen: continue
    seen.add(k)
    if Lng(M) <= 40:
        ns = [1, 2, 3, 4, 5, 6, 7]
        for nn in ns:
            try: M2 = oper(M, nn)
            except Exception: continue
            if M2 != M and len(M2) <= 48 and tuple(M2) not in seen:
                q.append(M2)
print("BFS: visited=%d maxLng=%d (%.0fs)" %
      (len(seen), max(len(m) for m in seen), time.time() - t0), flush=True)

vis = list(seen); random.shuffle(vis)
vis.sort(key=lambda m: -len(m))
# interleave: deep chains first but keep variety
chains = vis[SEEDSHIFT::2] + vis[1 - SEEDSHIFT::2]

S = dict(applic=0, WB=0, PP=0, OTHER=0,
         WB_adm=0, WB_noadm=0, PP_adm=0, PP_noadm=0,
         WB_eqh=0, WB_neqh=0, headle_f=0, tail_f=0, qlt_f=0, Gq_f=0,
         WBnoadm_headle_f=0, PP_qgeqp=0, PP_qltqp=0, skip=0,
         d12=0, d16=0)
OTHERex = []; FAILS = []
checked = set()
tC = time.time()
for E in chains:
    if time.time() - tC > T_CHK: break
    for kk in range(3, len(E) + 1):
        M = list(E[:kk]); km = tuple(M)
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
        if lPM[:len(ps)] != ps: continue
        rs = lPM[len(ps):]
        S['applic'] += 1
        L = len(M)
        if L >= 12: S['d12'] += 1
        if L >= 16: S['d16'] += 1
        signal.alarm(10)
        try:
            j1 = L - 1
            jp = parent(M, 0, j1)
            admv = tm.Adm(M, jp) if jp is not None else -1
            admpos = admv > 0
            wb = (rs == [])
            if wb:
                S['WB'] += 1
                S['WB_adm' if admpos else 'WB_noadm'] += 1
            elif len(rs) == 1 and rs[0][1] == x:
                S['PP'] += 1
                S['PP_adm' if admpos else 'PP_noadm'] += 1
                qp = rs[0][2]
                if bu.le_term(qp, qq): S['PP_qgeqp'] += 1
                else: S['PP_qltqp'] += 1
            else:
                S['OTHER'] += 1
                if len(OTHERex) < 8: OTHERex.append((L, M, rs[:2], x))
            if ps:
                hd, qb = ps[-1][1], ps[-1][2]
                if not (x < hd or (x == hd)):
                    S['headle_f'] += 1; FAILS.append(('headle', L, M))
                if wb:
                    if x == hd: S['WB_eqh'] += 1
                    else: S['WB_neqh'] += 1
                    if not admpos and not x <= hd:
                        S['WBnoadm_headle_f'] += 1
                if x == hd and not bu.le_term(qq, qb):
                    S['tail_f'] += 1; FAILS.append(('tailEH', L, M))
            if v0 <= x:
                body = lM
                if not bu.lt_term(qq, body):
                    S['qlt_f'] += 1; FAILS.append(('qlt', L, M))
                if not all(bu.lt_term(y, body) for y in bu.G(v0, qq)):
                    S['Gq_f'] += 1; FAILS.append(('Gq', L, M))
            signal.alarm(0)
        except (TO, Exception):
            signal.alarm(0); S['skip'] += 1
print("hosts(applic)=%d  d12=%d d16=%d  skip=%d  (%.0fs)"
      % (S['applic'], S['d12'], S['d16'], S['skip'], time.time() - tC))
print("classes: WB=%d (adm+%d/adm0 %d; eqh=%d neqh=%d)  PP=%d (adm+%d/adm0 %d)"
      % (S['WB'], S['WB_adm'], S['WB_noadm'], S['WB_eqh'], S['WB_neqh'],
         S['PP'], S['PP_adm'], S['PP_noadm']))
print("OTHER (keystone-shape violations!)=%d" % S['OTHER'])
for it in OTHERex: print("   OTHER Lng=%d M=%s rs[:2]=%s x=%s" % it)
print("PP tail direction: q>=qp %d / q<qp %d" % (S['PP_qgeqp'], S['PP_qltqp']))
print("sub-residual failures: headle=%d tailEH=%d qlt=%d Gq=%d WBnoadm_headle=%d"
      % (S['headle_f'], S['tail_f'], S['qlt_f'], S['Gq_f'], S['WBnoadm_headle_f']))
for it in FAILS[:10]: print("   FAIL", it[0], "Lng=%d" % it[1], "M=%s" % it[2])
