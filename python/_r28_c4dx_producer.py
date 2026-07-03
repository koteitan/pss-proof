#!/usr/bin/env python3
r"""r28-CONDIV13: validate the condition-agnostic producer data + witness matching
for the condIV exchange (1)/(3) (c4cx_condIV_exchange_full), with the concrete
witnesses the assembled lemma will use:

  body := bpHeadT (transC2 M),  s1/b1 := s84x_s1/b1 M,  (s0,b0) := the unique
  scb pair of body at the D_v1 0 hole (from c4cx2_condIV_mnform_of_slice).

Facts checked on GENUINE condIV hosts (mono, reduced, hasParent(1,j1), j1>1),
gated by admeq / reg as the lemma will be:

  UV     : entry M 1 (s84x_jm3 M) < v1                       (condition-agnostic claim)
  T2NE   : transT2 M != 0                                    (condIV claim)
  JM2UB  : entry M 1 (s84x_jm2 M) == v1 - 1  (= ub)          (RedCondA; proven, sanity)
  SHAPE  : bpHeadT(transC2 M) = t3 + D_jp(t4 + D_v1 0), with
           (leftDj0 -> t2 = t3 + D_jp t4) and (!leftDj0 -> t3 = t4 = t2)
  DBBODY : domB (bpHeadT (transC2 M)) = TBv (v1 - 1)
  BASE0  : lessBT (D_ub 0) (transT2 M)
  F1HEAD : first top-level head of t2 >= v1 (diagnostic for BASE0's proof)
  STRUCT : flat(t3 + D_jp(t4 + D_ub(D_ub 0))) == s0 @ [D ub] @ flat(D_ub 0) @ b0
           (the term-level identity of d4vx_ins s0 ub b0 (D_ub 0))
  BASE1  : lessBT (transT2 M) (t3 + D_jp(t4 + D_ub(D_ub 0)))
  K1SAN  : flat(Mark M jm3) == flat(transC2 M) under admeq   (witness-matching route)
  E13    : full (1)/(3s) conclusions at n=1..3 via the d4vx towers (end-to-end)

Hosts: r19/r27 proven generators (oper orbit, ⊆ ST_PS) + brute-force straddle
(reduced+mono, NOT oper-generated) with DEEP Lng>=9 tracked separately.
"""
import sys, os, time, signal, itertools, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm, trans_model as tm
from red_model import (Lng, entry, monoT, zeroT, diagSeq, parent, oper,
                       hasParent, seg, fmt)
from trans_model import (adm, Adm, ZB, Dpt, addBT, flatBT, flatBP, bpHeadV,
                         bpHeadT, PB, SigmaB, _c2, Pred, scb_decomps, unflatBT)

_TC, _MC, _RC, _rc = {}, {}, {}, {}
_T0, _M0, _R0, _r0 = tm.Trans, tm.Mark, rm.Red, tm.reduced
def Trans(M, d=0):
    k = tuple(M)
    if k not in _TC: _TC[k] = _T0(M, d)
    return _TC[k]
def Mark(M, m, d=0):
    k = (tuple(M), m)
    if k not in _MC: _MC[k] = _M0(M, m, d)
    return _MC[k]
def Red(M, d=0):
    k = tuple(M)
    if k not in _RC: _RC[k] = _R0(M, d)
    return _RC[k]
def reduced(M):
    k = tuple(M)
    if k not in _rc: _rc[k] = _r0(M)
    return _rc[k]
tm.Trans, tm.Mark, rm.Red, tm.reduced = Trans, Mark, Red, reduced

def pr(*a): print(*a, flush=True)
class TO(Exception): pass
signal.signal(signal.SIGALRM, lambda s, f: (_ for _ in ()).throw(TO()))

# ---------- Buchholz order and dom (faithful to pss_paper.thy) ----------
def lessBT(a, b):
    pa, pb = a[1], b[1]
    for x, y in zip(pa, pb):
        if x == y: continue
        return lessBP(x, y)
    return len(pa) < len(pb)
def lessBP(x, y):
    return x[1] < y[1] or (x[1] == y[1] and lessBT(x[2], y[2]))

def domB(a):
    ps = a[1]
    if not ps: return ('EMPTY',)
    if len(ps) > 1: return domB(('T', [ps[-1]]))
    (_, v, b) = ps[0]
    if b == ZB:
        return ('ZERO',) if v == 0 else ('TBV', v - 1)
    db = domB(b)
    if db == ('ZERO',): return ('NAT',)
    if db[0] == 'TBV' and v <= db[1]: return ('NAT',)
    return db

# ---------- host data ----------
def condIV(M):
    j1 = Lng(M) - 1; jp = parent(M, 0, j1)
    if jp is None: return False
    return entry(M, 1, j1) > 0 and entry(M, 1, jp) >= entry(M, 1, j1) and not adm(M, jp)

def transJ0(M): return parent(M, 0, Lng(M) - 1)
def transJm1(M): return Adm(M, transJ0(M))
def transT2(M): return bpHeadT(Mark(Pred(M), transJm1(M)))
def s84x_jm2(M): return parent(M, 1, Lng(M) - 1)
def s84x_jm3(M): return Adm(M, s84x_jm2(M))

def cat(chunks): return list(itertools.chain.from_iterable(chunks))

class St:
    def __init__(s): s.ok = 0; s.bad = 0; s.cex = []
    def rec(s, g, i):
        if g: s.ok += 1
        else:
            s.bad += 1
            if len(s.cex) < 5: s.cex.append(i)
    def __str__(s): return f"{s.ok}/{s.ok + s.bad}"

KEYS = ('UV','T2NE','JM2UB','SHAPE','DBBODY','BASE0','F1HEAD','STRUCT','BASE1',
        'K1SAN','E13')

def check_host(M, R, deeptag):
    j1 = Lng(M) - 1
    v1 = entry(M, 1, j1); ub = v1 - 1
    jp = transJ0(M); jpe = entry(M, 1, jp)
    jm2 = s84x_jm2(M); jm3 = s84x_jm3(M)
    if jm3 is None or jm2 is None: return
    e3 = entry(M, 1, jm3)
    jm1 = transJm1(M)
    admeq = (jm3 == jm1)
    reg = (jm2 < jp) or adm(M, jp)
    t2 = transT2(M)
    TM = Trans(M)
    c2 = _c2(M, j1, jp, bpHeadV(Mark(Pred(M), jm1)), t2)
    c2body = bpHeadT(c2)
    R['hosts'] += 1
    if admeq: R['admeq'] += 1
    if reg: R['reg'] += 1
    gate = admeq and reg
    if gate: R['gated'] += 1
    def rec(key, ok):
        R[key].rec(ok, (fmt(M),))
        if deeptag: R[key + '_deep'].rec(ok, (fmt(M),))
    # UV (claim: condition-agnostic, no gate needed)
    rec('UV', e3 < v1)
    # T2NE (condIV claim, no gate needed)
    rec('T2NE', t2 != ZB)
    # JM2UB (RedCondA; proven)
    rec('JM2UB', entry(M, 1, jm2) == ub)
    # SHAPE + t3/t4 relation
    if t2 == ZB:
        t3, t4, leftD = ZB, ZB, None
    else:
        Pt2 = PB(t2); J1b = len(Pt2) - 1; pj = Pt2[J1b]
        leftD = (bpHeadV(pj) == jpe)
        t3 = SigmaB(Pt2[:J1b]) if leftD else t2
        t4 = bpHeadT(pj) if leftD else t2
    shape_ok = (c2body == addBT(t3, Dpt(jpe, addBT(t4, Dpt(v1, ZB)))))
    if t2 != ZB:
        rel_ok = (t2 == addBT(t3, Dpt(jpe, t4))) if leftD else (t3 == t2 and t4 == t2)
        shape_ok = shape_ok and rel_ok
    rec('SHAPE', shape_ok)
    # DBBODY
    rec('DBBODY', domB(c2body) == ('TBV', ub))
    # BASE0 + first-head diagnostic
    rec('BASE0', lessBT(Dpt(ub, ZB), t2))
    if t2 != ZB:
        fh = t2[1][0][1]
        rec('F1HEAD', fh >= v1)
        R['fhead_min'] = min(R.get('fhead_min', 10**9), fh - v1)
    # STRUCT + BASE1 (need the unique (s0,b0) of c2body at the hole)
    hole = flatBP(('D', v1, ZB))
    ds = scb_decomps(c2body, hole)
    if len(ds) >= 1:
        R['s0b0'] += 1
        s0, b0 = ds[0]
        struct = addBT(t3, Dpt(jpe, addBT(t4, Dpt(ub, Dpt(ub, ZB)))))
        rec('STRUCT', flatBT(struct) == s0 + [('D', ub)] + flatBT(Dpt(ub, ZB)) + b0)
        rec('BASE1', lessBT(t2, struct))
        if len(ds) > 1: R['multi_sb'] += 1
    # K1SAN (under admeq)
    if admeq:
        rec('K1SAN', flatBT(Mark(M, jm3)) == flatBT(c2))
    # E13: end-to-end (1)/(3s) at n=1..3 through the towers, in the s1/b1 wrapper.
    # A_k = d4vx_core(t2, k), X_k = d4vx_core(D_ub 0, k); (1): A_{n-1} < X_n,
    # (3s): X_{n-1} < A_{n-1}.  Tower via term-level struct insert.
    if len(ds) >= 1 and gate:
        s0, b0 = ds[0]
        def ins(X):
            return unflatBT(s0 + [('D', ub)] + flatBT(X) + b0)
        try:
            A = [t2]; X = [Dpt(ub, ZB)]
            for k in range(4):
                A.append(ins(A[-1])); X.append(ins(X[-1]))
            ok = True
            for n in (1, 2, 3):
                if not lessBT(A[n-1], X[n]): ok = False
                if not lessBT(X[n-1], A[n-1]): ok = False
            rec('E13', ok)
        except (ValueError, IndexError):
            R['e13_err'] += 1

def gen_oper(max_len, cap, seed, ns, umax, vextra):
    rng = random.Random(seed); seen = set(); out = []; work = []
    for u in range(0, umax + 1):
        for v in range(u, u + vextra):
            work.append(diagSeq(u, v))
    while work and len(out) < cap:
        i = rng.randrange(len(work)); M = work.pop(i); k = tuple(M)
        if k in seen: continue
        seen.add(k); out.append(M)
        if Lng(M) > max_len: continue
        for n in ns:
            Mn = oper(M, n)
            if Lng(Mn) <= max_len + 3 and tuple(Mn) not in seen: work.append(Mn)
    return out

def gen_straddle(maxlen, cap, seed):
    rng = random.Random(seed); out = []; seen = set(); stack = [[(0, 0)]]; steps = 0
    while stack and len(out) < cap:
        steps += 1
        if steps > 400000: break
        M = stack.pop(); L = Lng(M)
        if L >= 4 and reduced(M) and monoT(M) and not zeroT(M) \
           and hasParent(M, 1, L - 1) and condIV(M):
            t = tuple(M)
            if t not in seen: seen.add(t); out.append(M)
        if L >= maxlen: continue
        prevmax0 = max((p[0] for p in M), default=0)
        cands = []
        for a in range(0, min(prevmax0 + 2, L + 1) + 1):
            for b in range(0, a + 1):
                Mn = M + [(a, b)]
                if reduced(Mn): cands.append(Mn)
        rng.shuffle(cands)
        for Mn in cands[:6]: stack.append(Mn)
    return out

def run(pool, tag, R, budget):
    t0 = time.time(); nh = 0
    for M in pool:
        if time.time() - t0 > budget: break
        j1 = Lng(M) - 1
        if j1 <= 1 or not monoT(M) or zeroT(M) or not hasParent(M, 1, j1): continue
        if not reduced(M): continue
        if not condIV(M): continue
        nh += 1
        signal.alarm(25)
        try: check_host(M, R, Lng(M) >= 9)
        except (TO, RecursionError, ValueError, IndexError, AssertionError):
            R['to'] += 1
        finally: signal.alarm(0)
    pr(f'[{tag}] pool={len(pool)} condIV={nh} ({time.time() - t0:.0f}s)')

def main():
    t0 = time.time()
    R = {'hosts': 0, 'admeq': 0, 'reg': 0, 'gated': 0, 'to': 0, 's0b0': 0,
         'multi_sb': 0, 'e13_err': 0}
    for k in KEYS:
        R[k] = St(); R[k + '_deep'] = St()
    for seed, mlen, cap, ns, um, vx, bud in (
            (202, 16, 4000, (1, 2), 2, 7, 40),
            (303, 18, 4000, (1, 2), 2, 8, 40),
            (505, 20, 5000, (1, 2), 3, 9, 40),
            (707, 22, 6000, (1, 2), 4, 9, 40),
            (811, 24, 6000, (1, 2, 3), 4, 10, 45),
            (913, 26, 6000, (1, 2), 5, 10, 45)):
        run(gen_oper(mlen, cap, seed, ns, um, vx), f'oper s{seed}', R, bud)
    for seed, mlen, cap, bud in ((41, 9, 600, 60), (43, 10, 500, 70), (47, 11, 400, 80)):
        run(gen_straddle(mlen, cap, seed), f'straddle s{seed}', R, bud)
    pr()
    pr(f'hosts={R["hosts"]} admeq={R["admeq"]} reg={R["reg"]} gated={R["gated"]} '
       f's0b0={R["s0b0"]} multi_sb={R["multi_sb"]} timeouts={R["to"]} '
       f'e13err={R["e13_err"]}')
    if 'fhead_min' in R: pr(f'fhead-v1 min = {R["fhead_min"]}')
    for k in KEYS:
        pr(f'  {k:8s} {str(R[k]):>12s}   deep {str(R[k + "_deep"]):>10s}'
           + ('' if not R[k].cex else f'   CEX {R[k].cex[:3]}'))
    pr(f'total {time.time() - t0:.0f}s')

if __name__ == '__main__':
    main()
