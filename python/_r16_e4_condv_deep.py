#!/usr/bin/env python3
"""r16-E4 deep mine: condV-adm generation-step claims (B1-B4 of _r16_e4_check)
on a WIDER genuine pool, n in 1..4; plus diagnosis of the (C) 'none' residue
for condIII-adm and condVI-adm (which (m,k) family covers them, if any).

Run: python3 _r16_e4_condv_deep.py [tmax] [seed...]
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import (Lng, entry, parent, oper, diagSeq, monoT)
from trans_model import (Trans, Mark, Pred, adm, Adm, condV, condIII, condVI,
                         Dpt, addBT, bpHeadT, flatBT, scb_decomps, ZB)
import buchholz as bu

INF = float('inf')

class TimeoutErr(Exception): pass
def _handler(signum, frame): raise TimeoutErr()
signal.signal(signal.SIGALRM, _handler)

def safe(f, *a, budget=3):
    signal.alarm(budget)
    try:
        r = f(*a); signal.alarm(0); return r
    except (TimeoutErr, RecursionError, AssertionError):
        signal.alarm(0); return None

def numBT(n): return ('T', [('D', 0, ZB)] * n)
def numNat(z): return len(z[1])
def multBT(a, n):
    out = ZB
    for _ in range(n): out = addBT(out, a)
    return out
def domB(a):
    ps = a[1]
    if not ps: return 'EMPTY'
    if len(ps) == 1:
        _, v, b = ps[0]
        if b == ZB:
            if v == 0: return 'ZERO'
            if v == INF: return 'NAT'
            return ('TB', v - 1)
        db = domB(b)
        if db == 'ZERO': return 'NAT'
        if isinstance(db, tuple) and db[0] == 'TB' and v <= db[1]: return 'NAT'
        return db
    return domB(('T', [ps[-1]]))
def operB(a, z):
    ps = a[1]
    if not ps: return ZB
    if len(ps) == 1:
        _, v, b = ps[0]
        if b == ZB:
            if v == 0: return ZB
            if v == INF: return Dpt(numNat(z) + 1, ZB)
            return z
        db = domB(b)
        if db == 'ZERO':
            return multBT(Dpt(v, operB(b, ZB)), numNat(z) + 1)
        if isinstance(db, tuple) and db[0] == 'TB' and v <= db[1]:
            return Dpt(v, xseq(b, db[1], numNat(z)))
        return Dpt(v, operB(b, z))
    return addBT(('T', ps[:-1]), operB(('T', [ps[-1]]), z))
def xseq(b, u, i):
    if i == 0: return Dpt(u, ZB)
    return operB(b, Dpt(u, xseq(b, u, i - 1)))
def op0(a): return operB(a, numBT(0))
def bucOf(t): return [('D', p[1], bucOf(p[2])) for p in t[1]]
def isOT(t): return bu.in_OT(bucOf(t))

def gen_ST(rng, tmax, maxlen=16, maxseed=4, nmax=4, steps=8):
    t0 = time.time()
    seen = set()
    while time.time() - t0 < tmax:
        u = rng.randrange(0, maxseed)
        vv = u + rng.randrange(1, maxseed + 2)
        M = diagSeq(u, vv)
        for _ in range(steps):
            key = tuple(M)
            if key not in seen and 2 < Lng(M) <= maxlen:
                seen.add(key)
                yield M
            n = rng.randrange(1, nmax + 1)
            M2 = safe(oper, M, n, budget=1)
            if M2 is None or M2 == M or Lng(M2) > maxlen * 3: break
            M = M2

def main():
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 420
    seeds = [int(s) for s in sys.argv[2:]] or [11, 222, 3333, 99, 2024]
    KMAX = 30
    B = dict(inst=0, hosts=set(), B1=0, B2=0, B3=0, B4=0, kvals={}, fails=[])
    diag = {'condIII-adm': {}, 'condVI-adm': {}}
    dnone = {'condIII-adm': [], 'condVI-adm': []}
    per_seed = tmax // max(len(seeds), 1)
    for sd in seeds:
        rng = random.Random(sd)
        t0 = time.time()
        for M in gen_ST(rng, per_seed):
            if time.time() - t0 > per_seed: break
            if not monoT(M): continue
            j1 = Lng(M) - 1
            if j1 <= 1: continue
            jp = parent(M, 0, j1)
            isV = condV(M) and adm(M, jp)
            isIII = condIII(M) and adm(M, jp)
            isVI = condVI(M) and adm(M, jp)
            if not (isV or isIII or isVI): continue
            TM = safe(Trans, M, budget=5)
            if TM is None: continue
            for n in (1, 2, 3, 4):
                Mn = safe(oper, M, n, budget=2)
                if Mn is None: continue
                TMn = safe(Trans, Mn, budget=6)
                if TMn is None: continue
                if isV:
                    e = entry(M, 1, jp)
                    c1 = safe(Mark, Pred(M), Adm(M, jp), budget=4)
                    if c1 is None: continue
                    t2 = bpHeadT(c1)
                    B['inst'] += 1; B['hosts'].add(tuple(M))
                    FS = safe(operB, TM, numBT(n), budget=5)
                    if FS is None: continue
                    B['B1'] += 1 if isOT(FS) else 0
                    dFS = domB(FS)
                    okd = (dFS == ('TB', e - 1)) if e > 0 else (dFS == 'NAT')
                    B['B4'] += 1 if okd else 0
                    cA = Dpt(e, addBT(t2, Dpt(e, Dpt(e, ZB))))
                    cB = Dpt(e, addBT(t2, Dpt(e, ZB)))
                    cC = Dpt(e, t2)
                    dsA = scb_decomps(FS, flatBT(cA))
                    t_1 = safe(op0, FS, budget=5)
                    t_2 = safe(op0, t_1, budget=5) if t_1 is not None else None
                    ok3 = False
                    if dsA and t_1 is not None and t_2 is not None:
                        S, Bb = dsA[0]
                        ok3 = (flatBT(t_1) == S + flatBT(cB) + Bb
                               and flatBT(t_2) == S + flatBT(cC) + Bb)
                    B['B3'] += 1 if ok3 else 0
                    if t_2 == TMn:
                        B['B2'] += 1; B['kvals'][2] = B['kvals'].get(2, 0) + 1
                    else:
                        kf = None
                        t = FS
                        for k in range(KMAX + 1):
                            if t == TMn: kf = k; break
                            t = safe(op0, t, budget=5)
                            if t is None: break
                        if kf is not None:
                            B['B2'] += 1
                            B['kvals'][kf] = B['kvals'].get(kf, 0) + 1
                        elif len(B['fails']) < 5:
                            B['fails'].append((M, n))
                else:
                    br = 'condIII-adm' if isIII else 'condVI-adm'
                    found = None
                    for moff in (0, -1, -2, 1):
                        m = n + moff
                        if m < 0: continue
                        t = safe(operB, TM, numBT(m), budget=5)
                        if t is None: continue
                        for k in range(KMAX + 1):
                            if t == TMn: found = (moff, k); break
                            t = safe(op0, t, budget=5)
                            if t is None: break
                        if found: break
                    if found:
                        diag[br][found] = diag[br].get(found, 0) + 1
                    elif len(dnone[br]) < 6:
                        dnone[br].append((M, n, entry(M, 1, j1)))
    print('(B) condV-adm deep: inst =', B['inst'], 'hosts =', len(B['hosts']))
    print('  B1 FSn in OT   :', B['B1'], '/', B['inst'])
    print('  B2 k found     :', B['B2'], '/', B['inst'], ' kvals =', B['kvals'])
    print('  B3 trajectory  :', B['B3'], '/', B['inst'])
    print('  B4 domB(FSn)   :', B['B4'], '/', B['inst'])
    if B['fails']: print('  FAILS:', B['fails'])
    for br in diag:
        tot = sum(diag[br].values()) + len(dnone[br])
        print('%s: (m-n,k) table %s  none-sample=%s'
              % (br, sorted(diag[br].items(), key=lambda x: -x[1])[:8],
                 dnone[br][:3]))

if __name__ == '__main__':
    main()
