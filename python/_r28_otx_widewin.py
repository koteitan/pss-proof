#!/usr/bin/env python3
"""r28-OTMEM probe 1: WIDE-window (m,k) search for the stepval identity
    Trans(M[n]) = (op0^k)(operB (Trans M) (numBT m))
focused on the branches/instances the naive window missed (r16 (C)-table
none=25 condVI-adm / none=69 condIII-adm), plus a full per-branch per-n map.

Key questions:
  Q1: are the NONE instances exactly the n=1 legs?
  Q2: does a wide window (m<=MMAX, k<=KMAX) recover them, and with what
      (m,k) pattern (k as function of host structure)?
  Q3: per-branch, per-n (m,k) table with minimal k, to pin the index
      calculations for the Isabelle stepval lemmas.
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import (Lng, entry, parent, hasParent, oper, seg, diagSeq,
                       monoT, zeroT, P)
from trans_model import (Trans, Mark, Pred, adm, Adm, condI, condIII, condV,
                         condVI, Dpt, addBT, PB, bpHeadV, bpHeadT, flatBT,
                         ZB)
import buchholz as bu

INF = float('inf')

class TimeoutErr(Exception): pass
def _handler(signum, frame): raise TimeoutErr()
signal.signal(signal.SIGALRM, _handler)

def safe(f, *a, budget=4):
    signal.alarm(budget)
    try:
        r = f(*a); signal.alarm(0); return r
    except (TimeoutErr, RecursionError, AssertionError):
        signal.alarm(0); return None

# ---------- Buchholz operB model (A23 form; same as _r16_e4_check) ----------
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

def condII(M):
    j1 = Lng(M) - 1; jp = parent(M, 0, j1)
    return entry(M, 1, j1) == 0 and not adm(M, jp)
def condIV(M):
    j1 = Lng(M) - 1; jp = parent(M, 0, j1)
    return (entry(M, 1, j1) > 0 and entry(M, 1, jp) >= entry(M, 1, j1)
            and not adm(M, jp))

def branch_of(M):
    j1 = Lng(M) - 1
    if not monoT(M): return 'multi'
    if j1 == 0: return 'single'
    t1 = safe(Trans, Pred(M))
    if t1 is None: return 'timeout'
    if t1 == ZB: return 't1zero'
    tag = None
    for nm, c in (('I', condI), ('II', condII), ('III', condIII),
                  ('IV', condIV), ('V', condV), ('VI', condVI)):
        if c(M): tag = nm; break
    if tag is None: tag = '??'
    jp = parent(M, 0, j1)
    return 'cond%s%s%s' % (tag, '-adm' if adm(M, jp) else '-nadm',
                           '-j1eq1' if j1 == 1 else '')

def gen_ST(rng, tmax, maxlen=14, maxseed=3, nmax=3, steps=7):
    t0 = time.time()
    seen = set()
    while time.time() - t0 < tmax:
        u = rng.randrange(0, maxseed)
        vv = u + rng.randrange(1, maxseed + 1)
        M = diagSeq(u, vv)
        for _ in range(steps):
            key = tuple(M)
            if key not in seen and 1 < Lng(M) <= maxlen:
                seen.add(key)
                yield M
            n = rng.randrange(1, nmax + 1)
            M2 = safe(oper, M, n, budget=1)
            if M2 is None or M2 == M or Lng(M2) > maxlen * 3: break
            M = M2

MMAX = 8
KMAX = 300

def find_mk(TM, TMn):
    """minimal-k (over m in 0..MMAX) pair with TMn = op0^k(operB TM [m])."""
    best = None
    for m in range(MMAX + 1):
        t = safe(operB, TM, numBT(m), budget=4)
        if t is None: continue
        for k in range(KMAX + 1):
            if best is not None and k >= best[1]: break
            if t == TMn:
                if best is None or k < best[1]: best = (m, k)
                break
            t = safe(op0, t, budget=4)
            if t is None: break
            if t == ZB and TMn != ZB:  # orbit died
                break
    return best

def main():
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    seeds = [int(s) for s in sys.argv[2:]] or [20260703, 424242]
    per_seed = tmax // max(len(seeds), 1)
    tab = {}    # (branch, n) -> {(m,k) or 'NONE': count}
    hard = []   # sample NONE hosts
    pool = 0
    for sd in seeds:
        rng = random.Random(sd)
        t0 = time.time()
        for M in gen_ST(rng, per_seed):
            if time.time() - t0 > per_seed: break
            pool += 1
            br = branch_of(M)
            if br in ('timeout', 'single'): continue
            j1 = Lng(M) - 1
            if br.startswith('cond') and j1 <= 1: continue
            TM = safe(Trans, M, budget=4)
            if TM is None: continue
            for n in (1, 2, 3):
                Mn = safe(oper, M, n, budget=1)
                if Mn is None: continue
                TMn = safe(Trans, Mn, budget=5)
                if TMn is None: continue
                got = find_mk(TM, TMn)
                key = tab.setdefault((br, n), {})
                kk = got if got else 'NONE'
                key[kk] = key.get(kk, 0) + 1
                if got is None and len(hard) < 8:
                    hard.append((br, n, M))
    print('pool =', pool)
    print('\n(m,k) minimal-k table per (branch, n):')
    for bk in sorted(tab, key=lambda x: (x[0], x[1])):
        tot = sum(tab[bk].values())
        top = sorted(tab[bk].items(), key=lambda x: -x[1])[:5]
        print('  %-24s n=%d tot=%-4d %s' % (bk[0], bk[1], tot, top))
    if hard:
        print('\nNONE samples:')
        for br, n, M in hard:
            print('  %s n=%d M=%s' % (br, n, M))

if __name__ == '__main__':
    main()
