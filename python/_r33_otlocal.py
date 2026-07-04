#!/usr/bin/env python3
"""r33-OTLOCAL: pin the op0-tower shape per condition, esp. condIV / condV-nadm
(absent from the r16 generic sweep) and re-examine condIII `none` with a WIDE
(m,k) window to confirm whether op0-tower-of-WHOLE-Trans-M is genuinely
impossible there (operB only touches the LAST top-level principal).

Tests, per genuine ST_PS mono keystone host M (condIII/IV/V, all adm/nadm) and
oper index n in {1,2,3,4}:
    Trans(M[n]) == (op0^k)(operB(Trans M)(numBT m))
searching m in a WIDE window [0..n+4] and k in [0..KMAX].  Reports per branch:
  - fraction with SOME (m,k) hit and the (m-n, k) histogram,
  - fraction NONE (genuinely no op0-tower-of-whole),
  - for NONE cases: does Trans(Pred M) have >1 top-level principal (=> the
    inserted principal is NOT the last => op0-of-whole impossible)?
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import (Lng, entry, parent, hasParent, oper, seg, diagSeq,
                       monoT, zeroT, P)
import red_model as rm
from trans_model import (Trans, Mark, Pred, adm, Adm, condI, condIII, condV,
                         condVI, Dpt, addBT, PB, bpHeadV, bpHeadT, flatBT,
                         scb_decomps, ZB, reduced)
import buchholz as bu

INF = float('inf')
class TimeoutErr(Exception): pass
def _handler(s, f): raise TimeoutErr()
signal.signal(signal.SIGALRM, _handler)
def safe(f, *a, budget=4):
    signal.alarm(budget)
    try:
        r = f(*a); signal.alarm(0); return r
    except (TimeoutErr, RecursionError, AssertionError, ValueError, IndexError):
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

def condII(M):
    j1 = Lng(M)-1; jp = parent(M,0,j1)
    return entry(M,1,j1)==0 and not adm(M,jp)
def condIV(M):
    j1 = Lng(M)-1; jp = parent(M,0,j1)
    return entry(M,1,j1)>0 and entry(M,1,jp)>=entry(M,1,j1) and not adm(M,jp)

def branch_of(M):
    j1 = Lng(M)-1
    if not monoT(M): return 'multi'
    if j1 == 0: return 'single'
    t1 = safe(Trans, Pred(M))
    if t1 is None: return 'timeout'
    if t1 == ZB: return 't1zero'
    tag = None
    for nm,c in (('I',condI),('II',condII),('III',condIII),('IV',condIV),('V',condV),('VI',condVI)):
        if c(M): tag = nm; break
    if tag is None: tag = '??'
    jp = parent(M,0,j1)
    return 'cond%s%s' % (tag, '-adm' if adm(M,jp) else '-nadm')

def npr_pred(M):
    """number of top-level principals of Trans(Pred M)."""
    t = safe(Trans, Pred(M))
    return None if t is None else len(t[1])

# --- wide-window op0-tower search ---
def op0tower_hit(TM, TMn, n, mmax_extra=4, KMAX=16):
    for m in range(0, n + mmax_extra + 1):
        t = safe(operB, TM, numBT(m), budget=4)
        if t is None: continue
        for k in range(KMAX + 1):
            if t == TMn: return (m - n, k)
            t = safe(op0, t, budget=4)
            if t is None: break
    return None

def gen_ST(rng, tmax, maxlen=15, maxseed=4, nmax=4, steps=9):
    t0 = time.time(); seen = set()
    while time.time()-t0 < tmax:
        u = rng.randrange(0, maxseed); vv = u + rng.randrange(1, maxseed+1)
        M = diagSeq(u, vv)
        for _ in range(steps):
            key = tuple(M)
            if key not in seen and 1 < Lng(M) <= maxlen:
                seen.add(key); yield M
            nn = rng.randrange(1, nmax+1)
            M2 = safe(oper, M, nn, budget=1)
            if M2 is None or M2 == M or Lng(M2) > maxlen*3: break
            M = M2

def main():
    tmax = int(sys.argv[1]) if len(sys.argv)>1 else 300
    seeds = [int(s) for s in sys.argv[2:]] or [11,22,33,44,55]
    hist = {}   # br -> {(moff,k):cnt}
    none = {}   # br -> cnt
    none_multiprin = {}  # br -> cnt where Trans(Pred M) has >1 top prin
    tot = {}
    per = tmax // max(len(seeds),1); pool = 0
    for sd in seeds:
        rng = random.Random(sd); t0 = time.time()
        for M in gen_ST(rng, per):
            if time.time()-t0 > per: break
            pool += 1
            br = branch_of(M)
            if not br.startswith('cond'): continue
            if br[4:].rstrip('-adm').rstrip('-nadm') in ('I','II','VI'):
                pass  # keep all conds for reference
            TM = safe(Trans, M, budget=5)
            if TM is None: continue
            j1 = Lng(M)-1
            if j1 <= 1: continue
            npp = npr_pred(M)
            for n in (1,2,3,4):
                Mn = safe(oper, M, n, budget=2)
                if Mn is None or Mn == M: continue
                TMn = safe(Trans, Mn, budget=6)
                if TMn is None: continue
                tot[br] = tot.get(br,0)+1
                hit = op0tower_hit(TM, TMn, n)
                if hit is None:
                    none[br] = none.get(br,0)+1
                    if npp is not None and npp > 1:
                        none_multiprin[br] = none_multiprin.get(br,0)+1
                else:
                    hist.setdefault(br,{})[hit] = hist.setdefault(br,{}).get(hit,0)+1
    print('pool =', pool)
    print('\nper-branch op0-tower-of-whole (WIDE m in [0..n+4], k<=16):')
    for br in sorted(tot):
        h = hist.get(br,{})
        nn = none.get(br,0)
        top = sorted(h.items(), key=lambda x:-x[1])[:6]
        print('  %-14s tot=%3d  none=%3d (multiprin-pred=%d)  %s'
              % (br, tot[br], nn, none_multiprin.get(br,0), top))

if __name__ == '__main__':
    main()
