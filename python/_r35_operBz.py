#!/usr/bin/env python3
"""r35-OTDEEP probe: for the deep-insertion legs, does there EXIST a term z
(a general BT, in dom(Trans N), z in OT_B) with

        Trans(N[m]) = operB (Trans N) z   ?

If YES for the deep-insertion legs, then the leg closes via b1x_master
(OT_B closed under a[z] for z in OT_B, z in dom a  or NatSet) -- the SAME
machinery e4x_OT_B_operB_numBT uses, but with a general (non-nat) index z.

Candidate z: every SUBTERM of Trans(N[m]) (the graft is read off directly),
plus numBT(0..n+4).  Report per leg: fraction with SOME such z, and whether
the winning z is in dom(Trans N) and in OT_B.
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import (Lng, entry, parent, hasParent, oper, seg, diagSeq,
                       monoT, zeroT, P)
import red_model as rm
from trans_model import (Trans, Mark, Pred, adm, Adm, condI, condIII, condV,
                         condVI, Dpt, addBT, PB, bpHeadV, bpHeadT, flatBT, ZB)
import buchholz as bu

INF = float('inf')
class TimeoutErr(Exception): pass
def _handler(s, f): raise TimeoutErr()
signal.signal(signal.SIGALRM, _handler)
def safe(f, *a, budget=4):
    signal.alarm(budget)
    try:
        r = f(*a); signal.alarm(0); return r
    except (TimeoutErr, RecursionError, AssertionError, ValueError, IndexError, KeyError):
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

def in_dom(z, a):
    """z in dom(a)?  dom tags: EMPTY|ZERO|NAT|('TB',u)."""
    d = domB(a)
    if d == 'EMPTY': return False
    if d == 'ZERO': return z == ZB
    if d == 'NAT': return all(p == ('D',0,ZB) for p in z[1])
    # ('TB', u): z in T_u  (top indices <= u)
    u = d[1]
    return all(p[1] <= u for p in z[1])

def subterms(t):
    """all BT subterms of t (including t itself and ZB)."""
    out = [t]
    for p in t[1]:
        out += subterms(p[2])
    # also Sigma-tails: Trm(ps[i:]) for the right-spine
    ps = t[1]
    for i in range(1, len(ps)):
        out.append(('T', ps[i:]))
    return out

def isOT(t):
    b = bu.bucOf(t) if hasattr(bu,'bucOf') else None
    b = [('D', p[1], _b(p[2])) for p in t[1]]
    return bu.in_OT(b) and bu.in_TB(b)
def _b(t): return [('D', p[1], _b(p[2])) for p in t[1]]

def find_z(TM, TMn, n):
    """find z with operB(TM,z)==TMn.  returns (z, in_dom, in_OT) or None."""
    cands = []
    for k in range(0, n+6): cands.append(numBT(k))
    cands += subterms(TMn)
    seen = set()
    for z in cands:
        key = repr(z)
        if key in seen: continue
        seen.add(key)
        r = safe(operB, TM, z, budget=4)
        if r == TMn:
            return (z, in_dom(z, TM), safe(isOT, z, budget=3))
    return None

def condII(M):
    j1 = Lng(M)-1; jp = parent(M,0,j1)
    return entry(M,1,j1)==0 and not adm(M,jp)
def condIV(M):
    j1 = Lng(M)-1; jp = parent(M,0,j1)
    return entry(M,1,j1)>0 and entry(M,1,jp)>=entry(M,1,j1) and not adm(M,jp)
def leg_of(M):
    if not monoT(M): return None
    j1 = Lng(M)-1
    if j1 <= 1: return None
    jp = parent(M,0,j1)
    if condIII(M): return 'otIII'
    if condIV(M):  return 'otIV'
    if condV(M):
        if not adm(M, jp): return 'otVnadm'
        if entry(M,1,jp) != 0: return 'otVadmDeep'
        return 'otVadm_e0'
    return None

def gen_ST(rng, tmax, maxlen=26, maxseed=5, nmax=4, steps=14):
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
    NMAX = int(sys.argv[2]) if len(sys.argv)>2 else 5
    seeds = [int(s) for s in sys.argv[3:]] or [11,22,33,44,55,66,77,88]
    from collections import defaultdict
    stat = defaultdict(lambda: [0,0,0,0])  # tot, hit, hit_indom, hit_OT
    examples = defaultdict(list)
    per = tmax // max(len(seeds),1)
    for sd in seeds:
        rng = random.Random(sd); t0 = time.time()
        for M in gen_ST(rng, per):
            if time.time()-t0 > per: break
            leg = leg_of(M)
            if leg is None or not leg.startswith('ot'): continue
            TM = safe(Trans, M, budget=6)
            if TM is None: continue
            for n in range(2, NMAX+1):
                Mn = safe(oper, M, n, budget=3)
                if Mn is None or Mn == M or Lng(Mn) == Lng(M): continue
                TMn = safe(Trans, Mn, budget=8)
                if TMn is None: continue
                s = stat[leg]; s[0]+=1
                r = safe(find_z, TM, TMn, n, budget=8)
                if r is not None:
                    z, ind, iot = r
                    s[1]+=1
                    if ind: s[2]+=1
                    if iot: s[3]+=1
                    if len(examples[leg]) < 3:
                        examples[leg].append((list(M), n, bu.fmt(_b(z)) if z[1] else '0',
                                              ind, iot, str(domB(TM))))
    print('pool legs: probe operB(Trans N)(z) == Trans(N[m]) for SOME term z')
    print('\nleg           tot    hit   hit/tot   indom   inOT')
    for leg in ['otIII','otIV','otVnadm','otVadmDeep']:
        s = stat[leg]
        f = s[1]/s[0] if s[0] else 0
        print('  %-11s %5d %6d   %.4f   %5d  %5d' % (leg, s[0], s[1], f, s[2], s[3]))
    for leg in ['otIII','otIV','otVnadm','otVadmDeep']:
        for ex in examples[leg]:
            print('  EX %-9s n=%d z=%s indom=%s inOT=%s dom(TM)=%s M=%s'
                  % (leg, ex[1], ex[2], ex[3], ex[4], ex[5], ex[0]))

if __name__ == '__main__':
    main()
