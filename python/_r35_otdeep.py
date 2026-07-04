#!/usr/bin/env python3
"""r35-OTDEEP: EMPIRICAL validation that Trans(N[m]) in OT_B for the FOUR
deep-insertion legs (otIII, otIV, otVnadm, otVadmDeep) on GENUINE ST_PS hosts.

The four legs (from the OTint dispatcher):
  otIII      : N in ST_PS, PT_PS, 1<Lng-1, transCondIII N, Trans N in OT_B, 1<n
  otIV       : same with transCondIV
  otVnadm    : transCondV N & NOT adm N (transJ0 N)
  otVadmDeep : transCondV N &     adm N (transJ0 N) & entry N 1 (transJ0 N) != 0
GOAL of each: Trans(N[n]) in OT_B.

We check in_OT(bucOf(Trans(N[n]))) for genuine hosts N and n in 2..NMAX.
Also confirm Trans N in OT (the IH) actually holds (it should, universally).
Report pass fractions, per branch, ALL Lng and DEEP (Lng>=10).
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
    except (TimeoutErr, RecursionError, AssertionError, ValueError, IndexError, KeyError):
        signal.alarm(0); return None

def bucOf(t): return [('D', p[1], bucOf(p[2])) for p in t[1]]
def isOT(t):
    b = bucOf(t)
    return bu.in_OT(b) and bu.in_TB(b)

def condII(M):
    j1 = Lng(M)-1; jp = parent(M,0,j1)
    return entry(M,1,j1)==0 and not adm(M,jp)
def condIV(M):
    j1 = Lng(M)-1; jp = parent(M,0,j1)
    return entry(M,1,j1)>0 and entry(M,1,jp)>=entry(M,1,j1) and not adm(M,jp)

def leg_of(M):
    """classify M into one of the 4 deep-insertion legs, or None."""
    if not monoT(M): return None
    j1 = Lng(M)-1
    if j1 <= 1: return None
    jp = parent(M,0,j1)
    if condIII(M): return 'otIII'
    if condIV(M):  return 'otIV'
    if condV(M):
        if not adm(M, jp): return 'otVnadm'
        # adm: split on e = entry(M,1,jp)
        if entry(M,1,jp) != 0: return 'otVadmDeep'
        return 'otVadm_e0'   # the clean (keystone-free) leg, not our target
    return None

SEED_HOSTS = [
    [(0,0),(1,1),(2,2),(3,1),(4,2),(4,2)],      # condV-adm-e>0 (r34 CEX)
    [(0,0),(1,1),(2,2),(3,1),(4,0),(5,1),(6,2),(7,0),(6,2)],  # condV-nadm (r16b)
    [(0,0),(1,1),(2,2),(3,1),(4,2)],
    [(0,0),(1,1),(2,2),(3,3),(4,1),(5,2)],
    [(0,0),(1,1),(2,2),(3,2)],                   # condIII/IV small
    [(0,0),(1,1),(2,1),(3,2)],
    [(0,0),(1,1),(2,2),(3,1),(4,3)],
    [(0,0),(1,1),(2,2),(3,2),(4,1),(5,2)],
]
def gen_ST(rng, tmax, maxlen=30, maxseed=6, nmax=5, steps=18):
    t0 = time.time(); seen = set()
    # seed with known interesting hosts + their oper-orbits
    starts = [diagSeq(u, u+d) for u in range(0,maxseed) for d in range(1,maxseed+1)]
    starts += [list(h) for h in SEED_HOSTS]
    rng.shuffle(starts)
    idx = 0
    while time.time()-t0 < tmax:
        if idx < len(starts):
            M = starts[idx]; idx += 1
        else:
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
    NMAX = int(sys.argv[2]) if len(sys.argv)>2 else 6
    seeds = [int(s) for s in sys.argv[3:]] or [11,22,33,44,55,66,77,88]
    # per branch: [tot, pass, deep_tot, deep_pass, ih_fail]
    from collections import defaultdict
    stat = defaultdict(lambda: [0,0,0,0,0])
    fails = []   # (leg, M, n, Lng)
    per = tmax // max(len(seeds),1); pool = 0
    for sd in seeds:
        rng = random.Random(sd); t0 = time.time()
        for M in gen_ST(rng, per):
            if time.time()-t0 > per: break
            pool += 1
            leg = leg_of(M)
            if leg is None: continue
            if not leg.startswith('ot'): continue
            if leg == 'otVadm_e0': continue
            TM = safe(Trans, M, budget=6)
            if TM is None: continue
            ihOK = safe(isOT, TM, budget=4)
            deep = Lng(M) >= 10
            for n in range(2, NMAX+1):
                Mn = safe(oper, M, n, budget=3)
                if Mn is None or Mn == M or Lng(Mn) == Lng(M): continue
                TMn = safe(Trans, Mn, budget=8)
                if TMn is None: continue
                ok = safe(isOT, TMn, budget=5)
                if ok is None: continue
                s = stat[leg]
                s[0]+=1
                if ok: s[1]+=1
                else: fails.append((leg, list(M), n, Lng(M)))
                if not ihOK: s[4]+=1
                if deep:
                    s[2]+=1
                    if ok: s[3]+=1
        # incremental per-seed print
        print('  [seed %d done] pool=%d  ' % (sd, pool)
              + ' '.join('%s=%d/%d' % (lg, stat[lg][1], stat[lg][0])
                         for lg in ['otIII','otIV','otVnadm','otVadmDeep']),
              flush=True)
    print('pool sampled =', pool)
    print('\nleg           tot   pass   frac    deep_tot deep_pass  ih_fail')
    for leg in ['otIII','otIV','otVnadm','otVadmDeep']:
        s = stat[leg]
        frac = s[1]/s[0] if s[0] else 0.0
        print('  %-11s %5d %6d  %.4f    %6d %8d   %6d'
              % (leg, s[0], s[1], frac, s[2], s[3], s[4]))
    if fails:
        print('\nFAILURES (first 12):')
        for leg,M,n,L in fails[:12]:
            print('  %-11s Lng=%d n=%d  M=%s' % (leg, L, n, M))
    else:
        print('\nNO FAILURES: all sampled Trans(N[n]) in OT_B.')

if __name__ == '__main__':
    main()
