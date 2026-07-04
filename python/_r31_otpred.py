#!/usr/bin/env python3
"""r31-OTRES: empirical test of the OTpred residual.

OTpred domain: N in ST_PS, Lng N > 2, nonzero last col,
  not (mono & condI), not (mono & condVI & not adm(N,jp)).
Conclusion to establish: Trans(Pred N) in OT_B.

Reduce to: is Trans(Pred N) an operB-value chain of Trans N (which is in OT_B)?
  A:  Trans(Pred N) == operB(Trans N)(numBT 0)              [plain descent]
  B:  exists m,k. Trans(Pred N) == op0^k(operB(Trans N)(numBT m))
Split by branch + parent status.  DEEP, genuine oper-BFS corpus.
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import (Lng, entry, parent, hasParent, oper, seg, diagSeq,
                       monoT, zeroT, P, idx1)
from trans_model import (Trans, Mark, Pred, adm, Adm, condI, condIII, condV,
                         condVI, Dpt, addBT, ZB)
from _r28_otx_widewin import (numBT, operB, op0, domB, safe, condII, condIV)

def stepval_chain(TM, TPred, mmax=8, kcap=400):
    for m in range(mmax + 1):
        t = safe(operB, TM, numBT(m), budget=5)
        if t is None: continue
        k = 0
        while k <= kcap:
            if t == TPred: return ('HIT', m, k)
            if t == ZB and TPred != ZB: break
            t2 = safe(op0, t, budget=5)
            if t2 is None: break
            if t2 == t: break
            t = t2; k += 1
    return ('MISS',)

def gen_ST(rng, tmax, maxlen=16, maxseed=4, nmax=4, steps=10):
    t0 = time.time(); seen = set()
    while time.time() - t0 < tmax:
        u = rng.randrange(0, maxseed)
        vv = u + rng.randrange(1, maxseed + 1)
        M = diagSeq(u, vv)
        for _ in range(steps):
            key = tuple(M)
            if key not in seen and 1 <= Lng(M) <= maxlen:
                seen.add(key); yield M
            n = rng.randrange(1, nmax + 1)
            M2 = safe(oper, M, n, budget=1)
            if M2 is None or M2 == M or Lng(M2) > maxlen * 3: break
            M = M2

def in_otpred_domain(M):
    if Lng(M) <= 2: return False
    j1 = Lng(M) - 1
    if entry(M,0,j1) == 0 and entry(M,1,j1) == 0: return False
    jp = parent(M, 0, j1)
    mono = monoT(M)
    if mono and condI(M): return False
    if mono and condVI(M) and not adm(M, jp): return False
    return True

def branch_tag(M):
    if not monoT(M): return 'multi'
    j1 = Lng(M) - 1; jp = parent(M, 0, j1)
    for nm, c in (('I', condI), ('II', condII), ('III', condIII),
                  ('IV', condIV), ('V', condV), ('VI', condVI)):
        if c(M):
            return 'cond%s%s' % (nm, '-adm' if adm(M, jp) else '-nadm')
    return 'mono??'

def has_last_parent(M):
    j1 = Lng(M) - 1
    return hasParent(M, idx1(M, j1), j1)

def main():
    rng = random.Random(4231)
    tmax = float(sys.argv[1]) if len(sys.argv) > 1 else 60.0
    from collections import defaultdict
    statsA = defaultdict(lambda: [0,0])   # branch -> [hitA, total]
    statsB = defaultdict(lambda: [0,0])
    miss_examples = []
    total = 0
    for M in gen_ST(rng, tmax):
        if not in_otpred_domain(M): continue
        TM = safe(Trans, M, budget=6)
        TPred = safe(Trans, Pred(M), budget=6)
        if TM is None or TPred is None: continue
        total += 1
        bt = branch_tag(M)
        par = 'P' if has_last_parent(M) else 'noP'
        key = bt + '/' + par
        # A
        t0 = safe(op0, TM, budget=5)
        okA = (t0 is not None and t0 == TPred)
        statsA[key][1] += 1
        if okA: statsA[key][0] += 1
        # B
        r = stepval_chain(TM, TPred)
        okB = (r[0] == 'HIT')
        statsB[key][1] += 1
        if okB:
            statsB[key][0] += 1
        else:
            if len(miss_examples) < 12:
                miss_examples.append((key, list(M), r))
    print("=== OTpred: total genuine domain hosts = %d ===" % total)
    print("\n-- A: Trans(Pred N) == operB(Trans N)(numBT 0) --")
    for k in sorted(statsA):
        h,t = statsA[k]; print("  %-22s %d/%d = %.3f" % (k,h,t, h/t if t else 0))
    print("\n-- B: Trans(Pred N) == op0^k(operB(Trans N)(numBT m)) --")
    for k in sorted(statsB):
        h,t = statsB[k]; print("  %-22s %d/%d = %.3f" % (k,h,t, h/t if t else 0))
    print("\n-- MISS examples (branch/par, M, chain-result) --")
    for key, M, r in miss_examples:
        print("  %-16s %s  %s" % (key, M, r))

if __name__ == '__main__':
    main()
