#!/usr/bin/env python3
"""r28-OTMEM probe 2: dissect the NONE hosts.
For M=[(0,0),(1,1),(2,2),(3,2),(4,2)] (condIII-adm, NONE at n=1,2,3) and the
condVI-adm n=1 NONE host, print flat strings of Trans M, Trans(M[n]),
operB(Trans M)(numBT m) and the full op0 orbits (until ZB or cap), marking
whether the orbit hits the target, dies at ZB, or exceeds the cap.
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import Lng, entry, parent, oper, diagSeq, monoT
from trans_model import Trans, Pred, adm, condI, condIII, condV, condVI, ZB, flatBT
from _r28_otx_widewin import numBT, operB, op0, domB, branch_of

def s(t):
    out = []
    for x in flatBT(t):
        if isinstance(x, tuple): out.append('D%s' % x[1])
        else: out.append({'Z':'0','(':'(',')':')',',':','}.get(x, str(x)))
    return ''.join(out)

def orbit_report(M, n, mmax=6, kcap=2000):
    TM = Trans(M)
    Mn = oper(M, n)
    TMn = Trans(Mn)
    print('=== M=%s  branch=%s  n=%d' % (M, branch_of(M), n))
    print('  M[n] =', Mn)
    print('  Trans M      =', s(TM))
    print('  domB(TransM) =', domB(TM))
    print('  Trans(M[n])  =', s(TMn))
    for m in range(mmax + 1):
        t = operB(TM, numBT(m))
        hit = None
        k = 0
        first = s(t)
        while k <= kcap:
            if t == TMn: hit = ('HIT', k); break
            if t == ZB: hit = ('DIED', k); break
            t = op0(t); k += 1
        if hit is None: hit = ('CAP', kcap)
        print('  m=%d %-12s operB=%s' % (m, hit, first[:100]))
        if m <= 2 and hit[0] != 'HIT':
            # print first few orbit values to see the shape drift
            t = operB(TM, numBT(m))
            for k in range(4):
                t = op0(t)
                print('        op0^%d = %s' % (k+1, s(t)[:100]))

M1 = [(0,0),(1,1),(2,2),(3,2),(4,2)]
for n in (1,2,3):
    orbit_report(M1, n)

M2 = [(0, 0), (1, 1), (2, 2), (3, 2), (4, 1), (5, 2), (6, 2), (7, 1), (8, 2)]
orbit_report(M2, 1)
