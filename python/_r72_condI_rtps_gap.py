#!/usr/bin/env python3
"""r72: is p_8_1_Trans_fseq_condI (pss_paper.thy:1766) TRUE on all of RT_PS n PT_PS,
or only on ST_PS (our scx_condI_exchange1 / scx_condI_descent)?

Region of interest: M in RT_PS n PT_PS \ ST_PS with transCondI M and Lng M - 1 > 1.
Hosts: EXHAUSTIVE enumeration of pair sequences (DFS over prefixes, pruned by
`reduced`, which is prefix-hereditary) up to length LMAX with entries <= VMAX.
ST_PS membership decided by the independent oracle yaBMS (`bms -s`), as in red_model.

Checks, for n = 1..NMAX:
  (1) Trans (M[n]) = operB (Trans M) (numBT (n-1))
  (2) lessBT (Trans (M[n])) (Trans M)
reported separately for standard vs NON-standard hosts.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import Lng, entry, monoT, oper, fmt, is_standard
import red_model as rm
from trans_model import reduced, condI, ZB
from _r15_vx_lib import Trans, operB, numBT, lessBT, guarded, SKIP

LMAX = int(os.environ.get('LMAX', 7))
VMAX = int(os.environ.get('VMAX', 3))
NMAX = int(os.environ.get('NMAX', 8))

def enum_reduced(lmax, vmax):
    """All reduced (RT_PS) pair sequences of length 1..lmax, entries 0..vmax."""
    out = []
    def dfs(pre):
        if pre:
            out.append(list(pre))
        if len(pre) == lmax: return
        for a in range(vmax + 1):
            for b in range(vmax + 1):
                cand = pre + [(a, b)]
                if reduced(cand):
                    dfs(cand)
    dfs([])
    return out

def main():
    allred = enum_reduced(LMAX, VMAX)
    hosts = [M for M in allred
             if Lng(M) - 1 > 1 and monoT(M) and condI(M)]
    print(f"enumeration: length<={LMAX}, entries<={VMAX}")
    print(f"  reduced (RT_PS) seqs      : {len(allred)}")
    print(f"  + mono + condI + Lng-1>1  : {len(hosts)}   (candidate hosts)")

    std, nonstd = [], []
    for M in hosts:
        (std if is_standard(M) else nonstd).append(M)
    print(f"  of which ST_PS (yaBMS)    : {len(std)}")
    print(f"  of which NON-standard     : {len(nonstd)}   <-- THE REGION IN QUESTION")

    sys.stdout.flush()
    for label, pool in (("ST_PS (sanity)", std), ("RT_PS \\ ST_PS (the claim)", nonstd)):
        ok1 = ok2 = f1 = f2 = skipped = 0
        fails = []
        print(f"\n=== checking {label}: hosts={len(pool)} ===", flush=True)
        for hi, M in enumerate(pool):
            if hi % 25 == 0:
                print(f"   [{hi}/{len(pool)}] ok1={ok1} f1={f1} ok2={ok2} f2={f2} skip={skipped}", flush=True)
            tM = guarded(Trans, M, budget=20)
            if tM is SKIP: skipped += 1; continue
            for n in range(1, NMAX + 1):
                Mn = oper(M, n)
                tMn = guarded(Trans, Mn, budget=20)
                if tMn is SKIP: skipped += 1; continue
                rhs = guarded(operB, tM, numBT(n - 1), budget=20)
                if rhs is SKIP: skipped += 1; continue
                if tMn == rhs: ok1 += 1
                else:
                    f1 += 1
                    fails.append(('(1)', M, n, tMn, rhs, tM))
                if lessBT(tMn, tM): ok2 += 1
                else:
                    f2 += 1
                    fails.append(('(2)', M, n, tMn, None, tM))
        print(f"\n=== RESULT {label}: hosts={len(pool)} ===", flush=True)
        print(f"  (1) exchange : PASS {ok1}  FAIL {f1}")
        print(f"  (2) descent  : PASS {ok2}  FAIL {f2}   (skipped/timeout {skipped})")
        for k, (which, M, n, tMn, rhs, tM) in enumerate(fails[:10]):
            print(f"  FAIL{k} {which} M={fmt(M)} n={n}")
            print(f"        M[n]      = {fmt(oper(M,n))}")
            print(f"        Trans M   = {tM}")
            print(f"        Trans M[n]= {tMn}")
            if rhs is not None:
                print(f"        operB rhs = {rhs}")
        if fails:
            print(f"  ... {len(fails)} failures total")

if __name__ == '__main__':
    main()
