#!/usr/bin/env python3
"""Fast boundary-valley verifier for operCA, built on fast_pss (bitset le0).
Confirms: for reduced tiling-i1=1 base M with pj=parent M 1 (parent M 1 j1),
every block-start z=j0+q*w in N=M[n] has NO le0-predecessor j'>pj with
entry1(N) j' < entry M 1 j0 (the boundary readback valley clause).

Run: python3 valley_fast.py [maxlen=17] [maxe=8] [cap=12000] [nmax=7]
~1000x faster than the red_model.reach-based audits, so it reaches the depth
needed to exhibit the (rare) dip-bearing reduced sequences without artifacts."""
import sys, time
from fast_pss import (Lng, entry, oper, parent1, hasParent1, idx1, le0, fmt,
                      reduced, diagSeq, maxent)

def closure(ML, ME, CAP, nmax_gen=5):
    seeds = [diagSeq(a, b) for a in range(0, 5) for b in range(a, a+8)]
    prov = set(); frontier = []; members = []
    for s in seeds:
        k = tuple(s)
        if k not in prov and Lng(s) <= ML and maxent(s) <= ME:
            prov.add(k); frontier.append(s); members.append(s)
    while frontier and len(members) < CAP:
        nxt = []
        for M in frontier:
            for n in range(1, nmax_gen+1):
                N = oper(M, n); k = tuple(N)
                if k not in prov and Lng(N) <= ML and maxent(N) <= ME:
                    prov.add(k); nxt.append(N); members.append(N)
        frontier = nxt
    return members

def main():
    ML   = int(sys.argv[1]) if len(sys.argv) > 1 else 17
    ME   = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    CAP  = int(sys.argv[3]) if len(sys.argv) > 3 else 12000
    NMAX = int(sys.argv[4]) if len(sys.argv) > 4 else 7
    t0 = time.time()
    members = closure(ML, ME, CAP)
    print(f"closure {len(members)}  [{time.time()-t0:.1f}s]")
    tested = valviol = bs = dipM = 0; vex = None
    for M in members:
        j1 = Lng(M) - 1
        if j1 <= 0 or (entry(M, 0, j1) == 0 and entry(M, 1, j1) == 0): continue
        if idx1(M, j1) != 1 or not hasParent1(M, j1): continue
        j0 = parent1(M, j1); w = j1 - j0
        if not (j0 < j1) or not hasParent1(M, j0): continue
        if not reduced(M): continue
        pj = parent1(M, j0); ev0 = entry(M, 1, j0)
        if any(entry(M, 1, j0+s) < ev0 for s in range(w)): dipM += 1
        for n in range(2, NMAX+1):
            N = oper(M, n)
            for q in range(1, n):
                z = j0 + q*w
                if z >= Lng(N): continue
                bs += 1
                for jp in range(pj+1, z):
                    if le0(N, jp, z):
                        tested += 1
                        if entry(N, 1, jp) < ev0:
                            valviol += 1
                            if vex is None: vex = (fmt(M), n, q, jp, entry(N, 1, jp), ev0)
    print(f"dip-bearing reduced bases={dipM}  block-starts={bs}  le0-checks={tested}"
          f"  [{time.time()-t0:.1f}s]")
    print(f"VALLEY violations: {valviol}" + (f"  ex={vex}" if vex else "  OK"))

if __name__ == "__main__":
    main()
