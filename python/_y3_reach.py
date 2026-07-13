"""r80-Y3: is a GOAL-failure REACHABLE from the T_PS hypotheses?

The ancestry-only engine is FALSE (see _y3_relax_engine.py): the EX! goal fails
at reduced N exactly where adm(N,m') is false.  But the TARGET only ever feeds
the engine reducts R = Red^2 M of M in T_PS satisfying:

    (H1) EX! j0. nextAdm M 0 j0 (Lng M - 1)
    (H2) (M,j) in Marked          [ = adm M j /\ le0 M j (Lng M -1) ]
    (H3) le0 M j j0

So: does ANY such M make the goal FAIL?  If yes -> the TARGET ITSELF IS FALSE and
must be refuted.  If no -> the hypotheses at M exclude the bad reducts.

Part 1: the known adm-counterexample cexM = (0,0)(1,6)(2,5)(3,3)(4,4), j0 = 3.
Part 2: brute preimage search over M in T_PS for the failing triples.
"""
import sys, itertools
sys.setrecursionlimit(100000)
from red_model import Lng, le0, Red, Pred, fmt
from trans_model import Mark, flatBT, scb_decomps, reduced, adm

def red2(M): return Red(Red(list(M)))

def dset(t, c):
    return set((tuple(s), tuple(b)) for s, b in scb_decomps(t, c))

def goal(N, m, mp):
    P = Pred(N)
    a = dset(Mark(list(P), m), flatBT(Mark(list(P), mp)))
    b = dset(Mark(list(N), m), flatBT(Mark(list(N), mp)))
    return len(a & b)          # 1 = EX! holds; 0 = no common decomp; >1 = not unique

def nextadm_j0(M):
    """unique j0 with nextAdm M 0 j0 (Lng M -1), or None."""
    n = Lng(M)
    if n < 2: return None
    j1 = n - 1
    cand = [j0 for j0 in range(j1) if le0(M, j0, j1) and adm(M, j0)
            and all((not le0(M, j, j1)) or (not adm(M, j)) for j in range(j0 + 1, j1))]
    return cand[0] if len(cand) == 1 else None

def marked(M, j):
    return adm(M, j) and le0(M, j, Lng(M) - 1)

def check(M, tag):
    j0 = nextadm_j0(M)
    if j0 is None:
        print(f"  {tag}: {fmt(M)} -- NO unique nextAdm j0 (H1 fails) -> not an exercise")
        return
    N = red2(M)
    print(f"  {tag}: M={fmt(M)}  j0={j0}  Red^2 M={fmt(N)}  adm(N,j0)={adm(N,j0)}")
    for j in range(Lng(M)):
        if not marked(M, j): continue
        if not le0(M, j, j0): continue
        k = goal(N, j, j0)
        status = "OK(EX!)" if k == 1 else ("FAIL: no common decomp" if k == 0
                                           else f"FAIL: {k} common decomps (not unique)")
        print(f"      j={j}: |common decomps| = {k}   {status}")

print("=== PART 1: the known adm-counterexample cexM (y3z_C4_false / y3z_brickA_false)")
check([(0,0),(1,6),(2,5),(3,3),(4,4)], "cexM")

print()
print("=== PART 2: preimage search -- brute force M in T_PS, does the GOAL ever FAIL?")
def sweep(maxe, maxl):
    cols = [(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    tot = fail = nadm = 0
    cex = []
    for L in range(2, maxl+1):
        for M in itertools.product(cols, repeat=L):
            M = list(M)
            j0 = nextadm_j0(M)
            if j0 is None: continue
            try:
                N = red2(M)
            except RecursionError: continue
            a0 = adm(N, j0)
            for j in range(Lng(M)):
                if not marked(M, j) or not le0(M, j, j0): continue
                tot += 1
                if not a0: nadm += 1
                try:
                    k = goal(N, j, j0)
                except (RecursionError, AssertionError):
                    tot -= 1
                    continue
                if k != 1:
                    fail += 1
                    if len(cex) < 10: cex.append((fmt(M), fmt(N), j, j0, a0, k))
    print(f"[T_PS entries<={maxe} Lng<={maxl}] NON-VACUOUS exercises {tot}, "
          f"GOAL FAILURES {fail}, of exercises adm(Red^2 M, j0) FALSE: {nadm}")
    for c in cex:
        print("   TARGET-CEX M=%s  Red^2M=%s  j=%s j0=%s adm(N,j0)=%s |decomps|=%s" % c)
    return fail

for (e, l) in [(int(sys.argv[1]), int(sys.argv[2]))]:
    sweep(e, l)
