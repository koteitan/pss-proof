"""TARGET 1: is p_7_4_Mark_nextAdm (A18-corrected) true on all of T_PS, or only RT_PS?

Statement tested (A18 form):
  M in T_PS, EX! j0. nextAdm M 0 j0 (Lng M - 1),  (M,j) in Marked,  leR M 0 j j0
  ==> EX! (s,b). scb_decomp (Mark (Pred M) j) s (flatBT (Mark (Pred M) j0)) b
               /\ scb_decomp (Mark M j)        s (flatBT (Mark M j0))        b
"""
import sys, itertools
sys.setrecursionlimit(10000)
from red_model import Lng, leR, adm, Pred, reduced, Red, fmt
from trans_model import Mark, flatBT, scb_decomps

def nextAdm0(M, j0, j1):
    return leR(M,0,j0,j1) and j0 < j1 and adm(M,j0) and \
        all((not leR(M,0,j,j1)) or (not adm(M,j)) for j in range(j0+1, j1))

def marked(M, m):
    return adm(M, m) and leR(M, 0, m, Lng(M)-1)

def joint(M, j, j0):
    A = Mark(Pred(M), j);  Ac = flatBT(Mark(Pred(M), j0))
    B = Mark(M, j);        Bc = flatBT(Mark(M, j0))
    da = set((tuple(s),tuple(b)) for s,b in scb_decomps(A, Ac))
    db = set((tuple(s),tuple(b)) for s,b in scb_decomps(B, Bc))
    return da & db

def run(maxent, maxlng):
    tot = nonvac = nontriv = 0
    bad = []; bad_nontriv = []
    pairs = [(a,b) for a in range(maxent) for b in range(maxent)]
    for L in range(1, maxlng+1):
        for M in itertools.product(pairs, repeat=L):
            M = list(M)
            j1 = Lng(M)-1
            ps = [j0 for j0 in range(j1) if nextAdm0(M,j0,j1)]
            if len(ps) != 1: continue
            j0 = ps[0]
            for j in range(Lng(M)):
                if not marked(M,j): continue
                if not leR(M,0,j,j0): continue
                nonvac += 1
                triv = (j == j0)
                if not triv: nontriv += 1
                try:
                    d = joint(M,j,j0)
                except RecursionError:
                    continue
                ok = (len(d) == 1)
                if not ok:
                    bad.append((M,j,j0,len(d),reduced(M)))
                    if not triv: bad_nontriv.append((M,j,j0,len(d),reduced(M)))
    print(f"entries<{maxent} Lng<={maxlng}: non-vacuous exercises = {nonvac}, "
          f"strictly non-trivial (j<j0) = {nontriv}")
    print(f"failures = {len(bad)} (non-trivial failures = {len(bad_nontriv)})")
    nr = [b for b in bad if not b[4]]; r = [b for b in bad if b[4]]
    print(f"  of failures: non-reduced = {len(nr)}, reduced = {len(r)}")
    for b in (bad_nontriv or bad)[:6]:
        M,j,j0,n,red = b
        print(f"  CEX {fmt(M)} j={j} j0={j0} #decomp={n} reduced={red} Red={fmt(Red(M))}")
        print(f"      Mark(Pred M,j)={Mark(Pred(M),j)}  Mark(Pred M,j0)={Mark(Pred(M),j0)}")
        print(f"      Mark(M,j)={Mark(M,j)}  Mark(M,j0)={Mark(M,j0)}")

if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]))
