"""r80-Y3: the DECISIVE census --- the §7.4 corollary ON T_PS, exactly as targeted.

For M in T_PS (NOT necessarily reduced):
  HYP: EX! j0. nextAdm M 0 j0 (Lng M - 1);  (M,j) : Marked;  leR M 0 j j0
  GOAL: EX! (s,b). scb_decomp (Mark (Pred M) j) s (flatBT (Mark (Pred M) j0)) b
                /\ scb_decomp (Mark M j)        s (flatBT (Mark M j0))        b

Mark M k = Mark (Red^2 M) k, so the goal is evaluated at the reduct (cached).

Also records, on the reduct N = Red^2 M, the diagnostic predicates:
  admN_j0 : adm N j0        (this is r79's Brick A -- known FALSE in general)
  TMB     : (Trans N, Mark N j0) : MarkedB
  refl    : j = j0

Bounds are reported; NON-VACUOUS counts only.
"""
import sys, itertools, random
sys.setrecursionlimit(10000)
import red_model as rm
from red_model import Lng, le0, Red, Pred, fmt
from trans_model import Mark, Trans, flatBT, scb_decomps, reduced, adm

_red2 = {}
def red2(M):
    k = tuple(M)
    if k not in _red2:
        _red2[k] = Red(Red(list(M)))
    return _red2[k]

_mark = {}
def mark(N, m):
    k = (tuple(N), m)
    if k not in _mark: _mark[k] = Mark(list(N), m)
    return _mark[k]
_trans = {}
def trans(N):
    k = tuple(N)
    if k not in _trans: _trans[k] = Trans(list(N))
    return _trans[k]

def hyps(M):
    """Return list of (j, j0) satisfying the article's hypotheses on M."""
    n = Lng(M)
    if n < 2: return []
    anc = [j for j in range(n) if le0(M, j, n-1)]
    cand = [j0 for j0 in range(n-1) if j0 in anc and adm(M, j0)
            and all((not le0(M,j,n-1)) or (not adm(M,j))
                    for j in range(j0+1, n-1))]
    if len(cand) != 1: return []
    j0 = cand[0]
    return [(j, j0) for j in range(n) if adm(M,j) and j in anc and le0(M, j, j0)]

def goal(N, j, j0):
    P = Pred(N)
    da = set((tuple(s),tuple(b)) for s,b in scb_decomps(mark(P,j), flatBT(mark(P,j0))))
    db = set((tuple(s),tuple(b)) for s,b in scb_decomps(mark(N,j), flatBT(mark(N,j0))))
    return len(da & db) == 1

def markedB(a,b): return len(scb_decomps(a, flatBT(b))) > 0

def run(gen, label):
    tot = 0; fail = 0; nadm0 = 0; ntmb = 0; nrefl = 0; cex = []
    for M in gen:
        hs = hyps(M)
        if not hs: continue
        try:
            N = red2(M)
            if not reduced(N): print("!! Red^2 not reduced", fmt(M)); continue
        except RecursionError: continue
        for (j, j0) in hs:
            tot += 1
            if j == j0: nrefl += 1
            try:
                ok = goal(N, j, j0)
                a0 = adm(N, j0)
                tb = markedB(trans(N), mark(N,j0))
            except (RecursionError, AssertionError): continue
            if not a0: nadm0 += 1
            if not tb: ntmb += 1
            if not ok:
                fail += 1
                if len(cex) < 8: cex.append((fmt(M), fmt(N), j, j0, a0, tb))
    print(f"[{label}] NON-VACUOUS exercises {tot}, FAILURES {fail}; "
          f"of the exercises: reflexive {nrefl}, adm(N,j0) FALSE {nadm0}, "
          f"(Trans N,Mark N j0) NOT in MarkedB {ntmb}")
    for c in cex: print("   CEX", c)
    return fail

def enum_TPS(maxe, maxl):
    cols = [(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    for L in range(2, maxl+1):
        for M in itertools.product(cols, repeat=L):
            yield list(M)

def rand_TPS(maxe, maxl, n, seed=987):
    r = random.Random(seed)
    for _ in range(n):
        L = r.randint(2, maxl)
        yield [(r.randint(0,maxe), r.randint(0,maxe)) for _ in range(L)]

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'full':
        e, l = int(sys.argv[2]), int(sys.argv[3])
        run(enum_TPS(e,l), f"FULL T_PS entries<={e} Lng<={l}")
    else:
        e, l, n = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        run(rand_TPS(e,l,n), f"RANDOM T_PS entries<={e} Lng<={l} n={n}")
