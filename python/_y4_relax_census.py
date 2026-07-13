"""r81-Y4: WIDE census of the RELAXED nesting engine (target y4e_Mark_nest_relaxed).

TARGET (on RT_PS, NO hypothesis on the inner column j):
  HYP:  N reduced,  (N,j0) in Marked,  j <= j0   [NO hypothesis on the inner column j]

  GOAL1 : EX! (s0,b0). scb_decomp (Mark N j) s0 (flatBT (Mark N j0)) b0
  GOAL2 : that SAME (s0,b0) satisfies
          scb_decomp (Mark (Pred N) j) s0 (flatBT (Mark (Pred N) j0)) b0
  GOAL2E: EX! (s,b) decomposing BOTH  (the old engine's joint form)

Sub-observations (to see what actually carries the proof):
  COLL  : Mark N j = Mark N j0            (collapse)
  ZJ0   : Mark N j0 = 0_B
  ZJ    : Mark N j  = 0_B
  ADMJ  : adm N j                          (how many exercises the OLD engine reaches)
  J0LAST: j0 = Lng N - 1
BOUNDS ARE PRINTED.  Only NON-VACUOUS exercises (HYP true) are counted.
"""
import sys, random
sys.setrecursionlimit(20000)
from red_model import Lng, le0, Pred, fmt
from trans_model import Mark, flatBT, scb_decomps, reduced, adm, ZB

_mk = {}
def mark(N, m):
    k = (tuple(N), m)
    if k not in _mk:
        _mk[k] = Mark(list(N), m)
    return _mk[k]

def dset(t, c):
    return set((tuple(s), tuple(b)) for s, b in scb_decomps(t, c))

def marked(N, j0):
    return adm(N, j0) and le0(N, j0, Lng(N) - 1)

def gen_reduced(maxe, maxl):
    cols = [(a, b) for a in range(maxe + 1) for b in range(maxe + 1)]
    out = []
    def rec(M):
        if M: out.append(list(M))
        if len(M) == maxl: return
        for c in cols:
            M.append(c)
            if reduced(M): rec(M)
            M.pop()
    rec([])
    return out

def rand_reduced(maxe, maxl, n, seed=81081):
    r = random.Random(seed)
    out, tries = [], 0
    while len(out) < n and tries < n * 5000:
        tries += 1
        L = r.randint(1, maxl)
        M = [(r.randint(0, maxe), r.randint(0, maxe)) for _ in range(L)]
        if reduced(M):
            out.append(M)
    return out

def run(Ns, label):
    tot = 0
    f1 = f2 = f2e = 0
    n_coll = n_zj0 = n_zj = n_admj = n_j0last = n_refl = n_p = 0
    cex1, cex2 = [], []
    for N in Ns:
        n = Lng(N)
        P = Pred(N)
        for j0 in range(n):
            if not marked(N, j0):
                continue
            for j in range(j0 + 1):
                if False:  # inner column j: NO hypothesis at all
                    continue
                try:
                    mj, mj0 = mark(N, j), mark(N, j0)
                    pj, pj0 = Mark(list(P), j), Mark(list(P), j0)
                except (RecursionError, AssertionError, IndexError, ValueError):
                    continue
                tot += 1
                if j == j0: n_refl += 1
                if mj == mj0: n_coll += 1
                if mj0 == ZB: n_zj0 += 1
                if mj == ZB: n_zj += 1
                if adm(N, j): n_admj += 1
                if j0 == n - 1: n_j0last += 1
                D = dset(mj, flatBT(mj0))
                ok1 = (len(D) == 1)
                if not ok1:
                    f1 += 1
                    if len(cex1) < 8:
                        cex1.append((fmt(N), j, j0, len(D), adm(N, j),
                                     mj == mj0, mj0 == ZB, mj == ZB, j0 == n - 1))
                if j0 < n - 1:              # the corollary's setting: j0 < j1 = Lng N - 1
                    n_p += 1
                    DP = dset(pj, flatBT(pj0))
                    ok2 = ok1 and (next(iter(D)) in DP)
                    if not ok2:
                        f2 += 1
                        if len(cex2) < 8:
                            cex2.append((fmt(N), j, j0, len(D), len(DP), adm(N, j),
                                         mj == mj0, j0 == n - 1))
                    if len(D & DP) != 1:
                        f2e += 1
    print(f"[{label}]")
    print(f"  NON-VACUOUS exercises (N reduced, (N,j0):Marked, j<=j0, le0 N j j0): {tot}")
    print(f"    reflexive j=j0            : {n_refl}")
    print(f"    adm N j  TRUE (old engine): {n_admj}   -> UNMARKED-inner cases: {tot - n_admj}")
    print(f"    j0 = Lng N - 1            : {n_j0last}")
    print(f"    collapse Mark N j = Mark N j0 : {n_coll}")
    print(f"    Mark N j0 = 0_B : {n_zj0}    Mark N j = 0_B : {n_zj}")
    print(f"  GOAL1 exercises {tot}: FAILURES {f1}")
    print(f"  GOAL2 exercises (j0 < Lng N -1) {n_p}: FAILURES same-sb-at-Pred {f2} | EX!-joint {f2e}")
    for c in cex1:
        print("   G1-CEX N=%s j=%s j0=%s |D|=%s admj=%s coll=%s zj0=%s zj=%s j0last=%s" % c)
    for c in cex2:
        print("   G2-CEX N=%s j=%s j0=%s |D|=%s |DP|=%s admj=%s coll=%s j0last=%s" % c)
    return f1, f2, f2e

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'full':
        e, l = int(sys.argv[2]), int(sys.argv[3])
        Ns = gen_reduced(e, l)
        print(f"# reduced N (entries<={e}, Lng<={l}): {len(Ns)}", flush=True)
        run(Ns, f"FULL RT_PS entries<={e} Lng<={l}")
    else:
        e, l, n = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        Ns = rand_reduced(e, l, n)
        print(f"# random reduced N sampled: {len(Ns)}", flush=True)
        run(Ns, f"RANDOM RT_PS entries<={e} Lng<={l} n={len(Ns)}")
