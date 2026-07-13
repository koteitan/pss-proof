"""r81-Y6 censuses.

(T)  TARGET, the article's 7.4 Mark/NextAdm proposition (A18 form) on ALL of T_PS:
       M in T_PS, EX! j0. nextAdm M 0 j0 (Lng M - 1), (M,j) in Marked, leR M 0 j j0
       ==> EX! (s,b). scb_decomp (Mark (Pred M) j) s (flatBT (Mark (Pred M) j0)) b
                    /\ scb_decomp (Mark M j)       s (flatBT (Mark M j0))       b

(E)  RELAXED ENGINE on RT_PS (what the other front must deliver):
       N in RT_PS, le0 N m (Lng N -1), le0 N m' (Lng N -1), m <= m', m' < Lng N - 1
       ==> EX! (s,b). ... same, with (N,m,m') for (M,j,j0)
     i.e. Mark_nest_common_marked with `Marked` weakened to `Marked minus adm`.
     Reduced sequences are enumerated EXHAUSTIVELY by prefix DFS (reduced is
     prefix-closed: the RedCondA/B condition at column j only looks at columns <= j).

(S)  CRUX (*): Mark (Pred M) i = Mark (Pred (Red (Red M))) i   (model-level check of
     the already-proved y3s_Pred_funpow_Red + y3s_Mark_funpow_Red).

Usage:
  python3 _y6_census.py target-ex  MAXENT MAXLNG      (exhaustive, entries 0..MAXENT)
  python3 _y6_census.py target-rnd MAXENT MAXLNG N SEED
  python3 _y6_census.py engine-ex  MAXENT MAXLNG      (exhaustive over REDUCED N)
  python3 _y6_census.py crux-rnd   MAXENT MAXLNG N SEED
"""
import sys, itertools, random, time
sys.setrecursionlimit(100000)
import _y6_fast as F
from _y6_fast import Mark, Pred, Red, flatBT, scb_decomps, Lng, entry, fmt, cache_clear

# ---------- fast un-memoised local predicates (used for the cheap prefilter) ----------
def _le0mat(M):
    n = len(M)
    nx = [[False]*n for _ in range(n)]
    for a in range(n):
        for b in range(a+1, n):
            if entry(M,0,a) < entry(M,0,b) and all(entry(M,0,c) >= entry(M,0,b)
                                                   for c in range(a+1,b)):
                nx[a][b] = True
    le = [[False]*n for _ in range(n)]
    for a in range(n): le[a][a] = True
    for a in range(n-1, -1, -1):
        for b in range(a+1, n):
            if any(nx[a][c] and le[c][b] for c in range(a+1, b+1)):
                le[a][b] = True
    return nx, le

def _nx1(M, le, a, b):
    n = len(M)
    if not (a < n and b < n and a < b): return False
    if not (entry(M,1,a) < entry(M,1,b)): return False
    if not le[a][b]: return False
    return all(entry(M,1,c) >= entry(M,1,b) for c in range(a+1, n) if le[c][b])

def _adm(M, le, j):
    n = len(M)
    if j > n: return False
    a = _nx1(M, le, max(j-1,0), j) and (j+1 < n and _nx1(M, le, j, j+1))
    return not a

def analyse(M):
    """returns (j0, [j...]) for the target's non-vacuous exercises, or None"""
    n = len(M)
    if n < 2: return None
    j1 = n-1
    nx, le = _le0mat(M)
    cand = []
    for j0 in range(j1):
        if not le[j0][j1]: continue
        if not _adm(M, le, j0): continue
        if any(le[j][j1] and _adm(M, le, j) for j in range(j0+1, j1)): continue
        cand.append(j0)
    if len(cand) != 1: return None
    j0 = cand[0]
    js = [j for j in range(n) if le[j][j1] and _adm(M, le, j) and le[j][j0]]
    if not js: return None
    return j0, js

def joint(M, j, j0):
    A = Mark(Pred(M), j);  Ac = flatBT(Mark(Pred(M), j0))
    B = Mark(M, j);        Bc = flatBT(Mark(M, j0))
    da = set((tuple(s), tuple(b)) for s, b in scb_decomps(A, Ac))
    db = set((tuple(s), tuple(b)) for s, b in scb_decomps(B, Bc))
    return da & db

# ---------------------------- (T) target ----------------------------
class Tally:
    def __init__(self, name):
        self.name = name; self.scanned = 0
        self.nonvac = 0; self.nontriv = 0
        self.nonred = 0; self.nonred_nontriv = 0
        self.fail = []; self.err = 0
        self.t0 = time.time()
    def report(self):
        print(f"[{self.name}] scanned={self.scanned}  "
              f"NON-VACUOUS exercises={self.nonvac} (strictly j<j0: {self.nontriv})")
        print(f"    of which M NOT reduced (the genuinely-T_PS content) = {self.nonred} "
              f"(strictly j<j0: {self.nonred_nontriv})")
        print(f"    FAILURES = {len(self.fail)}   model-errors = {self.err}   "
              f"[{round(time.time()-self.t0,1)}s]")
        for (M, j, j0, nd) in self.fail[:8]:
            print(f"    CEX {fmt(M)} j={j} j0={j0} #common-scb-positions={nd} "
                  f"reduced={F.reduced(M)} R2={fmt(Red(Red(M)))}")

def target_one(M, T):
    T.scanned += 1
    a = analyse(M)
    if a is None: return
    j0, js = a
    red = F.reduced(M)
    for j in js:
        T.nonvac += 1
        triv = (j == j0)
        if not triv: T.nontriv += 1
        if not red:
            T.nonred += 1
            if not triv: T.nonred_nontriv += 1
        try:
            d = joint(M, j, j0)
        except (RecursionError, RuntimeError, AssertionError):
            T.err += 1; continue
        if len(d) != 1:
            T.fail.append((list(M), j, j0, len(d)))

def target_ex(maxent, maxlng):
    T = Tally(f"TARGET exhaustive entries<={maxent} Lng<={maxlng}")
    pairs = [(a,b) for a in range(maxent+1) for b in range(maxent+1)]
    for L in range(2, maxlng+1):
        for M in itertools.product(pairs, repeat=L):
            target_one(list(M), T)
            if T.scanned % 400000 == 0:
                cache_clear()
                print(f"  ... {T.scanned} scanned, nonvac={T.nonvac}, fails={len(T.fail)}",
                      flush=True)
    T.report()

def target_rnd(maxent, maxlng, N, seed):
    random.seed(seed)
    T = Tally(f"TARGET random entries<={maxent} Lng<={maxlng} N={N} seed={seed}")
    for i in range(N):
        L = random.randint(2, maxlng)
        M = [(random.randint(0,maxent), random.randint(0,maxent)) for _ in range(L)]
        target_one(M, T)
        if (i+1) % 20000 == 0:
            cache_clear()
            print(f"  ... {i+1} sampled, nonvac={T.nonvac}, fails={len(T.fail)}", flush=True)
    T.report()

# ---------------------------- (E) relaxed engine ----------------------------
def gen_reduced(maxent, maxlng):
    """DFS over reduced sequences (reduced is prefix-closed)."""
    vals = range(maxent+1)
    stack = [[(a,b)] for a in vals for b in vals]
    stack = [M for M in stack if F.reduced(M)]
    out = []
    def rec(M):
        out.append(list(M))
        if len(M) == maxlng: return
        for a in vals:
            for b in vals:
                M2 = M + [(a,b)]
                if F.reduced(M2): rec(M2)
    for M in stack: rec(M)
    return out

def engine_ex(maxent, maxlng):
    t0 = time.time()
    Ns = gen_reduced(maxent, maxlng)
    print(f"[ENGINE] exhaustive REDUCED N, entries<={maxent} Lng<={maxlng}: "
          f"{len(Ns)} reduced sequences ({round(time.time()-t0,1)}s)", flush=True)
    nonvac = nontriv = err = 0
    fails = []
    # also: with the marked (adm) hypotheses, for comparison
    nonvac_marked = 0
    for N in Ns:
        n = len(N)
        if n < 2: continue
        j1 = n-1
        nx, le = _le0mat(N)
        for mp in range(j1):                      # m' = outer column, m' < Lng N - 1
            if not le[mp][j1]: continue
            for m in range(mp+1):                 # m <= m'
                if not le[m][j1]: continue
                nonvac += 1
                if m != mp: nontriv += 1
                if _adm(N, le, m) and _adm(N, le, mp): nonvac_marked += 1
                try:
                    d = joint(N, m, mp)
                except (RecursionError, RuntimeError, AssertionError):
                    err += 1; continue
                if len(d) != 1:
                    fails.append((list(N), m, mp, len(d), _adm(N,le,m), _adm(N,le,mp)))
        if len(F._mark) > 300000: cache_clear()
    print(f"[ENGINE] NON-VACUOUS exercises = {nonvac} (strictly m<m': {nontriv}); "
          f"of these {nonvac_marked} also satisfy the OLD (adm) hypotheses")
    print(f"[ENGINE] FAILURES = {len(fails)}  model-errors = {err}  "
          f"[{round(time.time()-t0,1)}s]")
    for (N,m,mp,nd,am,amp) in fails[:10]:
        print(f"    CEX {fmt(N)} m={m} m'={mp} #pos={nd} adm(m)={am} adm(m')={amp}")

# ---------------------------- (S) crux ----------------------------
def crux_rnd(maxent, maxlng, N, seed):
    random.seed(seed)
    t0 = time.time(); ok = err = 0; bad = []
    for i in range(N):
        L = random.randint(1, maxlng)
        M = [(random.randint(0,maxent), random.randint(0,maxent)) for _ in range(L)]
        R = Red(Red(M))
        try:
            for i2 in range(len(M)+2):
                if Mark(Pred(M), i2) != Mark(Pred(R), i2): bad.append((list(M), i2))
                if Mark(M, i2) != Mark(R, i2): bad.append(('M-side', list(M), i2))
            ok += 1
        except (RecursionError, RuntimeError, AssertionError):
            err += 1
        if (i+1) % 5000 == 0: cache_clear()
    print(f"[CRUX (*)] entries<={maxent} Lng<={maxlng} N={N}: {ok} sequences checked "
          f"(all non-vacuous), errors={err}, VIOLATIONS={len(bad)} "
          f"[{round(time.time()-t0,1)}s]")
    for b in bad[:5]: print("   ", b)

if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "target-ex":  target_ex(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == "target-rnd": target_rnd(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]))
    elif cmd == "engine-ex": engine_ex(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == "crux-rnd": crux_rnd(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]))
