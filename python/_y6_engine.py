"""EXHAUSTIVE census of the RELAXED (adm-free) 7 nesting engine on RT_PS.

  ENG(N,m,m'):  N in RT_PS, le0 N m (Lng N -1), le0 N m' (Lng N -1),
                m <= m', m' < Lng N - 1
        ==>  EX! (s,b). scb_decomp (Mark (Pred N) m) s (flatBT (Mark (Pred N) m')) b
                     /\ scb_decomp (Mark N m)        s (flatBT (Mark N m'))        b

Reduced sequences are enumerated EXHAUSTIVELY by prefix DFS: `reduced` is
prefix-closed, because the RedCondA/RedCondB condition at column j only looks at
columns <= j.  (Cross-checked below against a brute-force filter.)

Also reports the ORIGINAL (Marked = adm + le0) engine on the same domain, which
is the frozen theorem Mark_nest_common_marked --- it must show 0 failures.
"""
import sys, time
sys.setrecursionlimit(100000)
import _y6_fast as F
from _y6_census import _le0mat, _adm, joint
from _y6_fast import Lng, fmt, reduced, cache_clear

def dfs(maxent, maxlng, out):
    vals = list(range(maxent+1))
    def rec(M):
        out(M)
        if len(M) == maxlng: return
        for a in vals:
            for b in vals:
                M2 = M + [(a,b)]
                if reduced(M2): rec(M2)
    for a in vals:
        for b in vals:
            M = [(a,b)]
            if reduced(M): rec(M)

def main(maxent, maxlng):
    t0 = time.time()
    stats = dict(seqs=0, nonvac=0, nontriv=0, err=0,
                 old_nonvac=0, old_fail=0, fail=0)
    fails = []
    def visit(N):
        stats['seqs'] += 1
        n = len(N)
        if n < 2: return
        j1 = n-1
        nx, le = _le0mat(N)
        for mp in range(j1):
            if not le[mp][j1]: continue
            for m in range(mp+1):
                if not le[m][j1]: continue
                stats['nonvac'] += 1
                if m != mp: stats['nontriv'] += 1
                am, amp = _adm(N, le, m), _adm(N, le, mp)
                old = am and amp
                if old: stats['old_nonvac'] += 1
                try:
                    d = joint(N, m, mp)
                except (RecursionError, RuntimeError, AssertionError):
                    stats['err'] += 1; continue
                if len(d) != 1:
                    stats['fail'] += 1
                    if old: stats['old_fail'] += 1
                    fails.append((list(N), m, mp, len(d), am, amp))
        if len(F._mark) > 400000: cache_clear()
    dfs(maxent, maxlng, visit)
    print(f"[ENGINE exhaustive] REDUCED N with entries<={maxent}, Lng<={maxlng}: "
          f"{stats['seqs']} reduced sequences")
    print(f"  RELAXED (adm-free) engine: NON-VACUOUS exercises = {stats['nonvac']} "
          f"(strictly m<m': {stats['nontriv']}), model-errors = {stats['err']}")
    print(f"  RELAXED engine FAILURES   = {stats['fail']}")
    print(f"  ORIGINAL (Marked) engine : NON-VACUOUS = {stats['old_nonvac']}, "
          f"FAILURES = {stats['old_fail']}   <-- must be 0 (frozen theorem)")
    print(f"  [{round(time.time()-t0,1)}s]")
    if fails:
        fails.sort(key=lambda f: (len(f[0]), max(max(p) for p in f[0]), f[1], f[2]))
        print("  MINIMAL failures (sorted by Lng, then max entry):")
        for (N,m,mp,nd,am,amp) in fails[:12]:
            print(f"    {fmt(N)}  m={m} m'={mp}  #common={nd}  adm(m)={am} adm(m')={amp}")

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]))
