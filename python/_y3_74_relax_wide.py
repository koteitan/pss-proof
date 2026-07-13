"""r80-Y3: WIDE census of the RELAXED §7.4 engine (no adm hypothesis anywhere).

Target (on a REDUCED N, which is exactly Red^2 M for M in T_PS):
  HYP:  le0 N j j0,  le0 N j0 (Lng N - 1),  j0 < Lng N - 1
  GOAL: EX! (s,b). scb_decomp (Mark (Pred N) j)  s (flatBT (Mark (Pred N) j0)) b
                /\ scb_decomp (Mark N j)         s (flatBT (Mark N j0))        b

Also censuses the two sub-bricks:
  (P)  Mark N k is principal-or-zero (isPTB_str (flatBT (Mark N k)) or = 0B) for EVERY k
  (N)  (Mark N j, Mark N j0) : MarkedB  under HYP  (the nesting brick)
  (T)  common Trans-position of Mark _ j in Trans (Pred N) and Trans N  under HYP

The r77/r78 censuses bounded entries by <3 / <4 and that is exactly what hid the
r79 counterexample (a row-1 entry of 6).  Here: entries <= MAXE (default 8),
Lng <= MAXL (default 6), FULL enumeration of reduced sequences by prefix-pruned
DFS (reduced-ness is prefix-closed), plus random sampling beyond that.

Only NON-VACUOUS exercises (HYP true) are counted.
"""
import sys, itertools, random
sys.setrecursionlimit(10000)
import red_model as rm
from red_model import Lng, le0, leR, Pred, fmt
from trans_model import Mark, Trans, flatBT, scb_decomps, reduced, adm, isPTB_str, ZB

def gen_reduced(maxe, maxl):
    """DFS over columns; reduced-ness is prefix-closed so we can prune."""
    cols = [(a,b) for a in range(maxe+1) for b in range(maxe+1)]
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

def joint(N, j, j0):
    da = set((tuple(s),tuple(b)) for s,b in scb_decomps(Mark(Pred(N),j), flatBT(Mark(Pred(N),j0))))
    db = set((tuple(s),tuple(b)) for s,b in scb_decomps(Mark(N,j),        flatBT(Mark(N,j0))))
    return da & db

def princ(t):
    return t == ZB or isPTB_str(flatBT(t))

def markedB(a, b):
    return len(scb_decomps(a, flatBT(b))) > 0

def check(N, report):
    n = Lng(N)
    # brick (P): every column
    for k in range(n + 2):
        report('P', princ(Mark(N,k)), (N,k))
    for j0 in range(n-1):
        if not le0(N, j0, n-1): continue
        for j in range(j0+1):
            if not le0(N, j, j0): continue
            # NON-VACUOUS exercise of HYP
            report('GOAL', len(joint(N,j,j0)) == 1, (N,j,j0))
            report('N',    markedB(Mark(N,j), Mark(N,j0)), (N,j,j0))
            report('NP',   markedB(Mark(Pred(N),j), Mark(Pred(N),j0)), (N,j,j0))
            # is the adm hypothesis actually present?  (how often is it VIOLATED,
            # i.e. how many of these exercises the old engine could NOT reach)
            report('adm-j',  adm(N,j),  (N,j,j0))
            report('adm-j0', adm(N,j0), (N,j0))

def main():
    maxe = int(sys.argv[1]) if len(sys.argv)>1 else 8
    maxl = int(sys.argv[2]) if len(sys.argv)>2 else 6
    nrand = int(sys.argv[3]) if len(sys.argv)>3 else 0
    stats = {}
    cex = {}
    def report(key, ok, wit):
        t,f = stats.get(key,(0,0))
        stats[key] = (t+1, f + (0 if ok else 1))
        if not ok and key not in cex: cex[key] = wit
    Ns = gen_reduced(maxe, maxl)
    print(f"# reduced sequences, entries<={maxe}, Lng<={maxl}: {len(Ns)}")
    for N in Ns:
        try: check(N, report)
        except RecursionError:
            print("RECURSION", fmt(N)); continue
    if nrand:
        rnd = random.Random(12345)
        cnt = 0
        while cnt < nrand:
            L = rnd.randint(2, 9)
            N = [(rnd.randint(0,20), rnd.randint(0,20)) for _ in range(L)]
            if not reduced(N): continue
            cnt += 1
            try: check(N, report)
            except RecursionError: pass
        print(f"# + {nrand} random reduced samples (Lng<=9, entries<=20)")
    print("=== NON-VACUOUS counts (exercises / failures) ===")
    for k in sorted(stats):
        t,f = stats[k]
        print(f"  {k:7s}: {t:8d} exercises, {f:6d} failures" + (f"   e.g. {cex[k]}" if f else ""))

if __name__ == '__main__':
    main()
