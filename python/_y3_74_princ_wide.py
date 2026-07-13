"""r80-Y3: WIDE census of the unconditional-principality brick.

  BRICK (P):  N reduced  ==>  Mark N k = 0B  \/  (EX p. Mark N k = Trm [p] /\ dfree)
              i.e. Mark N k is principal-or-zero for EVERY column k --- no adm,
              no Marked, no ancestry hypothesis at all.

Bounds: full enumeration of reduced N at entries <= MAXE, Lng <= MAXL, every
k in 0..Lng N + 1 (so out-of-range columns are exercised too), plus random
reduced samples at larger entries/lengths.
"""
import sys, random
sys.setrecursionlimit(10000)
from red_model import Lng, fmt
from trans_model import Mark, flatBT, reduced, isPTB_str, ZB

def gen_reduced(maxe, maxl):
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

def princ(t): return t == ZB or isPTB_str(flatBT(t))

def main():
    maxe, maxl, nrand = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    tot = fail = zeros = 0
    Ns = gen_reduced(maxe, maxl)
    print(f"# reduced N (entries<={maxe}, Lng<={maxl}): {len(Ns)}", flush=True)
    for N in Ns:
        for k in range(Lng(N) + 2):
            tot += 1
            t = Mark(N, k)
            if t == ZB: zeros += 1
            if not princ(t):
                fail += 1
                if fail < 5: print("FAIL", fmt(N), k, flatBT(t), flush=True)
    print(f"[FULL entries<={maxe} Lng<={maxl}] {tot} exercises (all NON-VACUOUS: "
          f"no hypothesis), {fail} failures, {zeros} of them = 0B", flush=True)
    if nrand:
        r = random.Random(2026); c = t2 = f2 = 0
        while c < nrand:
            L = r.randint(1, 9)
            N = [(r.randint(0,20), r.randint(0,20)) for _ in range(L)]
            if not reduced(N): continue
            c += 1
            for k in range(Lng(N) + 2):
                t2 += 1
                try:
                    if not princ(Mark(N,k)):
                        f2 += 1
                        if f2 < 5: print("RFAIL", fmt(N), k, flush=True)
                except RecursionError: pass
        print(f"[RANDOM {nrand} reduced N, Lng<=9, entries<=20] {t2} exercises, "
              f"{f2} failures", flush=True)

main()
