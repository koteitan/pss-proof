"""r81-Y4: WIDE census of the FREE nesting engine (y4b_Mark_nest_free / y4c_..._ex1).

CLAIM (no hypothesis on either column at all):
    N in RT_PS,  j <= j0   ==>   EX! (s,b). scb_decomp (Mark N j) s (flatBT (Mark N j0)) b

No adm, no Marked, no le0-ancestry, and NO RANGE CONDITION on j0 -- so we probe j0
BEYOND Lng N - 1 as well (the theorem quantifies over all j0, and Mark N k is total).
Existence AND uniqueness are both checked.  BOUNDS PRINTED, counts NON-VACUOUS.
"""
import sys
sys.setrecursionlimit(30000)
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-y4/python')
import _y4_fastcache      # noqa: F401
import _y4_fastcache2     # noqa: F401
import trans_model as tm
from red_model import Lng, fmt
from _y4_joint_wide import gen_reduced, rand_reduced

Mark, flatBT, scb_decomps = tm.Mark, tm.flatBT, tm.scb_decomps


def run(Ns, label, over=3):
    tot = 0
    n_noexist = n_multi = 0
    n_oor = 0          # exercises with j0 out of range (j0 >= Lng N)
    n_zero = 0         # Mark N j = 0_B
    cex = []
    for N in Ns:
        N = list(N)
        n = Lng(N)
        hi = n + over            # probe j0 past the last column
        for j0 in range(hi):
            for j in range(j0 + 1):
                try:
                    mj, mj0 = Mark(N, j), Mark(N, j0)
                except (RecursionError, AssertionError, IndexError, ValueError):
                    continue
                tot += 1
                if j0 >= n:
                    n_oor += 1
                if mj == tm.ZB:
                    n_zero += 1
                d = scb_decomps(mj, flatBT(mj0))
                if len(d) == 0:
                    n_noexist += 1
                    if len(cex) < 6:
                        cex.append(('NO-DECOMP', fmt(N), j, j0))
                elif len(d) > 1:
                    n_multi += 1
                    if len(cex) < 6:
                        cex.append(('NON-UNIQUE', fmt(N), j, j0, len(d)))
    print(f"[{label}]")
    print(f"  NON-VACUOUS exercises (N reduced, j <= j0 < Lng N + {over}): {tot}")
    print(f"     of which j0 is OUT OF RANGE (j0 >= Lng N): {n_oor}")
    print(f"     of which Mark N j = 0_B                  : {n_zero}")
    print(f"  EXISTENCE  failures (no scb decomposition) : {n_noexist}")
    print(f"  UNIQUENESS failures (more than one (s,b))  : {n_multi}")
    print(f"  VERDICT: {'y4b + y4c CONFIRMED' if n_noexist == n_multi == 0 else 'REFUTED'}")
    for c in cex:
        print("   CEX", c)
    sys.stdout.flush()


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'full':
        e, l = int(sys.argv[2]), int(sys.argv[3])
        Ns = gen_reduced(e, l)
        print(f"# EXHAUSTIVE: all reduced N, entries<={e}, 1<=Lng<={l}: {len(Ns)}",
              flush=True)
        run(Ns, f"EXHAUSTIVE  entries<={e}  Lng<={l}")
    else:
        e, l, n = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        Ns = rand_reduced(e, l, n)
        print(f"# RANDOM (reduced-tree walk): entries<={e}, 2<=Lng<={l}: {len(Ns)}",
              flush=True)
        run(Ns, f"RANDOM  entries<={e}  Lng<={l}  n={len(Ns)}")
