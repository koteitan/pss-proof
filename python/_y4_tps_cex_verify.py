"""r81-Y4: VERIFY the counterexample that refutes the T_PS form of the Sec 7.4 corollary.

M = (0,0)(4,2)(2,6)(4,2)(8,4)(6,4)  --  in T_PS, NOT reduced.
Claim: with j0 the unique nextAdm-successor of 0 towards Lng M - 1, and j = 0 (also j = 2),
       (M,j) in Marked   [correction A18's hypothesis]
       leR M 0 j j0      [the corollary's own hypothesis]
   but NO (s0,b0) decomposes BOTH  Mark (Pred M) j  with core Mark (Pred M) j0
                              AND  Mark M j        with core Mark M j0.
A counterexample only needs to be CHECKED, not sampled.  This is the check.
"""
import sys
sys.setrecursionlimit(20000)
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-y4/python')
import _y4_fastcache      # noqa: F401
import _y4_fastcache2     # noqa: F401
import red_model as rm
import trans_model as tm
from red_model import Lng, fmt

M = [(0, 0), (4, 2), (2, 6), (4, 2), (8, 4), (6, 4)]
j1 = Lng(M) - 1

print("M            =", fmt(M))
print("M in T_PS    =", M[0] == (0, 0))
print("reduced M    =", tm.reduced(M), "  (must be False for this to be a T_PS-only cex)")
print("Red M        =", fmt(rm.Red(M)))
print("Red(Red M)   =", fmt(rm.Red(rm.Red(M))))
print("Lng M - 1    =", j1)

j0s = [j for j in range(Lng(M)) if rm.nextAdm(M, 0, j, j1)] if hasattr(rm, 'nextAdm') else None
if j0s is None:
    def nextAdm(M, i, j0, j1):
        if not (rm.leR(M, i, j0, j1) and j0 < j1 and tm.adm(M, j0)):
            return False
        return all(not rm.leR(M, i, j, j1) or not tm.adm(M, j)
                   for j in range(j0 + 1, j1))
    j0s = [j for j in range(Lng(M)) if nextAdm(M, 0, j, j1)]
print("j0 with nextAdm M 0 j0 (Lng M - 1) :", j0s)
assert len(j0s) == 1, j0s
j0 = j0s[0]

P = tm.Pred(M)
print("Pred M       =", fmt(P))
print()

fail = 0
for j in range(Lng(M)):
    admj = tm.adm(M, j)
    marked = admj and rm.leR(M, 0, j, j1)          # (M,j) in Marked  -- A18's hypothesis
    anc = rm.leR(M, 0, j, j0)                      # the corollary's hypothesis
    if not (marked and anc and j <= j0):
        continue
    mj, mj0 = tm.Mark(M, j), tm.Mark(M, j0)
    pj, pj0 = tm.Mark(P, j), tm.Mark(P, j0)
    DM = set((tuple(s), tuple(b)) for s, b in tm.scb_decomps(mj, tm.flatBT(mj0)))
    DP = set((tuple(s), tuple(b)) for s, b in tm.scb_decomps(pj, tm.flatBT(pj0)))
    common = DM & DP
    print(f"j={j}  adm={admj}  (M,j):Marked={marked}  leR M 0 j j0={anc}")
    print(f"   Mark M j      == Mark (Pred M) j      ? {mj == pj}")
    print(f"   Mark M j0     == Mark (Pred M) j0     ? {mj0 == pj0}   <-- cores COINCIDE")
    print(f"   # scb decomps of Mark (Pred M) j with core Mark (Pred M) j0 : {len(DP)}")
    print(f"   # scb decomps of Mark M j        with core Mark M j0        : {len(DM)}")
    print(f"   # COMMON (s0,b0)                                            : {len(common)}")
    if len(common) == 0:
        fail += 1
        print("   ==> the T_PS form of the Sec 7.4 corollary is FALSE here")
    print()

print("j0 =", j0)
print("columns j <= j0 satisfying BOTH (M,j):Marked AND leR M 0 j j0, "
      f"with NO common (s0,b0): {fail}")
print("VERDICT:", "T_PS form REFUTED" if fail else "no counterexample found (!)")
