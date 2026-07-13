"""Hunt + INDEPENDENTLY VERIFY counterexamples to the T_PS 7.4 target.

Verification uses the ORIGINAL red_model / trans_model functions (no local
re-implementation of adm/le0/nextAdm), i.e. a fresh interpreter without the
_y6_fast monkey-patches would give the same answer.
"""
import sys, random
sys.setrecursionlimit(100000)
import _y6_census as C
import _y6_fast as F
import red_model as rm
import trans_model as tm

def nextAdm0_orig(M, j0, j1):
    return rm.leR(M,0,j0,j1) and j0 < j1 and tm.adm(M,j0) and \
        all((not rm.leR(M,0,j,j1)) or (not tm.adm(M,j)) for j in range(j0+1, j1))

def marked_orig(M, m):
    return tm.adm(M, m) and rm.leR(M, 0, m, rm.Lng(M)-1)

def verify(M, j, j0):
    """re-check the hypotheses and the conclusion with the ORIGINAL model funcs"""
    j1 = rm.Lng(M)-1
    ps = [k for k in range(j1) if nextAdm0_orig(M,k,j1)]
    hyp = (len(ps) == 1 and ps[0] == j0 and marked_orig(M,j) and rm.leR(M,0,j,j0))
    A = tm.Mark(tm.Pred(M), j);  Ac = tm.flatBT(tm.Mark(tm.Pred(M), j0))
    B = tm.Mark(M, j);           Bc = tm.flatBT(tm.Mark(M, j0))
    da = set((tuple(s),tuple(b)) for s,b in tm.scb_decomps(A, Ac))
    db = set((tuple(s),tuple(b)) for s,b in tm.scb_decomps(B, Bc))
    return hyp, len(da), len(db), len(da & db), A, Ac, B, Bc

def main(maxent, maxlng, N, seed, want):
    random.seed(seed)
    found = 0
    for i in range(N):
        L = random.randint(2, maxlng)
        M = [(random.randint(0,maxent), random.randint(0,maxent)) for _ in range(L)]
        a = C.analyse(M)
        if a is None: continue
        j0, js = a
        for j in js:
            try: d = C.joint(M, j, j0)
            except Exception: continue
            if len(d) != 1:
                hyp, na, nb, nc, A, Ac, B, Bc = verify(M, j, j0)
                red = F.reduced(M)
                print(f"CEX {F.fmt(M)}  j={j} j0={j0}  reduced={red}  "
                      f"hyp_recheck={hyp}  #Pred-side={na} #M-side={nb} #common={nc}")
                print(f"    R2 = {F.fmt(F.Red(F.Red(M)))}")
                print(f"    Mark(Pred M,j)  = {A}")
                print(f"    Mark(Pred M,j0) = {tm.Mark(tm.Pred(M), j0)}")
                print(f"    Mark(M,j)       = {B}")
                print(f"    Mark(M,j0)      = {tm.Mark(M, j0)}", flush=True)
                found += 1
                if found >= want: return
        if len(F._mark) > 200000: F.cache_clear()
    print("done, found", found)

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]))
