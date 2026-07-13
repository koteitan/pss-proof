"""Probe: how much of the Marked hypothesis does the Mark-nesting engine actually need?

Claim under test (on REDUCED M):  for j <= j0 < Lng M - 1 (plain nat order),
  EX! (s,b). scb_decomp (Mark (Pred M) j) s (flatBT (Mark (Pred M) j0)) b
          /\ scb_decomp (Mark M j)        s (flatBT (Mark M j0))        b
with various hypothesis subsets.
"""
import sys, itertools
sys.setrecursionlimit(10000)
from red_model import Lng, leR, adm, Pred, reduced, Red, fmt
from trans_model import Mark, flatBT, scb_decomps

def marked(M,m): return adm(M,m) and leR(M,0,m,Lng(M)-1)

def joint(M,j,j0):
    da = set((tuple(s),tuple(b)) for s,b in scb_decomps(Mark(Pred(M),j), flatBT(Mark(Pred(M),j0))))
    db = set((tuple(s),tuple(b)) for s,b in scb_decomps(Mark(M,j), flatBT(Mark(M,j0))))
    return da & db

def run(maxent, maxlng, only_reduced=True):
    stats = {}
    pairs=[(a,b) for a in range(maxent) for b in range(maxent)]
    for L in range(1,maxlng+1):
        for M in itertools.product(pairs,repeat=L):
            M=list(M)
            if only_reduced and not reduced(M): continue
            n=Lng(M)
            for j0 in range(n-1):
                for j in range(j0+1):
                    try: ok = (len(joint(M,j,j0))==1)
                    except RecursionError: continue
                    # hypothesis classes
                    hj  = marked(M,j); h0 = marked(M,j0); hle = leR(M,0,j,j0)
                    key=(hj,h0,hle)
                    a,b = stats.get(key,(0,0))
                    stats[key]=(a+1, b + (0 if ok else 1))
                    if not ok and key==(True,True,True):
                        pass
    print(f"REDUCED-only={only_reduced} entries<{maxent} Lng<={maxlng}")
    for k in sorted(stats):
        tot,fail=stats[k]
        print(f"  markedj={k[0]} markedj0={k[1]} leR={k[2]}: {tot} exercises, {fail} failures")

if __name__=="__main__":
    run(int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]=="R" if len(sys.argv)>3 else True)
