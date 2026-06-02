#!/usr/bin/env python3
"""H3 empirical: branch-5 re-basing map preserves leR on the suffix.

For N (monoT standard, plus general T_PS), m10 with m10 <= jN = Lng N - 1,
RM = map (lambda p. (fst p - entry N 0 m10 + entry N 1 m10, snd p)) (seg N m10 (Lng N-1)).
Check:  leR RM i a b  ==  leR N i (a+m10) (b+m10)   for a,b < Lng N - m10, i in {0,1}.
Report TRUE/FALSE counts and counterexamples.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import Lng, entry, seg, leR, monoT, fmt
from d1pos_j0j1red_search import gen_std

def rebase(N, m10):
    e0 = entry(N,0,m10); e1 = entry(N,1,m10)
    S = seg(N, m10, Lng(N)-1)
    return [ (p[0]-e0+e1, p[1]) for p in S ]

def check(Ms, label, restrict_mono):
    T=F=0; cex=[]
    for N in Ms:
        ln=Lng(N)
        if restrict_mono and not monoT(N): continue
        for m10 in range(0, ln):            # m10 <= jN = ln-1
            RM = rebase(N, m10)
            w = ln - m10                     # Lng RM = w
            for i in (0,1):
                for a in range(w):
                    for b in range(w):
                        lhs = leR(RM, i, a, b)
                        rhs = leR(N, i, a+m10, b+m10)
                        if lhs==rhs: T+=1
                        else:
                            F+=1
                            if len(cex)<8:
                                cex.append((fmt(N),m10,i,a,b,lhs,rhs,
                                            entry(N,0,m10),entry(N,1,m10)))
    print(f"[{label}] TRUE={T} FALSE={F}")
    for c in cex:
        print("  CEX N=%s m10=%d i=%d a=%d b=%d lhs=%s rhs=%s e0=%d e1=%d"%c)
    return T,F

if __name__=="__main__":
    maxlen,maxval,KMAX=(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])) if len(sys.argv)>3 else (12,6,6)
    Ms=gen_std(maxlen,maxval,KMAX)
    print(f"generated {len(Ms)} standard terms (maxlen={maxlen} maxval={maxval} KMAX={KMAX})")
    check(Ms, "all T_PS standard", False)
    check(Ms, "monoT standard only", True)
