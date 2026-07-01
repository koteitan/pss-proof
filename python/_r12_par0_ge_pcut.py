import sys, itertools, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import Lng,entry,multiT,hasParent,parent,Pcut,le0

"""ROUND 12, Route 2: candidate FULLY GENERAL mechanism (no oper/condV/deepen-
block content at all) for the non-reset witness `entry N 0 (Pcut N) < fst
col`.  If Ncur=N@[col] has a row-0 parent par0=parent(Ncur,0,Lng(Ncur)-1)
(i.e. hasParent(Ncur,0,last)), CONJECTURE: Pcut(N) <= par0 ALWAYS (Pcut being
the smallest le0-connector to N's own last index, and par0 -- by its own
"everything strictly between is >= fst(col)" defining clause -- should also
connect back to N's own last index, so minimality forces Pcut(N)<=par0).  If
this holds broadly, then entry(N,0,Pcut N) <= entry(N,0,par0) < fst(col)
[the last step trivial: par0 is IN the set {j<last: entry(Ncur,0,j)<fst(col)}
by its own construction] closes the witness WITHOUT ANY reset/non-reset case
split or deepen-block-specific reasoning.

Test broadly, NO regime filter (just N multiT with hasParent(N@[col],0,last),
fst(col)>0 to separate from the already-closed reset case)."""

import itertools as it

def gen(maxlen=6, maxv=3):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]
    for L in range(2,maxlen+1):
        for s in it.product(pairs, repeat=L):
            yield list(s)

def main(timelimit=120, maxlen=6, maxv=3):
    t0=time.time(); tested=0; ok=0; bad=[]
    for N in gen(maxlen,maxv):
        if time.time()-t0>timelimit: break
        if not multiT(N): continue
        try:
            pc = Pcut(N)
        except Exception:
            continue
        for col in [(a,b) for a in range(maxv+2) for b in range(maxv+2)]:
            if col[0]==0: continue   # separate (already-closed) reset case
            Ncur = N+[col]
            last = Lng(Ncur)-1
            if not hasParent(Ncur,0,last): continue
            par0 = parent(Ncur,0,last)
            tested += 1
            good = (pc <= par0)
            if good: ok += 1
            else: bad.append((tuple(N),col,pc,par0))
    return tested, ok, bad

if __name__=='__main__':
    tl = int(sys.argv[1]) if len(sys.argv)>1 else 120
    tested, ok, bad = main(tl, 6, 3)
    print(f"tested={tested}, Pcut(N)<=par0: {ok}/{tested} ({100.0*ok/max(1,tested):.2f}%)")
    for b in bad[:15]:
        print("  BAD:", b)
