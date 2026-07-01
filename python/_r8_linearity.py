import sys, itertools
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import Lng, nextrel0, reach

"""ROUND 8 -- is le0 "ancestor-linear": common ancestors of the same target
are themselves le0-comparable?  I.e. le0 M a c /\\ le0 M b c ==> le0 M a b \\/
le0 M b a.  If true in general this would give a route to `nocut` in
m_8_5_Pcut_of_le0_cut (a witness j<Pcut N and Pcut N both reaching a common
descendant par0 would force j to reach Pcut N, contradicting Pcut's own
minimality).  Uses the reach() matrix directly (computed ONCE per M) instead
of the (much slower) `le0` wrapper recomputing reach() per query."""

def gen(maxlen=6, maxv=2):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]
    for L in range(1,maxlen+1):
        for s in itertools.product(pairs, repeat=L):
            yield list(s)

def main(maxlen=6, maxv=2):
    total=0; fails=[]
    for M in gen(maxlen,maxv):
        n=Lng(M)
        if n<2: continue
        R = reach(M, nextrel0)
        for c in range(n):
            anc = [x for x in range(c+1) if R[x][c]]
            for a in anc:
                for b in anc:
                    if a==b: continue
                    total+=1
                    if not (R[a][b] or R[b][a]):
                        fails.append((tuple(M),a,b,c))
    print('common-ancestor pairs tested:',total,'linearity failures:',len(fails))
    for f in fails[:10]: print(' ',f)

if __name__=='__main__':
    main(6,2)
