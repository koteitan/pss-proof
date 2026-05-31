import sys, itertools
sys.path.insert(0, '/home/koteitan/pss-slice/python')
from red_model import (Lng, seg, P, multiT, zeroT, monoT, Pcut)
def all_pairseqs(maxlen, maxval):
    for L in range(1, maxlen+1):
        cells = list(itertools.product(range(maxval+1), repeat=2))
        for tup in itertools.product(cells, repeat=L):
            yield list(tup)
MAXLEN=int(sys.argv[1]); MAXVAL=int(sys.argv[2])
# PURE claim: if multiT S and Lng S>1 and Pcut S = Lng S - 1
#   then  P (take (Lng S - 1) S) = butlast (P S)
total=0; fail=0; applies=0
# also test WITHOUT the Pcut hypothesis, just multiT, to confirm it's needed
mtotal=0; mfail=0
for S in all_pairseqs(MAXLEN, MAXVAL):
    L=Lng(S)
    if L<2: continue
    if not multiT(S): continue
    total+=1
    pc=Pcut(S)
    lhs=P(S[:L-1])
    rhs=P(S)[:-1]
    if pc==L-1:
        applies+=1
        if lhs!=rhs:
            fail+=1
            if fail<=5: print("FAIL(pcut=L-1)",S,"pc",pc,"lhs",lhs,"rhs",rhs)
    else:
        mtotal+=1
        if lhs!=rhs:
            mfail+=1
print("multiT total",total,"  pcut=L-1 applies",applies,"fail",fail)
print("  (sanity) multiT with pcut!=L-1:",mtotal,"of which lhs!=rhs:",mfail)
