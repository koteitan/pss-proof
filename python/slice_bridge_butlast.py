import sys, itertools
sys.path.insert(0, '/home/koteitan/pss-slice/python')
from red_model import (Lng, entry, seg, oper, P, Br, TrMax, FirstNodes,
                       is_standard, parent, idx1, le0, leR, monoT, multiT, zeroT,
                       Pcut, hasParent)
def all_pairseqs(maxlen, maxval):
    for L in range(1, maxlen+1):
        cells = list(itertools.product(range(maxval+1), repeat=2))
        for tup in itertools.product(cells, repeat=L):
            yield list(tup)
MAXLEN=int(sys.argv[1]); MAXVAL=int(sys.argv[2])

# Hypotheses to test for the butlast bridge on seg N a b with b=LN-1.
# We test the bridge over ALL standard N and ALL valid (a,b) windows that are
# in the case-A regime, and report which hypothesis set is necessary/sufficient.
total=0
# counters keyed by hypothesis profile
prof={}
fails_pcut={}
def rec(d,k):
    d[k]=d.get(k,0)+1

for N in all_pairseqs(MAXLEN, MAXVAL):
    if not is_standard(N): continue
    LN=Lng(N)
    if LN<3: continue
    b=LN-1
    # case-A regime conditions on N at index b (from the decomp scripts):
    # entry(N,1,b)==0, idx1(N,b)==0, hasParent at (0,b), parent < b
    if entry(N,1,b)!=0: continue
    if idx1(N,b)!=0: continue
    if not hasParent(N,0,b): continue
    j0N=parent(N,0,b)
    if not (j0N<b): continue
    # window: a < b. seg N a b must be a monomial (mono) segment for the regime.
    for a in range(0,b):
        S=seg(N,a,b)
        Sm=seg(N,a,b-1)
        if Lng(S)<2: continue
        lhs=P(Sm)
        rhs=P(S)[:-1]  # butlast
        ok = (lhs==rhs)
        # characterize
        prc = Pcut(S) if multiT(S) else None
        prof_key=(monoT(S), multiT(S), (prc==(b-a)) if prc is not None else None, ok)
        total+=1
        rec(prof,prof_key)
        # specifically test: does monoT(S) imply Pcut(S)==b-a and ok?
        if monoT(S):
            rec(fails_pcut,("monoT", ok, "pcut_eq_b-a", (prc==b-a) if prc is not None else "noPcut(monoseg)"))
        if multiT(S):
            rec(fails_pcut,("multiT", ok, "pcut_eq_b-a", prc==(b-a)))

print("total windows",total)
print("--- profile (monoT,multiT,pcut==b-a,ok) ---")
for k in sorted(prof,key=str): print(" ",k,prof[k])
print("--- by type ---")
for k in sorted(fails_pcut,key=str): print(" ",k,fails_pcut[k])
