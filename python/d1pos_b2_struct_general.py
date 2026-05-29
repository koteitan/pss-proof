#!/usr/bin/env python3
"""Are (S-adj) and (S-sgl) GENERAL facts about P, or do they need monoT/standard context?

(S-adj): consecutive P-components J-1,J of Q with equal row-0 head are M-adjacent (pR=pL+1).
(S-sgl): the LEFT one (J-1) is a singleton (Lng=1).

Test over ARBITRARY sequences Q (all pairseqs len<=5/val<=2), and separately over
monoT Q only, to locate the minimal hypothesis.  Also test the consequence for the
adjacency reduction: if components J-1,J have equal row-0 head, is component J-1 a
SINGLE row-0-left-min cell whose successor opens component J?
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import Lng, entry, P, monoT, zeroT, multiT

def gen_seqs(maxlen, maxval):
    cellset=[(a,b) for a in range(maxval+1) for b in range(maxval+1)]
    for L in range(1, maxlen+1):
        for cells in itertools.product(cellset, repeat=L):
            yield list(cells)

def offs(comps):
    o=[0]
    for c in comps: o.append(o[-1]+Lng(c))
    return o

def run(filt, label):
    tie=adj_fail=sgl_fail=0
    ex_adj=ex_sgl=None
    for Q in gen_seqs(5,2):
        if not filt(Q): continue
        comps=P(Q)
        if len(comps)<2: continue
        o=offs(comps)
        for J in range(1,len(comps)):
            cL,cR=comps[J-1],comps[J]
            if entry(cR,0,0)!=entry(cL,0,0): continue
            tie+=1
            if o[J]!=o[J-1]+1:
                adj_fail+=1
                if ex_adj is None: ex_adj=(Q,J,o)
            if Lng(cL)!=1:
                sgl_fail+=1
                if ex_sgl is None: ex_sgl=(Q,J,Lng(cL))
    print(f"[{label}] tie pairs={tie}  (S-adj) fail={adj_fail}  (S-sgl) fail={sgl_fail}")
    if ex_adj: print(f"   adj counterexample: Q={ex_adj[0]} J={ex_adj[1]} offs={ex_adj[2]}")
    if ex_sgl: print(f"   sgl counterexample: Q={ex_sgl[0]} J={ex_sgl[1]} leftLng={ex_sgl[2]}")

if __name__=='__main__':
    run(lambda Q: True, "ALL seqs len<=5/val<=2")
    run(lambda Q: monoT(Q), "monoT Q only")
    run(lambda Q: not multiT(Q), "non-multiT Q")
