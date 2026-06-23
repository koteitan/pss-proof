#!/usr/bin/env python3
"""Empirical check: in a reduced sequence row0 dominates row1 pointwise.
   p_6_6_reduced_coeff: M in RT_PS, j<Lng M ==> entry M 0 j >= entry M 1 j.
Also tests whether RedCondA & RedCondB (the keystone RHS) suffice on their own,
to gauge whether reduced_coeff needs the full keystone or is more elementary."""
import sys, itertools
sys.path.insert(0, __import__('os').path.dirname(__file__))
from red_model import Lng, entry, reduced, hasParent, parent, nextR

def RedCondA(M):
    for i in (0,1):
        for j in range(Lng(M)):
            if hasParent(M,i,j):
                if entry(M,i,parent(M,i,j))+1 != entry(M,i,j): return False
    return True
def RedCondB(M):
    for j in range(Lng(M)):
        if (not hasParent(M,0,j)) and j<=Lng(M)-1:
            if entry(M,0,j) != entry(M,1,j): return False
    return True

def coeff_ok(M):
    return all(entry(M,0,j) >= entry(M,1,j) for j in range(Lng(M)))

def enum(maxlen, val):
    for n in range(1, maxlen+1):
        cells = [(a,b) for a in range(val+1) for b in range(val+1)]
        for M in itertools.product(cells, repeat=n):
            yield list(M)

def main():
    maxlen, val = 4, 3
    tot=red=fail_coeff=condfail_coeff=0
    ex=[]
    for M in enum(maxlen, val):
        tot+=1
        if not reduced(M): continue
        red+=1
        if not coeff_ok(M):
            fail_coeff+=1
            if len(ex)<5: ex.append(("REDUCED but coeff FAIL", M))
        # independent angle: does CondA&CondB alone imply coeff?
        if RedCondA(M) and RedCondB(M) and not coeff_ok(M):
            condfail_coeff+=1
    print(f"maxlen={maxlen} val={val}: total={tot} reduced={red}")
    print(f"  reduced & coeff-FAIL: {fail_coeff}")
    print(f"  (CondA&CondB) & coeff-FAIL: {condfail_coeff}")
    for tag,M in ex: print("   ", tag, M)

if __name__=='__main__':
    main()
