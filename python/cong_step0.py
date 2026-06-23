#!/usr/bin/env python3
"""STEP 0: empirically pin the exact hypotheses for the Red congruence.

Conjecture (red_cong_conj):
  nextrel0 A == nextrel0 X  and  nextrel1 A == nextrel1 X  and  Lng A == Lng X
    ==>  Red A == Red X

We generate X from A by random order-preserving relabelings of each row, and
check whether equal nextrel0/nextrel1 forces equal Red.  If it fails, we hunt
for the minimal extra hypothesis (le0/le1 eq, entry _ _ 0 eq, monoT/multiT eq).
"""
import sys, os, random, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, nextrel0, nextrel1, le0, le1, Red,
                       zeroT, monoT, multiT, TrMax)

def nextrel0_map(M):
    n=Lng(M)
    return {(a,b):nextrel0(M,a,b) for a in range(n) for b in range(n)}
def nextrel1_map(M):
    n=Lng(M)
    return {(a,b):nextrel1(M,a,b) for a in range(n) for b in range(n)}
def le0_map(M):
    n=Lng(M)
    return {(a,b):le0(M,a,b) for a in range(n) for b in range(n)}
def le1_map(M):
    n=Lng(M)
    return {(a,b):le1(M,a,b) for a in range(n) for b in range(n)}
def row(M,i): return tuple(entry(M,i,j) for j in range(Lng(M)))
def entry0_0(M): return entry(M,0,0)
def entry1_0(M): return entry(M,1,0)

def order_preserving_relabel(vals, maxval):
    """Return a new tuple with the same strict order structure (a<b, a==b, a>b
    all preserved) but possibly different actual values."""
    # distinct sorted values
    uniq = sorted(set(vals))
    # assign new strictly-increasing values, randomly spaced
    newvals = []
    cur = random.randint(0, 2)
    for _ in uniq:
        newvals.append(cur)
        cur += random.randint(1, 3)
    mapping = dict(zip(uniq, newvals))
    return tuple(mapping[v] for v in vals)

def relabel_seq(A):
    r0 = order_preserving_relabel(row(A,0), None)
    r1 = order_preserving_relabel(row(A,1), None)
    return [(r0[j], r1[j]) for j in range(Lng(A))]

def gen_random_seq(maxlen, maxval):
    n = random.randint(1, maxlen)
    return [(random.randint(0,maxval), random.randint(0,maxval)) for _ in range(n)]

def test(trials=200000, maxlen=4, maxval=3, relabels=4):
    fails = []
    fails_with_le = []
    fails_with_le_e0 = []
    fails_with_le_e0e1 = []
    checked = 0
    for _ in range(trials):
        A = gen_random_seq(maxlen, maxval)
        try:
            RA = Red(A)
        except Exception:
            continue
        for _ in range(relabels):
            X = relabel_seq(A)
            if X == A:
                continue
            # base hypothesis
            if nextrel0_map(A)!=nextrel0_map(X): continue
            if nextrel1_map(A)!=nextrel1_map(X): continue
            if Lng(A)!=Lng(X): continue
            checked += 1
            try:
                RX = Red(X)
            except Exception:
                continue
            if RA != RX:
                rec = (A, X, RA, RX)
                fails.append(rec)
                le_eq = (le0_map(A)==le0_map(X) and le1_map(A)==le1_map(X))
                if le_eq:
                    fails_with_le.append(rec)
                    e0_eq = (entry0_0(A)==entry0_0(X))
                    e1_eq = (entry1_0(A)==entry1_0(X))
                    if e0_eq:
                        fails_with_le_e0.append(rec)
                        if e1_eq:
                            fails_with_le_e0e1.append(rec)
    print(f"checked pairs (nextrel0/1+Lng eq): {checked}")
    print(f"FAILS (base hyp only): {len(fails)}")
    print(f"FAILS also with le0/le1 eq: {len(fails_with_le)}")
    print(f"FAILS also with le0/le1 + entry00 eq: {len(fails_with_le_e0)}")
    print(f"FAILS also with le0/le1 + entry00 + entry10 eq: {len(fails_with_le_e0e1)}")
    return fails, fails_with_le, fails_with_le_e0, fails_with_le_e0e1

if __name__=="__main__":
    random.seed(12345)
    fails, fwl, fwle0, fwle0e1 = test()
    def show(lst, name, k=5):
        print(f"\n--- sample {name} ---")
        for (A,X,RA,RX) in lst[:k]:
            print("A=",A,"-> RedA=",RA)
            print("X=",X,"-> RedX=",RX)
            print("  zeroT/monoT/multiT A:",zeroT(A),monoT(A),multiT(A),
                  " X:",zeroT(X),monoT(X),multiT(X), " TrMax A/X:",TrMax(A),TrMax(X))
            print()
    if fails: show(fails,"base-only fails")
    if fwl: show(fwl,"le-eq fails")
    if fwle0: show(fwle0,"le+e0 fails")
    if fwle0e1: show(fwle0e1,"le+e0+e1 fails")
