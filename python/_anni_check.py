#!/usr/bin/env python3
"""Empirically model the §8.6/8.7 [0]-annihilation lemmas.
[0] operation = bracket(a, ZERO) since numBT 0 = [] = ZERO."""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/python')
from buchholz import (ZERO, D, one, nat, is_zero, add, mul, lt_term, le_term,
                      in_OT, in_TB, dom, bracket, fmt)

def zero_op(a):           # the [0] step
    return bracket(a, ZERO)

def iter0(a, k):
    for _ in range(k):
        a = zero_op(a)
    return a

# ---------- LEMMA 1 model ----------
# Claim: for principal c = D_u(t' + D_v 0), there is k with 0<k<=v+1 and
#        c[0]^k = D_u t'   (as the marked principal of an scb-decomposition;
#        at the principal level the transformation is exactly on the principal).
# Article: ((D_u(t'+D_v 0))[0] strips trailing D_v 0 toward D_u t' in <= v+1 steps.
# Test on the *principal* level (s,b empty): c[0]^k should reach D_u t'.

def principal(u, t):
    return [D(u, t)]

def test_lemma1(maxu=3, maxv=3):
    fails = []
    tested = 0
    # t' ranges over a set of small OT_B terms
    tprimes = []
    tprimes.append(ZERO)                       # 0
    for a in range(3):
        tprimes.append([D(a, ZERO)])           # D_a 0
    for a in range(3):
        tprimes.append([D(a, ZERO), D(0, ZERO)])  # D_a 0 + D_0 0 (descending? need a>=0)
    for a in range(2):
      for bb in range(2):
        tprimes.append([D(a,[D(bb,ZERO)])])    # D_a(D_b 0)
    for u in range(maxu+1):
        for v in range(maxv+1):
            for tp in tprimes:
                # c = D_u(t' + D_v 0)
                inner = add(tp, [D(v, ZERO)])
                c = principal(u, inner)
                target = principal(u, tp)
                # require c in T_B (always, no omega) and ideally OT but article
                # only needs t in OT_B for the OUTER lemma; lemma1 is about T_B.
                tested += 1
                found = None
                cur = c
                for k in range(1, v+2):        # k in 1..v+1
                    cur = zero_op(cur)
                    if cur == target:
                        found = k
                        break
                if found is None:
                    fails.append(('lem1', u, v, fmt(tp), fmt(c), fmt(target),
                                  [fmt(iter0(c,kk)) for kk in range(v+2)]))
    return tested, fails

t, f = test_lemma1()
print(f"LEMMA1: tested {t}, fails {len(f)}")
for x in f[:20]:
    print("  FAIL", x)
