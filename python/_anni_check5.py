#!/usr/bin/env python3
"""KEY: relate t[0] to c[0] when (s,c,b) is a RIGHT-SPINE scb-decomp of t.
Build t by nesting c at the right spine under some s-context, compute t[0],
read back its right-spine principal c', and check c' = c[0]'s principal.
The article claims t[0]'s decomp principal is determined by c via fundseq.
We model: t = D_w1(D_w2(...(c)...))  (right-spine nesting, b=())  and also
with multi-term left context.  Then t[0] should = D_w1(...(c[0])...) when the
recursion descends to c (i.e. dom is governed by c at every level)."""
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/python')
from buchholz import (ZERO, D, one, nat, is_zero, add, mul, lt_term, le_term,
                      in_OT, in_TB, dom, bracket, fmt)

def zero_op(a):
    return bracket(a, ZERO)

# A right-spine occurrence: t's flat string = s @ flat(c) @ b with b all ')'.
# Simplest family: t = D_{w_1}(... D_{w_m}(c) ...), a chain of single principals
# wrapping c.  Here s = "D_{w_1}...D_{w_m}", b = "))...)" (m closing parens)?
# Actually nesting D_w(x) flat = "D_w" + flat(x); no closing paren for single principal.
# So b=() for pure single-principal nesting.  c sits at the deepest right spine.
# t[0]: outer D_{w_1}(body), body=D_{w2}(...) single principal !=0.
#   dom(t)=dom(body)=...=dom(c).  Recursion (iii) if u>w at each level OR may hit
#   xseq/(i).  We just want: is t[0]'s deepest principal = c[0]?  i.e. does [0]
#   commute past the wrapping single principals?
print("=== single-principal wrapping: t = D_w(c); compare t[0] vs D_w(c[0]) ===")
mism=0; tot=0
import itertools
cands = []
for u in range(3):
    for v in range(3):
        for tp in [ZERO,[D(0,ZERO)],[D(1,ZERO)]]:
            cands.append([D(u, add(tp,[D(v,ZERO)]))])
for c in cands:
    for w in range(3):
        t = [D(w, c)]
        if is_zero(c): continue
        lhs = zero_op(t)
        rhs = [D(w, zero_op(c))]
        tot+=1
        if lhs!=rhs:
            mism+=1
            if mism<=25:
                print(f"  MISMATCH w={w} c={fmt(c)}: t[0]={fmt(lhs)}  D_w(c[0])={fmt(rhs)}")
print(f"single-wrap: {mism}/{tot} mismatches")
