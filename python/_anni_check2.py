#!/usr/bin/env python3
"""Model the CORRECT per-step transformation of the marked principal.
In an scb-decomp (s,c,b) of t with c the right-spine principal, t[0] acts
as c[0] *inside* the decomposition.  So the right object is c[0] where
c = D_u(t' + D_v 0).  Article: c[0] = D_u((t'+D_v 0)[0]).
We test: does iterating c -> c[0] reach D_u t' in <= v+1 steps?
And what is (t'+D_v 0)[0] exactly?"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/python')
from buchholz import (ZERO, D, one, nat, is_zero, add, mul, lt_term, le_term,
                      in_OT, in_TB, dom, bracket, fmt)

def zero_op(a):
    return bracket(a, ZERO)

# inspect (t' + D_v 0)[0] for various t', v
print("=== (D_v 0)[0] and (t'+D_v 0)[0] ===")
for v in range(4):
    Dv0 = [D(v, ZERO)]
    print(f"(D_{v} 0)[0] = {fmt(zero_op(Dv0))}")

print()
# Article claim per-step:  (t'+D_v 0)[0]:
#   v=0: -> t'   (since (D_0 0)[0]=0, and last-principal peel: (t'+D_0 0)[0]=t'+(D_0 0)[0]=t'+0=t')
#   v>0: -> t'+D_{v-1} 0   (since (D_v 0)[0]... wait, dom(D_v 0)=T_{v-1}, (D_v 0)[0]=0!)
# BUT article says (D_v 0)[0]=0 AND (D_v 0)[D_{v-1} 0]=D_{v-1} 0.  [0] uses z=0=numBT 0.
# dom(D_v 0) for v>0 = T_{v-1}.  bracket with z=0: ([].2) D_{u+1}0 [z] = z = 0.  So (D_v 0)[0]=0.
# So (t' + D_v 0)[0] = t' + (D_v 0)[0] = t' + 0 = t'  for ALL v (when t'+D_v0 is multi)!
print("=== last-principal peel: (t' + D_v 0)[0] when multi ===")
for v in range(4):
    for tp in [[D(0,ZERO)], [D(2,ZERO)], [D(1,ZERO),D(0,ZERO)]]:
        inner = add(tp, [D(v,ZERO)])
        print(f"v={v} t'={fmt(tp):20s} (t'+D_{v}0)[0] = {fmt(zero_op(inner))}  (t'={fmt(tp)})")
