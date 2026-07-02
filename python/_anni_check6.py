#!/usr/bin/env python3
"""For lemma 1 via operB_scb_spine, need:
  (A) domB(D_u(t'+D_v 0)) = NatSet  ?
  (B) operB(D_u(t'+D_v 0)) (numBT 0) = single principal D_u(something) ?
Model dom and the c[0] value for c = D_u(t'+D_v 0)."""
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/python')
from buchholz import (ZERO, D, one, nat, is_zero, add, mul, lt_term, le_term,
                      in_OT, in_TB, dom, bracket, fmt)

def zero_op(a):
    return bracket(a, ZERO)

print("=== (A) domB(D_u(t'+D_v 0)) and (B) c[0] ===")
tprimes = [ZERO, [D(0,ZERO)], [D(3,ZERO)], [D(1,ZERO),D(0,ZERO)], [D(0,[D(1,ZERO)])]]
for u in range(3):
  for v in range(4):
    for tp in tprimes:
        inner = add(tp, [D(v,ZERO)])
        c = [D(u, inner)]
        dc = dom(c)
        c0 = zero_op(c)
        single = (len(c0)==1)
        nat_dom = (dc == 'N')
        flag = "" if (nat_dom and single) else "  <-- "
        print(f"u={u} v={v} t'={fmt(tp):18s} dom(c)={str(dc):10s} single_c0={single} c[0]={fmt(c0)}{flag}")
