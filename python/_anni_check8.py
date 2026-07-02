#!/usr/bin/env python3
"""Test the TRUE scb-level lemma 1: c=D_u(t'+D_v 0) is the RIGHTMOST-spine
principal of t (t = wrap of c). Compute t[0], read off its rightmost-spine
principal c'. Article: c' in {D_u t', D_u(t'+D_{v-1} 0)} (induct) reaching
D_u t' in <= v+1 [0]-steps on t.  Build t = D_w(c) (single wrap, w>u so
dom propagates) and check t[0]'s deepest principal."""
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/python')
from buchholz import (ZERO, D, one, nat, is_zero, add, mul, lt_term, le_term,
                      in_OT, in_TB, dom, bracket, fmt)

def zero_op(a): return bracket(a, ZERO)

def rightmost_principal_body(t):
    # the deepest right-spine: follow last principal's body chain to the
    # principal whose body's last-principal is D_? 0 ... return the c-occurrence.
    # Here we just return t's outer single principal body if single.
    return t

# Simplest faithful t: c sits at right spine with NO wrapper (t=c).  Then
# t[0]=c[0].  We already know that's the kind-1 collapse when t'!=0.
# So the article statement must put c at the rightmost spine of a t where
# the [0] recursion REACHES c via dom-propagation, i.e. dom at outer levels
# routes to c.  The cleanest faithful witness: t = c itself when t'=0
# (then c=D_u(D_v 0)) -- the REAL inductive content is t'=0.
# Let's verify lemma1 for t'=0 ONLY and read the per-step principal.
print("=== t'=0 case: c=D_u(D_v 0); trajectory and per-step principal ===")
for u in range(4):
  for v in range(5):
    c=[D(u,[D(v,ZERO)])]
    if not in_OT(c): continue
    target=[D(u,ZERO)]
    cur=c; traj=[fmt(c)]; found=None
    for k in range(1,v+2):
        cur=zero_op(cur); traj.append(fmt(cur))
        if cur==target: found=k; break
    print(f"u={u} v={v}: k={found}  {traj}")
print()
print("Per-step: is each step D_u(D_w 0) -> D_u(D_{w-1} 0) (or ->D_u 0)?")
# check the descent law for t'=0:  (D_u(D_w 0))[0] = ?
for u in range(4):
  for w in range(5):
    c=[D(u,[D(w,ZERO)])]
    print(f"  (D_{u}(D_{w} 0))[0] = {fmt(zero_op(c))}")
