#!/usr/bin/env python3
"""The REAL content: t'=0 case.  c = D_u(D_v 0), single principal w/ single body.
Article wants: c[0]^k = D_u 0 with 0<k<=v+1.  Check the descent."""
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/python')
from buchholz import (ZERO, D, one, nat, is_zero, add, mul, lt_term, le_term,
                      in_OT, in_TB, dom, bracket, fmt)

def zero_op(a):
    return bracket(a, ZERO)

def iter0(a,k):
    for _ in range(k): a=zero_op(a)
    return a

print("=== c = D_u(D_v 0), c[0] trajectory; target D_u 0 ===")
for u in range(3):
    for v in range(5):
        c = [D(u,[D(v,ZERO)])]
        target = [D(u,ZERO)]
        traj=[fmt(c)]; cur=c; found=None
        for k in range(1, v+2):
            cur=zero_op(cur); traj.append(fmt(cur))
            if cur==target: found=k; break
        ok = found is not None
        print(f"u={u} v={v}: k={found} ({'OK' if ok else 'FAIL'}) traj={traj}")

print()
print("=== general (t' arbitrary, possibly 0):  D_u(t' + D_v 0) ===")
# Now the FULL lemma 1 (correctly: c[0]^k = D_u t', the marked principal).
# t' ranges incl 0 and nonzero.
tprimes = [ZERO, [D(0,ZERO)], [D(2,ZERO)], [D(1,ZERO),D(0,ZERO)], [D(0,[D(1,ZERO)])]]
fails=[]
tested=0
for u in range(3):
    for v in range(5):
        for tp in tprimes:
            inner = add(tp, [D(v,ZERO)])
            c = [D(u, inner)]
            target = [D(u, tp)]
            tested+=1
            cur=c; found=None
            for k in range(1, v+2):
                cur=zero_op(cur)
                if cur==target: found=k; break
            if found is None:
                fails.append((u,v,fmt(tp),[fmt(iter0(c,kk)) for kk in range(v+2)]))
print(f"FULL lemma1 (c-level): tested {tested} fails {len(fails)}")
for x in fails[:30]: print("  FAIL", x)
