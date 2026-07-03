#!/usr/bin/env python3
"""Under OT constraint: does domB(D_u(t'+D_v 0))=NatSet always hold?
And does lemma1 (c[0]^k=D_u t', 0<k<=v+1) hold for OT c?"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/python')
from buchholz import (ZERO, D, one, nat, is_zero, add, mul, lt_term, le_term,
                      in_OT, in_TB, dom, bracket, fmt)

def zero_op(a): return bracket(a, ZERO)
def iter0(a,k):
    for _ in range(k): a=zero_op(a)
    return a

# enumerate small OT_B terms as t' candidates
def gen_terms(depth, maxidx):
    if depth==0:
        return [ZERO]
    sub = gen_terms(depth-1, maxidx)
    princ=[]
    for v in range(maxidx+1):
        for b in sub:
            p=[D(v,b)]
            if in_OT(p): princ.append(p)
    # multi: descending lists of principals (length<=3)
    terms=[ZERO]+princ
    for k in range(2,3):
        for combo in itertools.product(princ, repeat=k):
            t=[]
            for c in combo: t+=c
            if in_OT(t): terms.append(t)
    # dedup
    seen=[]; out=[]
    for t in terms:
        if t not in seen: seen.append(t); out.append(t)
    return out

cands = gen_terms(2, 2)
print(f"#OT term candidates for t': {len(cands)}")

natset_fail=0; lem1_fail=0; tot=0; checked_ot_c=0
fails=[]
for u in range(4):
  for v in range(5):
    for tp in cands:
        inner = add(tp, [D(v,ZERO)])
        c = [D(u, inner)]
        if not in_OT(c): continue          # restrict to OT marked principals
        checked_ot_c+=1
        dc = dom(c)
        if dc != 'N':
            natset_fail+=1
            if len(fails)<25: fails.append(('NOTNAT', u,v,fmt(tp), str(dc), fmt(c)))
        # lemma1 c-level
        target=[D(u,tp)]
        cur=c; found=None
        for k in range(1,v+2):
            cur=zero_op(cur)
            if cur==target: found=k; break
        if found is None:
            lem1_fail+=1
            if len(fails)<25: fails.append(('LEM1', u,v,fmt(tp),fmt(c),
                                            [fmt(iter0(c,kk)) for kk in range(v+2)]))
        tot+=1
print(f"OT marked principals checked: {checked_ot_c}")
print(f"domB(c)!=NatSet among OT c: {natset_fail}")
print(f"lemma1 c-level fails among OT c: {lem1_fail}")
for f in fails: print("  ", f)
