#!/usr/bin/env python3
"""When does (D_u body)[0] = D_u(body[0]) hold?  ([].4)(iii) branch.
And: the article's lemma 1 requires t in OT_B, c=D_u(t'+D_v 0) an scb-occurrence.
Crucially in OT terms the DESCENDING condition constrains t'.  Re-examine WITH
the OT constraint and the article's actual recursion."""
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/python')
from buchholz import (ZERO, D, one, nat, is_zero, add, mul, lt_term, le_term,
                      in_OT, in_TB, dom, bracket, fmt, le_princ)

def zero_op(a):
    return bracket(a, ZERO)
def iter0(a,k):
    for _ in range(k): a=zero_op(a)
    return a

# The article's lemma 1 hypothesis: (s, D_u(t'+D_v 0), b) is an scb-decomp of t,
# AND t in OT_B (from the OUTER lemma 2 which calls lemma1).  Actually lemma 1
# (§8.6) states t,t' in T_B only.  But the recursion descent (D_v 0 ->D_{v-1}0)
# in the article PROOF requires the [0] to act on the body, i.e. ([].4)(iii):
#   dom(D_u body)= dom(body), needs dom(body) != {0} and not xseq case.
# For c = D_u(t'+D_v 0) to recurse into the body via (iii), need:
#   dom(t'+D_v 0) = dom(D_v 0) = (v=0: zero; v>0: T_{v-1}) and:
#     if v=0: dom=zero -> ([].4)(i)!  c[0]=(D_u(body[0]))*1 = D_u(body[0]).  body[0]=(t'+D_0 0)[0].
#     if v>0: dom=T_{v-1}; (iii) needs u> v-1 i.e. u>=v. (ii) when u<=v-1 i.e. u<v -> xseq tower!
# So the article identity (D_u body)[0]=D_u(body[0]) needs u>=v (for v>0) -- BUT the article
# claims it for ALL u,v.  Let's check: is the article lemma TRUE on its T_B domain, or does it
# need u>=v?  Check c-level reaching D_u t' in <= v+1 steps, recording when it works.
print("=== c=D_u(t'+D_v 0): does c[0]^k = D_u t' for some k in 1..v+1? classify by u vs v ===")
tprimes = [ZERO, [D(0,ZERO)], [D(3,ZERO)], [D(1,ZERO),D(0,ZERO)], [D(0,[D(1,ZERO)])]]
rows=[]
for u in range(4):
    for v in range(5):
        for tp in tprimes:
            inner = add(tp, [D(v,ZERO)])
            c = [D(u, inner)]
            target = [D(u, tp)]
            cur=c; found=None
            for k in range(1, v+2):
                cur=zero_op(cur)
                if cur==target: found=k; break
            ok = found is not None
            rows.append((u,v,is_zero(tp),u>=v,ok,found))

# summarize: for t'=0 (the real inductive case) and t'!=0
from collections import Counter
print("t'=0 cases:")
c0 = [r for r in rows if r[2]]
print("  all OK?", all(r[4] for r in c0), " k distribution:", Counter(r[5] for r in c0))
print("t'!=0 cases:")
c1 = [r for r in rows if not r[2]]
print("  all OK?", all(r[4] for r in c1))
print("  OK when u>=v?", all(r[4] for r in c1 if r[3]))
print("  OK when u<v?", all(r[4] for r in c1 if not r[3]))
print("  fails:", [(r[0],r[1]) for r in c1 if not r[4]][:20])
