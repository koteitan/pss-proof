#!/usr/bin/env python3
"""Validate candidate readings of Buchholz ([].4)(ii) fundamental sequence.

The article footnote (content.md 6427) reads:
  x_0 = D_u 0,  x_i = b[D_u x_{i-1}] (i>0),  a[n] = D_v b[x_n]   (a = D_v b, dom b = T_u, v<=u)
We found Lemma 3.2a (a[n] < a) fails for this 'literal' reading because the OUTER b[x_n]
is fed x_n in T_{u+1}, escaping dom(b)=T_u.

Candidate corrections (drop the doubled outer b):
  fix_xn  :  a[n] = D_v x_n
  fix_xn1 :  a[n] = D_v x_{n+1}

For every case-(ii) principal a = D_v b that is in OT and D_omega-free, we check, for n=0..N:
  (esc)  no bracket call ever receives an out-of-domain index   (well-definedness)
  (3.2a) a[n] < a
  (3.2b) a[m] < a[n] for m < n                                   (strict monotone)
  (3.2c) a[n] in T_v  (and in OT)
"""
from buchholz import (D, ZERO, INF, dom, lt_term, in_Tv, in_OT, in_TB,
                      is_zero, nat_value, in_dom, nat, mul, fmt)

IDX = [0, 1, 2]
NMAX = 4

# ---- reading-aware bracket ----
def brk(a, z, reading, trace):
    if is_zero(a): return ZERO
    if len(a) >= 2:
        return a[:-1] + brk([a[-1]], z, reading, trace)
    _, v, b = a[0]
    if is_zero(b):
        if v == 0: return ZERO
        if v == INF:
            n = nat_value(z); return [D(n+1, ZERO)]
        return z
    db = dom(b)
    if db == 'zero':
        n = nat_value(z); return mul([D(v, brk(b, ZERO, reading, trace))], n+1)
    if db == 'N' or (isinstance(db, tuple) and v > db[1]):
        if not in_dom(z, b): trace.append(('iii', fmt(b), fmt(z)))
        return [D(v, brk(b, z, reading, trace))]
    # ([].4)(ii)
    u = db[1]; n = nat_value(z)
    x = [D(u, ZERO)]                                  # x_0
    for _ in range(n):                               # build x_n
        arg = [D(u, x)]
        if not in_dom(arg, b): trace.append(('inner', fmt(b), fmt(arg)))
        x = brk(b, arg, reading, trace)
    if reading == 'literal':
        if not in_dom(x, b): trace.append(('outer', fmt(b), fmt(x)))
        return [D(v, brk(b, x, reading, trace))]
    if reading == 'fix_xn':
        return [D(v, x)]                              # a[n] = D_v x_n
    if reading == 'fix_xn1':
        arg = [D(u, x)]
        if not in_dom(arg, b): trace.append(('outer1', fmt(b), fmt(arg)))
        xn1 = brk(b, arg, reading, trace)
        return [D(v, xn1)]                            # a[n] = D_v x_{n+1}
    raise ValueError(reading)

# ---- term enumerator (small OT, D_omega-free) ----
def gen_principals(depth, cache):
    if depth in cache: return cache[depth]
    res = []
    subs = [ZERO] if depth == 0 else gen_terms(depth-1, cache)
    for v in IDX:
        for a in subs:
            res.append(D(v, a))
    cache[depth] = res
    return res

def gen_terms(depth, cache):
    princ = []
    for d in range(depth+1):
        princ += gen_principals(d, cache)
    # dedupe principals
    seen = []; up = []
    for p in princ:
        if p not in up: up.append(p)
    terms = [ZERO] + [[p] for p in up]
    for p in up:
        for q in up:
            terms.append([p, q])
    return [t for t in terms if in_OT(t)]

def case_ii_principals(depth):
    cache = {}
    res = []
    for t in gen_terms(depth, cache):
        if len(t) != 1: continue                     # principal a = D_v b
        _, v, b = t[0]
        if is_zero(b): continue
        d = dom(b)
        if isinstance(d, tuple) and d[0] == 'Tv' and v <= d[1]:   # case (ii)
            if in_OT(t) and in_TB(t):
                res.append((t, v, d[1]))
    return res

# ---- run ----
READINGS = ['literal', 'fix_xn', 'fix_xn1']
cases = case_ii_principals(2)
print(f"case-(ii) OT, D_omega-free principals enumerated: {len(cases)}\n")

for r in READINGS:
    n_esc = n_32a = n_32b = n_32c = 0
    tot = 0
    cex = {}
    for (a, v, u) in cases:
        seq = []
        bad_esc = bad_a = bad_b = bad_c = False
        for n in range(NMAX+1):
            trace = []
            an = brk(a, nat(n), r, trace)
            if trace: bad_esc = True
            if not lt_term(an, a): bad_a = True
            if not in_Tv(an, v): bad_c = True
            if in_OT(a) and not in_OT(an): bad_c = True
            seq.append(an)
        for i in range(len(seq)):
            for j in range(i+1, len(seq)):
                if not lt_term(seq[i], seq[j]): bad_b = True
        tot += 1
        n_esc += (not bad_esc); n_32a += (not bad_a)
        n_32b += (not bad_b); n_32c += (not bad_c)
        if bad_a and 'a' not in cex: cex['a'] = (fmt(a), [fmt(s) for s in seq])
        if bad_esc and 'esc' not in cex: cex['esc'] = (fmt(a), trace)
    print(f"[{r:8}]  well-def(no escape): {n_esc}/{tot}   "
          f"3.2a(a[n]<a): {n_32a}/{tot}   3.2b(mono): {n_32b}/{tot}   3.2c(in T_v/OT): {n_32c}/{tot}")
    if 'a' in cex: print(f"            3.2a CEX: a={cex['a'][0]}  seq={cex['a'][1]}")
    if 'esc' in cex: print(f"            escape  : a={cex['esc'][0]}  trace={cex['esc'][1][:2]}")
print()
print("Interpretation: the correct reading is the one with ALL four = tot/tot.")
