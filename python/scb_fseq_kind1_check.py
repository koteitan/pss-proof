#!/usr/bin/env python3
"""Empirical validation for A23: §7.2 命題（scb分解と基本列の関係）(2).

The article gives, for a kind-1 scb-decomposition with marked sub-principal D_v 0
(prefixed by D_u s0, suffixed by b0):
    t[n] = s1  D_u (s0 D_{v-1})^{n+1} 0 b0^{n+1}  b1        (LITERAL, article 1978)
The xseq tower itself has base x0 = D_{v-1} 0 and therefore contains n wrappers:
    x_n = ([D_{v-1}] s0)^n D_{v-1} 0 b0^n.
The surrounding call ``operB body x_n`` contributes one final s0/b0 wrapper.
After the standard prefix shift this is exactly the article's n+1 formula above,
also when s0 or b0 is non-empty.  ``tower_only`` below deliberately omits that
outer wrapper and is retained as a negative control.

operB/xseq are modelled via buchholz.bracket.  Run: python3 scb_fseq_kind1_check.py
"""
import sys
sys.path.insert(0, "/home/koteitan/proofs/pss-proof/python")
import buchholz as B

def flat_term(a):
    if B.is_zero(a): return ['Z']
    if len(a) == 1: return flat_princ(a[0])
    res = ['LP'] + flat_princ(a[0])
    for p in a[1:]: res += ['CM'] + flat_princ(p)
    return res + ['RP']
def flat_princ(p):
    _, v, b = p
    return [('D', v)] + flat_term(b)
def rep(k, xs):
    out = []
    for _ in range(k): out += xs
    return out

def literal(s1, u, s0, v, b0, b1, n):
    return s1 + [('D',u)] + rep(n+1, s0 + [('D',v-1)]) + ['Z'] + rep(n+1, b0) + b1
def tower_only(s1, u, s0, v, b0, b1, n):
    return s1 + [('D',u)] + rep(n, s0 + [('D',v-1)]) + [('D',v-1)] + ['Z'] + rep(n, b0) + b1

def run(label, t, s1, u, s0, v, b0, b1):
    lit_ok = cor_ok = 0; tot = 0
    for n in range(0, 4):
        actual = flat_term(B.bracket(t, B.nat(n)))
        tot += 1
        if actual == literal(s1,u,s0,v,b0,b1,n):   lit_ok += 1
        if actual == tower_only(s1,u,s0,v,b0,b1,n):  cor_ok += 1
    print(f"  [{label}] u={u} v={v}: article {lit_ok}/{tot}  tower-only {cor_ok}/{tot}")
    return (lit_ok, cor_ok, tot)

def total(rows):
    return (sum(r[0] for r in rows), sum(r[1] for r in rows), sum(r[2] for r in rows))

# --- s0 = b0 = () : t = c2 = D_u(D_v 0), plus a multi embedding ---
print("Case s0=b0=():")
basic = []
for u in range(0, 3):
    for v in range(u+1, u+4):
        t = [B.D(u, [B.D(v, [])])]
        if B.in_TB(t): basic.append(run("A", t, [], u, [], v, [], []))
for u in range(0, 2):
    for v in range(u+1, u+3):
        c2 = [B.D(u, [B.D(v, [])])]; X = B.D(v+5, [])
        t = [X] + c2
        if B.in_TB(t):
            basic.append(run("B", t, ['LP'] + flat_princ(X) + ['CM'], u, [], v, [], ['RP']))

# --- s0 != () : c2 = D_u(D_w(D_v 0)), s0 = [D_w], u<v<=w ---
print("Case s0!=():")
s0case = []
for u in range(0, 2):
    for v in range(u+1, u+3):
        for w in range(v, v+3):
            t = [B.D(u, [B.D(w, [B.D(v, [])])])]
            if B.in_TB(t): s0case.append(run("C", t, [], u, [('D',w)], v, [], []))

# --- b0 != () : c2 = D_u((X, D_v 0)), b0 = [RP] ---
print("Case b0!=():")
b0case = []
for (u, v, Xi) in [(1,3,5), (0,2,4), (2,5,6)]:
    X = B.D(Xi, [])
    t = [B.D(u, [X, B.D(v, [])])]
    if B.in_TB(t):
        b0case.append(run("D", t, [], u, ['LP'] + flat_princ(X) + ['CM'], v, ['RP'], []))

for name, rows in [("s0=b0=()", basic), ("s0!=()", s0case), ("b0!=()", b0case)]:
    l, c, t = total(rows)
    print(f"{name:10s}: article {l}/{t}   tower-only {c}/{t}")
