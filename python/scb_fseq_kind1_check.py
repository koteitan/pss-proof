#!/usr/bin/env python3
"""Empirical validation for correction A24: §7.2 命題（scb分解と基本列の関係）(2).

The article gives, for a kind-1 scb-decomposition with marked sub-principal D_v 0
(prefixed by D_u s0, suffixed by b0):
    t[n] = s1  D_u (s0 D_{v-1})^{n+1} 0 b0^{n+1}  b1        (LITERAL, article 1978)
This is FALSE for non-empty s0 or b0.  The xseq tower has base x0 = D_{v-1} 0
(bare, NOT wrapped by s0/b0) and step x_{i+1} = D_u s0 D_{v-1} x_i b0, so the true
formula wraps (s0 D_{v-1}) n times (not n+1) and leaves a bare innermost D_{v-1}:
    t[n] = s1  D_u (s0 D_{v-1})^n D_{v-1} 0 b0^n  b1          (CORRECTED, A24)
The two coincide exactly when s0 = b0 = () (the case the proven Isabelle lemma
m_7_2_scb_fseq_kind1_basic and the downstream §8.6/§8.7 零化 lemmas consume).

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
def corrected(s1, u, s0, v, b0, b1, n):
    return s1 + [('D',u)] + rep(n, s0 + [('D',v-1)]) + [('D',v-1)] + ['Z'] + rep(n, b0) + b1

def run(label, t, s1, u, s0, v, b0, b1):
    lit_ok = cor_ok = 0; tot = 0
    for n in range(0, 4):
        actual = flat_term(B.bracket(t, B.nat(n)))
        tot += 1
        if actual == literal(s1,u,s0,v,b0,b1,n):   lit_ok += 1
        if actual == corrected(s1,u,s0,v,b0,b1,n):  cor_ok += 1
    print(f"  [{label}] u={u} v={v}: literal {lit_ok}/{tot}  corrected {cor_ok}/{tot}")
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
    print(f"{name:10s}: literal {l}/{t}   corrected {c}/{t}")
