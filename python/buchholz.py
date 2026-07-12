#!/usr/bin/env python3
"""Faithful Python model of the Buchholz notation system [Buc1] used in §7
(see docs/buchholz.md).  Enables empirically auditing §7 propositions the way
red_model.py does for §6.

Representation
-------------
A term is a list of *principal* terms (the `(a_0,…,a_k)` form):
  - 0            := []                      (the empty list)
  - principal    := ('D', v, a)             v an index (int, or INF for ω), a a term
  - (a_0,…,a_k)  := [p_0, …, p_k]           each p_i a principal
  - a single principal `a` is the term `[a]`.
Addition is list concatenation:  a + b = a + b   (matches (a_0..a_n)+(b_0..b_m)).
`1` := D_0 0 = ('D',0,[]);  the natural n := [D_0 0]*n  (= 1·n).
"""
import math
INF = math.inf            # ω

# ---- constructors ----
ZERO = []
def D(v, a): return ('D', v, a)          # principal term D_v a
def one(): return [D(0, ZERO)]
def nat(n): return [D(0, ZERO)] * n      # natural number n = 1·n

def is_zero(a): return a == []
def is_principal_term(a): return len(a) == 1
def add(a, b): return a + b              # ([].3 addition)
def mul(a, n):                           # a·n
    r = []
    for _ in range(n): r = r + a
    return r

# ---- order < (docs/buchholz.md (<1)-(<3)) ----
def lt_princ(p, q):                      # D_u a < D_v b
    _, u, a = p; _, v, b = q
    if u != v: return u < v
    return lt_term(a, b)
def le_princ(p, q): return p == q or lt_princ(p, q)

def lt_term(a, b):                       # a < b on terms (lists of principals)
    if is_zero(a): return not is_zero(b)            # (<1) 0 < b iff b != 0
    if is_zero(b): return False
    # dictionary order; proper prefix is smaller
    for i in range(min(len(a), len(b))):
        if a[i] != b[i]:
            return lt_princ(a[i], b[i])
    return len(a) < len(b)
def le_term(a, b): return a == b or lt_term(a, b)

# ---- G_u a (G1)-(G3): the set of sub-terms b with index >= u under D_v, v>=u ----
def G(u, a):
    out = []
    for p in a:                          # (G2) union over principals
        _, v, b = p
        if v >= u:                       # (G3) u <= v
            out.append(b); out += G(u, b)
        # else (v < u): contributes nothing
    return out
def G_lt(u, a, bnd):                     # G_u a < bnd  (all elements < bnd)
    return all(lt_term(x, bnd) for x in G(u, a))

# ---- OT membership (OT1)-(OT3) ----
def in_OT(a):
    if is_zero(a): return True                       # (OT1)
    if len(a) >= 2:                                  # (OT2) principal list, weakly decreasing
        if not all(le_princ(a[i+1], a[i]) for i in range(len(a)-1)): return False
        return all(in_OT([p]) for p in a)
    # single principal D_v b
    _, v, b = a[0]
    return in_OT(b) and G_lt(v, b, b)                # (OT3) b in OT and G_v b < b

# ---- T_v membership ([Buc1] §3): top-level indices <= v ----
def in_Tv(a, v):
    return is_zero(a) or all(p[1] <= v for p in a)

# ---- T_B : the D_ω-free terms (recursive: no index equals ω anywhere) ----
def in_TB(a):
    return all(p[1] != INF and in_TB(p[2]) for p in a)

# ---- dom(a) and fundamental sequence a[z]  ([].0)-([].5) ----
# dom is returned as a tag: 'empty' | 'zero' | 'N' | ('Tv', u)
def dom(a):
    if is_zero(a): return 'empty'                    # ([].0)
    if len(a) >= 2:                                  # ([].5) dom(a)=dom(a_k)
        return dom([a[-1]])
    _, v, b = a[0]                                   # a = D_v b
    if is_zero(b):                                   # D_v 0
        if v == 0: return 'zero'                     # ([].1) dom(1)={0}
        if v == INF: return 'N'                      # ([].3) dom(D_ω 0)=ℕ
        return ('Tv', v-1)                           # ([].2) dom(D_{u+1}0)=T_u
    db = dom(b)                                      # ([].4) a=D_v b, b!=0
    if db == 'zero': return 'N'                                       # (i)
    if db == 'N': return 'N'                                          # (iii) dom(b)=ℕ
    u = db[1]                                         # dom(b)=T_u
    if v <= u: return 'N'                                             # (ii)
    return ('Tv', u)                                                  # (iii) T_u, u<v

def nat_value(z):
    """if z is a natural number term (1·n) return n, else None."""
    if all(p == D(0, ZERO) for p in z): return len(z)
    return None

def in_dom(z, a):
    d = dom(a)
    if d == 'empty': return False
    if d == 'zero': return is_zero(z)
    if d == 'N': return nat_value(z) is not None
    return in_Tv(z, d[1])                             # T_u

def bracket(a, z):
    """a[z].  z is a term; for ℕ-domain its nat value is used."""
    if is_zero(a): return ZERO                        # 0[n]=0
    if len(a) >= 2:                                   # ([].5) (a_0..a_k)[z] = (a_0..a_{k-1}) + a_k[z]
        return a[:-1] + bracket([a[-1]], z)
    _, v, b = a[0]                                    # a = D_v b
    if is_zero(b):
        if v == 0: return ZERO                        # ([].1) 1[0]=0
        if v == INF:                                  # ([].3) (D_ω 0)[n] = D_{n+1}0
            n = nat_value(z); return [D(n+1, ZERO)]
        return z                                      # ([].2) (D_{u+1}0)[z]=z
    db = dom(b)
    if db == 'zero':                                  # ([].4)(i) a[n] = (D_v b[0])·(n+1)
        n = nat_value(z)
        return mul([D(v, bracket(b, ZERO))], n+1)
    if db == 'N' or (isinstance(db, tuple) and v > db[1]):   # ([].4)(iii) dom(a)=dom(b)
        return [D(v, bracket(b, z))]
    # ([].4)(ii) dom(b)=T_u, v<=u<omega, [Buc2] modification.
    # CORRECTED (supersedes A23): the article footnote (content.md 6427) prints
    #   x_0 = D_u 0,  x_i = b[D_u x_{i-1}],  a[n] = D_v b[x_n]
    # and the defect is a TRANSPOSITION inside x_i, not a doubled outer b[.]:
    #   x_0 = D_u 0,  x_i = D_u b[x_{i-1}],  a[n] = D_v b[x_n]
    # which is exactly Buchholz's fundamental sequence
    #   psi_v(b)[n] = psi_v(b[g_n]),  g_0 = Omega_u,  g_{n+1} = psi_u(b[g_n]).
    # Under this reading every x_i is D_u-headed, hence stays in dom(b)=T_u, and
    # the article's own §7.2 (2) holds literally (112/112; the old "drop the outer
    # b[.]" reading fails 60/60).
    u = db[1]; n = nat_value(z)
    x = [D(u, ZERO)]                                  # x_0 = D_u 0
    for _ in range(n):
        x = [D(u, bracket(b, x))]                     # x_i = D_u b[x_{i-1}]
    return [D(v, bracket(b, x))]                      # a[n] = D_v b[x_n]

# ---- pretty printer ----
def fmt(a):
    if is_zero(a): return "0"
    def fp(p):
        _, v, b = p
        idx = "ω" if v == INF else str(v)
        return f"D_{idx}({fmt(b)})"
    return "(" + ",".join(fp(p) for p in a) + ")" if len(a) > 1 else fp(a[0])

if __name__ == "__main__":
    Z = ZERO
    print("1 =", fmt(one()))
    print("D_1 0 =", fmt([D(1, Z)]), " 1 < D_1 0 ?", lt_term(one(), [D(1, Z)]), "(expect True)")
    Dw0 = [D(INF, Z)]
    print("(D_ω 0)[3] =", fmt(bracket(Dw0, nat(3))), "(expect D_4(0))")
    print("(D_2 0)[z=D_0 0] =", fmt(bracket([D(2, Z)], [D(0, Z)])), "(expect D_0(0); dom=T_1, identity)")
    print("1[0] =", fmt(bracket(one(), Z)), "(expect 0)")
    # D_0 (D_ω 0): b=D_ω 0, dom(b)=ℕ -> (iii) dom(a)=ℕ, a[n]=D_0(b[n])
    a = [D(0, Dw0)]
    print("dom(D_0(D_ω 0)) =", dom(a), "; [2] =", fmt(bracket(a, nat(2))), "(expect D_0(D_3(0)))")
    print("OT(1)?", in_OT(one()), " OT(D_1 0)?", in_OT([D(1, Z)]), " T_B(D_ω 0)?", in_TB(Dw0), "(expect True True False)")
