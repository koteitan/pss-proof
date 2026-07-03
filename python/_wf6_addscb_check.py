#!/usr/bin/env python3
"""Empirical truth-check for p_7_2_add_scb (Front B, §7.2).
BT model:  Trm ps  ->  tuple of principals;  DB v a -> ('D', v, a).
flatBT, flatBP, scb_decomp, MarkedB transcribed from pss_paper.thy.
We use small finite indices (0,1) and bounded depth, EXCLUDING omega (INF):
all c,c' are in T_B (dfree) since indices are finite ints.
"""
import itertools

LP, CM, RP, Zsym = 'LP', 'CM', 'RP', 'Zsym'
def Dsym(u): return ('Dsym', u)

# ---- BT representation: Trm(ps) = ('Trm', tuple_of_principals); DB v a = ('D', v, a)
def Trm(ps): return ('Trm', tuple(ps))
def DB(v, a): return ('D', v, a)

def flatBP(p):
    _, u, a = p
    return [Dsym(u)] + flatBT(a)

def flatBT(t):
    _, ps = t
    if len(ps) == 0:
        return [Zsym]
    if len(ps) == 1:
        return flatBP(ps[0])
    head = ps[0]; rest = ps[1:]
    mid = []
    for r in rest:
        mid += [CM] + flatBP(r)
    return [LP] + (flatBP(head) + mid) + [RP]

def dfree_BT(t):
    _, ps = t
    return all(dfree_BP(p) for p in ps)
def dfree_BP(p):
    _, v, a = p
    return v != 'INF' and dfree_BT(a)
def in_TB(t): return dfree_BT(t)

def isPTB_str(c):
    # exists p. dfree_BP p and c == flatBP p
    # search among enumerated principals (use catalogue passed globally)
    return any(dfree_BP(p) and c == flatBP(p) for p in ALL_PRINC)

def scb_decomp(t, s, c, b):
    if flatBT(t) != s + c + b:
        return False
    if t != Trm([]):
        if not isPTB_str(c):
            return False
    if not all(x == RP for x in b):
        return False
    return True

def addBT(t, c):
    _, a = t; _, bs = c
    return Trm(list(a) + list(bs))

def in_MarkedB(t, c):
    # exists s,b. scb_decomp t s (flatBT c) b
    fc = flatBT(c)
    ft = flatBT(t)
    n = len(ft); m = len(fc)
    for i in range(n - m + 1):
        s = ft[:i]; b = ft[i+m:]
        if ft[i:i+m] == fc and scb_decomp(t, s, fc, b):
            return True
    return False

# ---- enumerate small BT terms and principals ----
def enum_terms(depth, idxs, max_princ):
    # returns list of BT terms up to given depth, principal-list length up to max_princ
    if depth == 0:
        return [Trm([])]
    sub = enum_terms(depth-1, idxs, max_princ)
    princ = []
    for v in idxs:
        for a in sub:
            princ.append(DB(v, a))
    terms = [Trm([])]
    # principal lists of length 1..max_princ
    for k in range(1, max_princ+1):
        for combo in itertools.product(princ, repeat=k):
            terms.append(Trm(list(combo)))
    return terms

IDXS = [0, 1]
DEPTH = 2
MAXP = 2

ALL_TERMS = enum_terms(DEPTH, IDXS, MAXP)
ALL_PRINC = []
for t in ALL_TERMS:
    _, ps = t
    for p in ps:
        if p not in ALL_PRINC:
            ALL_PRINC.append(p)
# also principals from one deeper to make isPTB search complete enough
for t in enum_terms(DEPTH, IDXS, MAXP):
    _, ps = t
    for p in ps:
        if p not in ALL_PRINC:
            ALL_PRINC.append(p)

# principal terms c = Trm([p]) in T_B
PRINC_TERMS = [Trm([p]) for p in ALL_PRINC if in_TB(Trm([p]))]
print(f"#terms={len(ALL_TERMS)} #princ_terms(c)={len(PRINC_TERMS)}")

TB_TERMS = [t for t in ALL_TERMS if in_TB(t)]

# ---- Conjunct (1): (t+c, c) in MarkedB ----
fail1 = 0; tot1 = 0
for t in TB_TERMS:
    for c in PRINC_TERMS:
        tot1 += 1
        if not in_MarkedB(addBT(t, c), c):
            fail1 += 1
            if fail1 <= 5:
                print("FAIL1", t, c)
print(f"Conjunct(1): {fail1}/{tot1} failures")

# ---- Conjunct (2): given scb_decomp (t+c) s (flatBT c) b, then scb_decomp (t+c') s (flatBT c') b ----
fail2 = 0; tot2 = 0
for t in TB_TERMS:
    for c in PRINC_TERMS:
        tc = addBT(t, c)
        ftc = flatBT(tc); fc = flatBT(c)
        # enumerate all (s,b) decompositions of t+c with c
        decomps = []
        m = len(fc); n = len(ftc)
        for i in range(n - m + 1):
            s = ftc[:i]; b = ftc[i+m:]
            if ftc[i:i+m] == fc and scb_decomp(tc, s, fc, b):
                decomps.append((s, b))
        for c2 in PRINC_TERMS:
            tc2 = addBT(t, c2); fc2 = flatBT(c2)
            for (s, b) in decomps:
                tot2 += 1
                if not scb_decomp(tc2, s, fc2, b):
                    fail2 += 1
                    if fail2 <= 8:
                        print("FAIL2 t=",t,"c=",c,"c'=",c2,"s=",s,"b=",b)
print(f"Conjunct(2): {fail2}/{tot2} failures")

# ---- Conjunct (3): nested D_v context ----
# u1 in T_B, flatBT u1 = s1 @ (Dsym v # flatBT(t+c)) @ b1, scb_decomp u1 s0 (flatBT c) b0
#  => exists u1' in T_B with flatBT u1' = s1 @ (Dsym v # flatBT(t+c')) @ b1
#     and scb_decomp u1' s0 (flatBT c') b0
fail3 = 0; tot3 = 0; checked3 = 0
for t in TB_TERMS:
    for c in PRINC_TERMS:
        tc = addBT(t, c); ftc = flatBT(tc)
        for v in IDXS:
            target_sub = [Dsym(v)] + ftc
            for u1 in TB_TERMS:
                fu1 = flatBT(u1)
                # find s1,b1 with fu1 = s1 @ target_sub @ b1
                L = len(target_sub)
                for i in range(len(fu1) - L + 1):
                    if fu1[i:i+L] != target_sub:
                        continue
                    s1 = fu1[:i]; b1 = fu1[i+L:]
                    # find scb_decomp u1 s0 (flatBT c) b0
                    fc = flatBT(c); m = len(fc)
                    for j in range(len(fu1) - m + 1):
                        s0 = fu1[:j]; b0 = fu1[j+m:]
                        if fu1[j:j+m] == fc and scb_decomp(u1, s0, fc, b0):
                            # premise holds; check conclusion for each c'
                            for c2 in PRINC_TERMS:
                                tc2 = addBT(t, c2); fc2 = flatBT(c2)
                                ftc2 = flatBT(tc2)
                                want = s1 + ([Dsym(v)] + ftc2) + b1
                                tot3 += 1
                                checked3 += 1
                                ok = False
                                for u1p in TB_TERMS:
                                    if flatBT(u1p) == want and scb_decomp(u1p, s0, fc2, b0):
                                        ok = True; break
                                if not ok:
                                    fail3 += 1
                                    if fail3 <= 8:
                                        print("FAIL3 t=",t,"c=",c,"c'=",c2,"v=",v,"u1=",u1,"s0=",s0,"b0=",b0)
print(f"Conjunct(3): {fail3}/{tot3} failures (checked {checked3})")
