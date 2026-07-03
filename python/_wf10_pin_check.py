#!/usr/bin/env python3
"""Empirical truth-check for the cut-pinning (Front B, wf10):
For t != Trm [], all kind-0 scb-decompositions of t share length s;
and all kind-1 scb-decompositions of t share length s.
Also check the article's intermediate claims:
  - RightNodes c_i is a suffix segment of RightNodes t
  - the cut is the last occurrence of Dsym v0 in flatBT t.
"""
import itertools

LP, CM, RP, Zsym = 'LP', 'CM', 'RP', 'Zsym'
def Dsym(u): return ('Dsym', u)
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

# RightNodes: Trm [] -> []; else RightNodes of last principal DB u a -> u # RightNodes a
def RightNodes_T(t):
    _, ps = t
    if len(ps) == 0:
        return []
    _, u, a = ps[-1]
    return [u] + RightNodes_T(a)

PRINC_MAP = {}  # filled after ALL_PRINC built: tuple(flatBP p) -> p

def isPTB_str(c):
    return tuple(c) in PRINC_MAP

def get_princ(c):
    return PRINC_MAP.get(tuple(c))

def scb_decomp(t, s, c, b):
    if flatBT(t) != s + c + b:
        return False
    if t != Trm([]):
        if not isPTB_str(c):
            return False
    if not all(x == RP for x in b):
        return False
    return True

def RN_princ(p):
    # RightNodes (Trm [p])
    return RightNodes_T(Trm([p]))

def scb_kind0(t, s, c, b):
    if not scb_decomp(t, s, c, b):
        return False
    p = get_princ(c)
    if p is None:
        # if no principal, the (forall p. c=flatBP p -> ...) is vacuous
        return True
    r = RN_princ(p)
    return len(r) == 2 and r[1] == 0

def scb_kind1(t, s, c, b):
    if not scb_decomp(t, s, c, b):
        return False
    p = get_princ(c)
    if p is None:
        return True
    r = RN_princ(p)
    j1 = len(r) - 1
    if j1 < 1:
        return False
    if not (r[0] < r[j1]):
        return False
    for j in range(1, j1):
        if not (r[j] >= r[j1]):
            return False
    return True

def all_decomps(t, pred):
    ft = flatBT(t)
    n = len(ft)
    out = []
    for i in range(n+1):
        for k in range(n - i + 1):
            s = ft[:i]; c = ft[i:i+k]; b = ft[i+k:]
            if pred(t, s, c, b):
                out.append((s, c, b))
    return out

def enum_terms(depth, idxs, max_princ):
    if depth == 0:
        return [Trm([])]
    sub = enum_terms(depth-1, idxs, max_princ)
    princ = []
    for v in idxs:
        for a in sub:
            princ.append(DB(v, a))
    terms = [Trm([])]
    for k in range(1, max_princ+1):
        for combo in itertools.product(princ, repeat=k):
            terms.append(Trm(list(combo)))
    return terms

IDXS = [0, 1, 2]
DEPTH = 2
MAXP = 2

ALL_TERMS = enum_terms(DEPTH, IDXS, MAXP)
ALL_PRINC = []
for t in ALL_TERMS:
    _, ps = t
    for p in ps:
        if p not in ALL_PRINC:
            ALL_PRINC.append(p)
# deeper principals (depth+1) to make isPTB / get_princ complete, but only
# single-principal terms to keep the catalogue tractable.
for t in enum_terms(DEPTH+1, IDXS, 1):
    _, ps = t
    for p in ps:
        if p not in ALL_PRINC:
            ALL_PRINC.append(p)

for p in ALL_PRINC:
    if dfree_BP(p):
        PRINC_MAP.setdefault(tuple(flatBP(p)), p)

TB_TERMS = [t for t in ALL_TERMS if in_TB(t) and t != Trm([])]
print(f"#TB nonempty terms={len(TB_TERMS)} #princ={len(ALL_PRINC)}")

def last_index(lst, x):
    idx = -1
    for i, e in enumerate(lst):
        if e == x:
            idx = i
    return idx

for kindname, pred in [("kind0", scb_kind0), ("kind1", scb_kind1)]:
    fail_len = 0; tot = 0
    fail_rn_suffix = 0; rn_checks = 0
    fail_lastocc = 0
    for t in TB_TERMS:
        ds = all_decomps(t, pred)
        if not ds:
            continue
        lens = set(len(s) for (s,c,b) in ds)
        tot += 1
        if len(lens) > 1:
            fail_len += 1
            if fail_len <= 5:
                print(f"FAIL {kindname} len(s) varies: t={t} lens={lens}")
                for (s,c,b) in ds:
                    print("   ", len(s), c)
        # check RightNodes-suffix + last-occurrence claims
        rnt = RightNodes_T(t)
        for (s,c,b) in ds:
            p = get_princ(c)
            if p is None:
                continue
            rnc = RN_princ(p)
            rn_checks += 1
            # claim: rnc is a suffix segment of rnt
            if rnt[len(rnt)-len(rnc):] != rnc:
                fail_rn_suffix += 1
                if fail_rn_suffix <= 5:
                    print(f"FAIL {kindname} rn-suffix: t={t} rnt={rnt} rnc={rnc}")
            # claim: cut s is the prefix up to the last Dsym(v0) in flatBT t, v0 = rnc[0]
            v0 = rnc[0]
            ft = flatBT(t)
            li = last_index(ft, Dsym(v0))
            if li != len(s):
                fail_lastocc += 1
                if fail_lastocc <= 5:
                    print(f"FAIL {kindname} lastocc: t={t} len(s)={len(s)} lastDsym(v0)={li} v0={v0}")
    print(f"{kindname}: len(s)-pinning {fail_len}/{tot} fail; "
          f"rn-suffix {fail_rn_suffix}/{rn_checks} fail; lastocc {fail_lastocc} fail")
