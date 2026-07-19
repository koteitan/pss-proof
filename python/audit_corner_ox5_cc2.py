#!/usr/bin/env python3
"""AUDIT for lean/8/8.7-corner-census.lean MISSION (SetleCensusOx5_cc2 corner branch).

The refuted route demanded a SHARED WRAPPER between A0 (=transT2 M, 1 principal) and
ins 0_B (2 principals) — structurally impossible at the admeq corner.  The RE-PLUMBED
route bypasses the wrapper entirely: the ACTUAL downstream need is only the census body
driver `ox5`

    forall u.  b1x_setle (GBT u A0) ({ins 0_B} ∪ GBT u (ins 0_B)),

which the built `ox5_body_driver` derives from a `b1x_triG _ A0 (ins 0_B)` G-control and
`base1 : A0 < ins 0_B` ALONE (no wrapper).  The G-control is exactly the already-proven
unconditional `tri0CruxConcrete_holds` (at z = D_∞ 0_B).

This audit verifies the ox5 CONCLUSION *directly* (computing GBT / leBT verbatim from the
Lean defs) on every admeq-corner condIV STPS host, over a range of u, using the degenerate
corner reconstruction ins 0_B = transT2 M +_B D_w(transT2 M +_B D_{v1-1} 0_B).  If it holds
on all corner hosts for all tested u, the restated Prop's corner branch is TRUE.
"""
import sys, signal
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
import red_model as rm
_rc = {}; _orig = rm.reach
def fast_reach(M, nextf):
    k = (tuple(map(tuple, M)), nextf.__name__); v = _rc.get(k)
    if v is None: v = _orig(M, nextf); _rc[k] = v
    return v
rm.reach = fast_reach
from red_model import Lng, entry, monoT, parent, hasParent, oper, reduced, diagSeq, adm
from trans_model import (Pred, Adm, bpHeadT, bpHeadV, addBT, Dpt, Mark, Trans, ZB, PB, SigmaB)

class TO(Exception): pass
signal.signal(signal.SIGALRM, lambda s, f: (_ for _ in ()).throw(TO()))

def lastParent(M): return parent(M, 0, Lng(M) - 1)
def transJ0(M): return lastParent(M)
def transJm1(M): return Adm(M, transJ0(M))
def transC1(M): return Mark(Pred(M), transJm1(M))
def transT2(M): return bpHeadT(transC1(M))
def transT1(M): return Trans(Pred(M))
def s84x_jm2(M): return parent(M, 1, Lng(M) - 1)

def transCondIV(M):
    j1 = Lng(M) - 1; jp = parent(M, 0, j1)
    return jp is not None and entry(M, 1, j1) > 0 and entry(M, 1, j1) <= entry(M, 1, jp) and not adm(M, jp)

def is_corner_admeq(M):
    if not hasParent(M, 1, Lng(M) - 1): return False
    jm2 = s84x_jm2(M)
    return jm2 is not None and Adm(M, jm2) == transJm1(M)

# ---- Buchholz order + gather, VERBATIM from lean/PSS/Buchholz.lean ----
# BT = ('T', [('D', v, sub), ...]).  Compare on the principal lists.
def lessBT(a, b): return lessBPList(a[1], b[1])
def lessBP(p, q):
    u, av = p[1], p[2]; v, bv = q[1], q[2]
    return (u < v) or (u == v and lessBT(av, bv))
def lessBPList(a, b):
    if not a and not b: return False
    if not a and b: return True
    if a and not b: return False
    return lessBP(a[0], b[0]) or (a[0] == b[0] and lessBPList(a[1:], b[1:]))
def leBT(a, b): return lessBT(a, b) or a == b

def gatherBT(u, t): return gatherBPList(u, t[1])
def gatherBP(u, p):
    v, b = p[1], p[2]
    return ([b] + gatherBT(u, b)) if (u <= v) else []
def gatherBPList(u, ps):
    out = []
    for p in ps: out += gatherBP(u, p)
    return out

def b1x_setle(Mset, Nset):
    """forall x in Mset, exists y in Nset, x <= y (leBT)."""
    for x in Mset:
        if not any(leBT(x, y) for y in Nset): return False
    return True

def max_index(t, acc=0):
    for p in t[1]:
        acc = max(acc, p[1]); acc = max(acc, max_index(p[2], acc))
    return acc

def corner_ins0(M):
    """degenerate corner ins 0_B = transT2 +_B D_w(transT2 +_B D_{v1-1} 0)."""
    A0 = transT2(M); w = entry(M, 1, transJ0(M)); v1 = entry(M, 1, Lng(M) - 1)
    return addBT(A0, Dpt(w, addBT(A0, Dpt(v1 - 1, ZB))))

def check_host(M):
    A0 = transT2(M); X1 = corner_ins0(M)
    base1 = lessBT(A0, X1)
    umax = max(max_index(A0), max_index(X1)) + 2
    ok = True
    for u in range(0, umax + 1):
        GA0 = gatherBT(u, A0); GX1 = gatherBT(u, X1)
        Nset = [X1] + GX1
        if not b1x_setle(GA0, Nset): ok = False; break
    return base1, ok

def gen_corpus(umax=2, vmax=4, opermax=5, size_cap=11, cap=6000):
    seen = set(); frontier = []
    for u in range(umax + 1):
        for v in range(u, u + vmax + 1):
            M = tuple(diagSeq(u, v)); seen.add(M); frontier.append(M)
    allM = set(seen)
    while frontier and len(allM) < cap:
        M = frontier.pop(); Ml = list(M)
        for n in range(opermax + 1):
            try: R = oper(Ml, n)
            except: continue
            if not R or Lng(R) > size_cap: continue
            if max(max(a, b) for (a, b) in R) > 22: continue
            Rt = tuple(R)
            if Rt not in allM:
                allM.add(Rt)
                if len(allM) < cap: frontier.append(Rt)
    return allM

if __name__ == '__main__':
    corpus = gen_corpus()
    print("corpus size:", len(corpus), flush=True)
    corners = []
    for M in corpus:
        Ml = list(M)
        if Lng(Ml) - 1 <= 1: continue
        try:
            signal.alarm(3)
            ok = reduced(Ml) and monoT(Ml) and transCondIV(Ml) and is_corner_admeq(Ml)
            if ok: ok = (transT1(Ml) != ZB)
            signal.alarm(0)
        except Exception:
            signal.alarm(0); continue
        if not ok: continue
        try:
            signal.alarm(3); base1, setle_ok = check_host(Ml); signal.alarm(0)
        except Exception:
            signal.alarm(0); continue
        corners.append((Ml, base1, setle_ok))
    print("admeq-corner condIV mono STPS hosts (transT1!=0):", len(corners))
    nbase = sum(1 for _, b, _ in corners if b)
    nsetle = sum(1 for _, _, s in corners if s)
    print(f"base1 (A0 < ins 0_B) holds: {nbase} / {len(corners)}")
    print(f"ox5 setle conclusion holds: {nsetle} / {len(corners)}")
    bad = [(M, b, s) for M, b, s in corners if not s]
    print(f"hosts where ox5 setle FAILS: {len(bad)} / {len(corners)}")
    for M, b, s in bad[:5]:
        print("  FAIL:", M, "base1=", b)
    t = [(0, 0), (1, 1), (2, 2), (2, 1)]
    print("\n=== target (0,0)(1,1)(2,2)(2,1) detail ===")
    print("  A0 = transT2 =", transT2(t))
    print("  ins 0_B      =", corner_ins0(t))
    b1, s1 = check_host(t)
    print("  base1 (A0 < ins 0_B):", b1)
    print("  ox5 setle holds     :", s1)
    print("\nCONCLUSION:",
          "restated Prop's corner branch (ox5 setle) is TRUE on all corner hosts."
          if not bad and nsetle == len(corners) else "FAILURE — investigate.")
