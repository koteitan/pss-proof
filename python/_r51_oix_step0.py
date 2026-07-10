#!/usr/bin/env python3
"""r51-OIX STEP-0: validate the two claims behind the oix_ OTint route.

PART A (pure BT): the SANDWICH TRANSPORT claim.
  Host context: an OT term tHi with a rightmost-spine principal cHi = D_v(body)
  at path p.  Premises:
    - tLo := tHi[p := D_v bodyLo] is OT           (lo donor, same head)
    - c'  := D_v body'  with bodyLo <= body' <= body (term order)
    - isOT_BP c' (i.e. [c'] in OT)
    - setle: for all u: every x in G(u,[c']) is <= some y in G(u,[cLo])
  Claim: t' := tHi[p := c'] is OT.
  (r35 finding 2 says WITHOUT the setle/lo premises this is false; we test that
   the premise set above repairs it, and count NONTRIVIAL instances where
   G(u,[c']) is not a subset of G(u,[cLo]) for some u.)

PART B (genuine ST_PS, condV-adm): the tower assembly.
  For genuine condV-adm hosts M (mono, Lng-1>1), e=M[1,j0], v1=M[1,j1]:
  find the right-spine path in Trans(M[1]) whose principal is D_e(t2) such that
  substituting D_e(V_k), V_k = block^k(t2), block(x) = t2 + [D_e x], reproduces
  Trans(M[k+1]) for k=1..3, and the operB towers W_k = block^k([D_e 0]) give
  operB(Trans M, k).  Then check the transport premises:
    lo/hi OT, W_k <= V_k <= W_(k+1), isOT_BP(D_e V_k),
    setle(G(u,[D_e V_k]) vs G(u,[D_e W_k])),
    newOT parts: G(e,t2) < t2, HB: components of t2 >= D_v1 0, t2lb: D_e 0 < t2.
"""
import sys, time, signal, random, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import (Lng, entry, parent, hasParent, oper, seg, diagSeq,
                       monoT, zeroT)
from trans_model import Trans, Pred, adm, Adm
import buchholz as bu

INF = float('inf')
class TimeoutErr(Exception): pass
def _handler(s, f): raise TimeoutErr()
signal.signal(signal.SIGALRM, _handler)
def safe(f, *a, budget=4):
    signal.alarm(budget)
    try:
        r = f(*a); signal.alarm(0); return r
    except (TimeoutErr, RecursionError, AssertionError, ValueError, IndexError, KeyError):
        signal.alarm(0); return None

def D(v, a): return ('D', v, a)
ZERO = []
def bucOf(t): return [('D', p[1], bucOf(p[2])) for p in t[1]]
def isOTb(a): return bu.in_OT(a) and bu.in_TB(a)
def lt(a,b): return bu.lt_term(a,b)
def le(a,b): return bu.le_term(a,b)

def G(u, a): return bu.G(u, a)

def all_heads(a, acc=None):
    if acc is None: acc = set()
    for p in a:
        acc.add(p[1]); all_heads(p[2], acc)
    return acc

def setle(A, B):
    """every x in A is <= some y in B (x,y BT terms; A,B lists of terms)."""
    for x in A:
        if not any(le(x, y) for y in B):
            return False, x
    return True, None

def subsetG(A, B):
    return all(any(x == y for y in B) for x in A)

# ---------- rightmost-spine paths ----------
def rpaths(a):
    paths = []; cur = a; path = []
    while cur:
        i = len(cur)-1
        path = path + [i]
        paths.append(list(path))
        cur = cur[i][2]
    return paths

def get_at(a, path):
    cur = a
    for i in path[:-1]: cur = cur[i][2]
    return cur[path[-1]]

def set_at(a, path, newp):
    if len(path) == 1:
        return a[:path[-1]] + [newp] + a[path[-1]+1:]
    i = path[0]; p = a[i]
    return a[:i] + [D(p[1], set_at(p[2], path[1:], newp))] + a[i+1:]

# ---------- PART A ----------
def gen_OT(rng, maxv=3, depth=3):
    if depth == 0: return ZERO
    n = rng.randrange(0, 3)
    ps = []
    for _ in range(n):
        v = rng.randrange(0, maxv+1)
        b = gen_OT(rng, maxv, depth-1)
        p = D(v, b)
        if not bu.in_OT([p]): continue
        if ps and not le([p], [ps[-1]]): continue
        ps.append(p)
    return ps if bu.in_OT(ps) else ZERO

def partA(trials=60000, seed=7):
    rng = random.Random(seed)
    tot = nontriv = 0; fails = []
    prem_hold = 0
    for _ in range(trials):
        # host
        body0 = gen_OT(rng, 3, 3)
        v = rng.randrange(0, 4)
        host_ps = gen_OT(rng, 3, 2)
        cand = D(v, body0)
        # build a host OT term with cand on the rightmost spine, wrapped
        w = rng.randrange(0, 4)
        tHi = [D(w, host_ps + [cand])] if bu.in_OT([D(w, host_ps + [cand])]) else None
        if tHi is None or not isOTb(tHi): continue
        # sometimes wrap once more
        if rng.random() < 0.5:
            w2 = rng.randrange(0, 4)
            t2c = [D(w2, gen_OT(rng, 3, 2) + tHi)]
            if isOTb(t2c): tHi = t2c
        ps_ = rpaths(tHi)
        if len(ps_) < 2: continue
        path = ps_[rng.randrange(1, len(ps_))]
        cHi = get_at(tHi, path)
        vh, bodyHi = cHi[1], cHi[2]
        # candidate lo / mid bodies
        bodyLo = gen_OT(rng, 3, 2)
        bodyMid = gen_OT(rng, 3, 3)
        if not (le(bodyLo, bodyMid) and le(bodyMid, bodyHi)): continue
        cLo = D(vh, bodyLo); cMid = D(vh, bodyMid)
        tLo = set_at(tHi, path, cLo)
        if not isOTb(tLo): continue
        if not bu.in_OT([cMid]): continue
        # setle premise over all u
        heads = all_heads(tHi) | all_heads([cMid]) | {0}
        ok_set = True
        strict = False
        for u in sorted(heads | {h+1 for h in heads}):
            gm = G(u, [cMid]); gl = G(u, [cLo])
            ok, _x = setle(gm, gl)
            if not ok: ok_set = False; break
            if not subsetG(gm, gl): strict = True
        if not ok_set: continue
        prem_hold += 1
        if strict: nontriv += 1
        t_ = set_at(tHi, path, cMid)
        tot += 1
        if not isOTb(t_):
            fails.append((tHi, path, cLo, cMid))
            if len(fails) >= 3: break
    print("PART A: premises held on %d cases (%d nontrivial-setle); conclusion failed %d"
          % (tot, nontriv, len(fails)))
    for f in fails[:3]:
        print("  CEX: host=%s path=%s cLo=%s cMid=%s" % (bu.fmt(f[0]), f[1], bu.fmt([f[2]]), bu.fmt([f[3]])))
    return len(fails) == 0

# ---------- PART B ----------
def condV(M):
    j1 = Lng(M)-1
    if j1 < 1 or not hasParent(M, 0, j1): return False
    jp = parent(M, 0, j1)
    return entry(M,1,j1) > 0 and entry(M,1,jp) < entry(M,1,j1) and entry(M,1,jp) > 0

def gen_ST(rng, tmax, maxlen=24, nmax=4, steps=14):
    t0 = time.time(); seen = set()
    starts = [diagSeq(u, u+d) for u in range(0,5) for d in range(1,6)]
    starts += [[(0,0),(1,1),(2,2),(3,1),(4,2),(4,2)],
               [(0,0),(1,1),(2,2),(3,1),(4,2)],
               [(0,0),(1,1),(2,2),(3,3),(4,1),(5,2)]]
    rng.shuffle(starts); idx = 0
    while time.time()-t0 < tmax:
        if idx < len(starts): M = starts[idx]; idx += 1
        else:
            u = rng.randrange(0,5); M = diagSeq(u, u+rng.randrange(1,6))
        for _ in range(steps):
            key = tuple(M)
            if key not in seen and 1 < Lng(M) <= maxlen:
                seen.add(key); yield M
            M2 = safe(oper, M, rng.randrange(1, nmax+1), budget=1)
            if M2 is None or M2 == M or Lng(M2) > maxlen*3: break
            M = M2

def tower(t2, e, k, base=None):
    x = t2 if base is None else base
    for _ in range(k):
        x = t2 + [D(e, x)]
    return x

def partB(tmax=90, seed=5):
    rng = random.Random(seed)
    hosts = 0; okhosts = 0
    fail = {k: 0 for k in ['align','lo','ord','setle','newOT','G_t2','HB','t2lb','final','loOT','hiOT','descP']}
    examples = []
    t0 = time.time()
    for M in gen_ST(rng, tmax):
        if time.time()-t0 > tmax: break
        j1 = Lng(M)-1
        if j1 <= 1 or not monoT(M): continue
        if not condV(M): continue
        jp = parent(M,0,j1)
        if not adm(M, jp): continue
        hosts += 1
        e = entry(M,1,jp); v1 = entry(M,1,j1)
        TM = safe(Trans, M, budget=5)
        M1 = safe(oper, M, 1, budget=2)
        if TM is None or M1 is None: continue
        A1 = safe(Trans, M1, budget=5)
        if A1 is None: continue
        TMb = bucOf(TM); A1b = bucOf(A1)
        A = {}
        bad = False
        for k in (2,3,4):
            Mk = safe(oper, M, k, budget=3)
            Tk = safe(Trans, Mk, budget=6) if Mk else None
            if Tk is None: bad = True; break
            A[k] = bucOf(Tk)
        if bad: continue
        # find the aligned path in A1b
        found = None
        for path in rpaths(A1b):
            p = get_at(A1b, path)
            if p[1] != e: continue
            t2 = p[2]
            ok = all(set_at(A1b, path, D(e, tower(t2, e, k))) == A[k+1] for k in (1,2,3))
            if ok: found = (path, t2); break
        if found is None:
            fail['align'] += 1
            if len(examples) < 2: examples.append(('align', M))
            continue
        path, t2 = found
        # operB towers at same path
        loOK = True
        for k in (1,2,3):
            LOk = safe(bu.bracket, TMb, bu.nat(k), budget=3)
            Wk = tower(t2, e, k, base=[D(e, ZERO)] )
            # NOTE: W_k = block^k(D_e 0): base [D(e,ZERO)], k blocks
            if LOk != set_at(A1b, path, D(e, Wk)):
                loOK = False; break
        if not loOK:
            fail['lo'] += 1
            if len(examples) < 4: examples.append(('lo', M))
            continue
        okhosts += 1
        for k in (1,2,3):
            Vk = tower(t2, e, k)
            Wk = tower(t2, e, k, base=[D(e, ZERO)])
            Wk1 = tower(t2, e, k+1, base=[D(e, ZERO)])
            if not (le(Wk, Vk) and le(Vk, Wk1)): fail['ord'] += 1
            heads = all_heads(TMb) | {0, e, v1}
            for u in sorted(heads):
                # BODY-level setle: G(u, V_k) dominated by G(u, W_k)
                ok, x = setle(G(u, Vk), G(u, Wk))
                if not ok:
                    fail['setle'] += 1
                    if len(examples) < 6: examples.append(('setle', M, k, u, repr(x)))
                    break
                # top insert handled separately: V_k < t2 + [D_e V_k] (tower-mono chain)
                if not lt(Vk, t2 + [D(e, Vk)]): fail['ord'] += 1
            if not bu.in_OT([D(e, Vk)]): fail['newOT'] += 1
            LOk = safe(bu.bracket, TMb, bu.nat(k), budget=3)
            HIk = safe(bu.bracket, TMb, bu.nat(k+1), budget=3)
            if LOk is None or not isOTb(LOk): fail['loOT'] += 1
            if HIk is None or not isOTb(HIk): fail['hiOT'] += 1
            if set_at(A1b, path, D(e, Vk)) != A[k+1] or not isOTb(A[k+1]): fail['final'] += 1
        # newOT ingredient facts
        ok, x = setle(G(e, t2), [])
        gt2 = G(e, t2)
        if not all(lt(x, t2) for x in gt2): fail['G_t2'] += 1
        if not all(le([D(v1, ZERO)], [c]) for c in t2): fail['HB'] += 1
        if not lt([D(e, ZERO)], t2): fail['t2lb'] += 1
        # descP-last: [D_e X] < [D_v1 0] (heads e < v1)
        if not lt([D(e, tower(t2,e,2))], [D(v1, ZERO)]): fail['descP'] += 1
    print("PART B: condV-adm hosts=%d aligned-and-loOK=%d" % (hosts, okhosts))
    print("  failures:", {k:v for k,v in fail.items() if v})
    for ex in examples[:6]: print("   ", ex)
    return all(v == 0 for v in fail.values()) and okhosts > 0

if __name__ == '__main__':
    a = partA()
    b = partB(tmax=int(sys.argv[1]) if len(sys.argv) > 1 else 90)
    print("STEP-0 RESULT: partA=%s partB=%s" % (a, b))
