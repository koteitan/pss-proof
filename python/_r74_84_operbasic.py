#!/usr/bin/env python3
"""r74: empirical check of p_8_4_oper_basic parts (2) and (3) under the CORRECTED operB.

operB is taken from buchholz.py (the VETTED, corrected footnote-[30] rule);
_r15_vx_lib.operB is the OLD transposed rule and is deliberately NOT used.

Hosts: M in ST_PS (built by iterating oper from diagSeq), monoT, hasParent M 1 j1,
       j1 = Lng M - 1 > 1, and (condIII M or condIV M).

Part (2):  operB (Trans M) (numBT (n-1)) == Trans ( ([1]^^(j1-1-jm2)) (M[n+1]) ),  jm2 = parent M 1 j1
Part (3):  exists (s,c1,c2,b), c1,c2 principal, c1<c2,
             flatBT(Trans (M[n]))            = s @ flatBP c1 @ b
             flatBT(operB (Trans M) (numBT n)) = s @ flatBP c2 @ b
also reports the weak consequence  Trans(M[n]) < operB(Trans M)(numBT n).
"""
import sys, time, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4c/python')
import red_model as rm
import trans_model as tm
from red_model import Lng, entry, parent, oper, diagSeq, monoT, hasParent
from trans_model import Trans, adm, flatBT, PB, ZB
import buchholz as bu
from _r15_vx_lib import guarded, SKIP   # ONLY the timeout guard; NOT its stale operB

# ---- bridge between trans_model BT (('T',[('D',v,t)])) and buchholz terms (lists) ----
def to_b(t):
    return [('D', p[1], to_b(p[2])) for p in t[1]]
def to_t(a):
    return ('T', [('D', v, to_t(b)) for (_, v, b) in a])
def operB(t, n):
    """t[n] with n a nat, computed by the CORRECTED buchholz.bracket."""
    return to_t(bu.bracket(to_b(t), bu.nat(n)))
def lessBT(a, b):
    return bu.lt_term(to_b(a), to_b(b))

def condIII(M):
    j1 = Lng(M)-1; jp = parent(M, 0, j1)
    return entry(M,1,j1) > 0 and entry(M,1,jp) >= entry(M,1,j1) and adm(M, jp)
def condIV(M):
    j1 = Lng(M)-1; jp = parent(M, 0, j1)
    return entry(M,1,j1) > 0 and entry(M,1,jp) >= entry(M,1,j1) and not adm(M, jp)

def op1pow(M, k):
    for _ in range(k): M = oper(M, 1)
    return M

# ---- scb: enumerate (s, cp, b) with flatBT t = s @ flatBP cp @ b, cp principal ----
from trans_model import flatBP
def _wins_p(p, pre, suf, out):
    out.append((tuple(pre), ('T', [p]), tuple(suf)))
    _wins_t(p[2], pre + [('D', p[1])], suf, out)
def _wins_t(t, pre, suf, out):
    ps = t[1]
    if not ps: return
    if len(ps) == 1:
        _wins_p(ps[0], pre, suf, out); return
    pieces = [flatBP(p) for p in ps]
    for i, p in enumerate(ps):
        s = pre + ['(']
        for j in range(i): s = s + pieces[j] + [',']
        b = []
        for j in range(i+1, len(ps)): b = b + [','] + pieces[j]
        b = b + [')']
        _wins_p(p, s, b + suf, out)
def principal_windows(t):
    out = []
    _wins_t(t, [], [], out)
    return out

def part3(M, n):
    t1 = Trans(oper(M, n))
    t2 = operB(Trans(M), n)
    W1 = principal_windows(t1)
    W2 = {(s, b): cp for (s, cp, b) in principal_windows(t2)}
    for (s, c1, b) in W1:
        c2 = W2.get((s, b))
        if c2 is None: continue
        if len(PB(c1)) == 1 and len(PB(c2)) == 1 and lessBT(c1, c2):
            return True
    return False

def mine(tmax, rng, want):
    t0 = time.time(); seen = set(); out = []
    while time.time()-t0 < tmax and len(out) < want:
        u = rng.randrange(0, 5); v = u + rng.randrange(1, 6)
        M = diagSeq(u, v)
        for _ in range(rng.randrange(4, 26)):
            if time.time()-t0 > tmax: break
            k = rng.choice((1,1,1,2,2,2,3,4))
            try: M2 = oper(M, k)
            except Exception: break
            if not M2 or M2 == M or Lng(M2) > 14: break
            M = M2
            key = tuple(M)
            if key in seen: continue
            seen.add(key)
            j1 = Lng(M)-1
            if j1 <= 1 or not monoT(M): continue
            if not hasParent(M, 1, j1): continue
            if not (condIII(M) or condIV(M)): continue
            out.append(list(M))
    return [list(t) for t in dict.fromkeys(tuple(m) for m in out)]

def main():
    tmine = float(sys.argv[1]) if len(sys.argv) > 1 else 60
    seed  = int(sys.argv[2]) if len(sys.argv) > 2 else 4242
    rng = random.Random(seed)
    hosts = mine(tmine, rng, 30)
    print('mined condIII/IV hosts (hasParent row1, j1>1):', len(hosts), flush=True)
    st = {'p2_ok':0,'p2_bad':0,'p3_ok':0,'p3_bad':0,'weak_ok':0,'weak_bad':0,'skip':0}
    cex2 = []; cex3 = []
    for hi, M in enumerate(hosts):
        j1 = Lng(M)-1; jm2 = parent(M, 1, j1)
        kind = 'III' if condIII(M) else 'IV'
        print('host', hi, 'Lng', Lng(M), kind, 'jm2', jm2, 'j1', j1, flush=True)
        for n in (1,2):
            try:
                Mn  = guarded(oper, M, n, budget=8)
                Mn1 = guarded(oper, M, n+1, budget=8)
                TM  = guarded(Trans, M, budget=20)
                if Mn is SKIP or Mn1 is SKIP or TM is SKIP:
                    st['skip'] += 1; continue
                # part (2)
                it2 = j1 - 1 - jm2 if j1 - 1 >= jm2 else None
                if it2 is None:
                    st['skip'] += 1
                else:
                    lhs = guarded(operB, TM, n-1, budget=20)
                    L = guarded(op1pow, Mn1, it2, budget=8)
                    rhs = SKIP if L is SKIP else guarded(Trans, L, budget=20)
                    if lhs is SKIP or rhs is SKIP:
                        st['skip'] += 1; continue
                    if lhs == rhs: st['p2_ok'] += 1
                    else:
                        st['p2_bad'] += 1
                        if len(cex2) < 3: cex2.append((list(M), n, kind, jm2, j1))
                # part (3)
                p3 = guarded(part3, M, n, budget=30)
                if p3 is SKIP: st['skip'] += 1
                elif p3: st['p3_ok'] += 1
                else:
                    st['p3_bad'] += 1
                    if len(cex3) < 3: cex3.append((list(M), n, kind))
                # weak consequence
                TMn = guarded(Trans, Mn, budget=20); OP = guarded(operB, TM, n, budget=20)
                if TMn is SKIP or OP is SKIP: st['skip'] += 1
                elif lessBT(TMn, OP): st['weak_ok'] += 1
                else: st['weak_bad'] += 1
            except Exception as e:
                st['skip'] += 1
    print('STATS', st, flush=True)
    for c in cex2: print('  CEX(2):', c, flush=True)
    for c in cex3: print('  CEX(3):', c, flush=True)

main()
