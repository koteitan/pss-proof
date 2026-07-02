#!/usr/bin/env python3
"""Scratch: find the termination measure for the xseq tower (operB ([].4)(ii)).

Isabelle recursion (pss_paper.thy 739-777):
  operB (Trm [DB v b]) z, b != 0, db = domB b:
     db = {0}        -> mult (D_v (operB b 0)) (z+1)
     exists u. v<=u and db = TBv u   ->  D_v (xseq b u_idx z)       [([].4)(ii)]
     else (db = N or db = TBv u with v>u)  ->  D_v (operB b z)      [([].4)(iii)/(i)]
  operB (Trm [p,q,...]) z -> add (butlast) (operB (Trm [last]) z)   [([].5)]
  xseq b u 0 = D_u 0
  xseq b u (Suc j) = operB b (D_u (xseq b u j))

WAIT: the ([].4)(ii) GUARD in operB is `exists u. v<=u and db=TBv u`.
The task says the genuine tower is db=TBv u with v>u.  Let me re-check.

Actually looking at python dom: ([].4)(ii) fires when dom(b)=T_u and v<=u -> dom(a)=N.
([].4)(iii) fires when dom(b)=T_u and v>u -> dom(a)=T_u.

And in operB (Isabelle), the SECOND branch (xseq) fires when v<=u & db=TBv u.
So the xseq tower fires when domB b = TBv u and v <= u.  (The task statement's
'v>u' refers to dom(a)=TBv u being a Tv-domain at the OUTER level, i.e. the
principal a=D_v b being a kind1 principal -- need to disentangle.)

The point: xseq b u i recurses operB b (D_u (xseq b u (i-1))).  We need termination:
each operB call is on argument b (FIXED), with the SECOND argument z growing.
operB's recursion on b: b is FIXED across the tower.  operB b z' for various z'.

Let me just SIMULATE and confirm the tower terminates, and measure recursion depth.
"""
import math, sys
sys.setrecursionlimit(100000)
INF = math.inf
ZERO = []
def D(v,a): return ('D',v,a)
def is_zero(a): return a==[]

# operB / xseq following the ISABELLE definition (A23 applied)
CALLS = {'operB':0, 'xseq':0, 'domB':0}

def domB(a):
    CALLS['domB'] += 1
    if is_zero(a): return ('empty',)
    if len(a)>=2: return domB([a[-1]])
    _,v,b = a[0]
    if is_zero(b):
        if v==0: return ('zero',)
        if v==INF: return ('N',)
        return ('Tv', v-1)
    db = domB(b)
    if db==('zero',): return ('N',)
    if db==('N',): return ('N',)
    if db[0]=='Tv':
        u = db[1]
        if v <= u: return ('N',)          # ([].4)(ii)
        return ('Tv', u)                  # ([].4)(iii)
    return ('empty',)

def numNat(z): return len(z)  # z is a nat term 1*n

def operB(a, z, depth=0):
    CALLS['operB'] += 1
    if is_zero(a): return ZERO
    if len(a)>=2:
        return [a[-1]] and (a[:-1] + operB([a[-1]], z, depth+1))
    _,v,b = a[0]
    if is_zero(b):
        if v==0: return ZERO
        if v==INF: return [D(numNat(z)+1, ZERO)]
        return z
    db = domB(b)
    if db==('zero',):  # db={0}
        n = numNat(z)
        # mult (D_v (operB b 0)) (n+1)
        return mul([D(v, operB(b, ZERO, depth+1))], n+1)
    if db[0]=='Tv':
        u = db[1]
        if v <= u:                       # xseq branch ([].4)(ii)
            return [D(v, xseq(b, u, numNat(z), depth+1))]
    # else
    return [D(v, operB(b, z, depth+1))]

def xseq(b, u, i, depth=0):
    CALLS['xseq'] += 1
    if i==0: return [D(u, ZERO)]
    return operB(b, [D(u, xseq(b, u, i-1, depth+1))], depth+1)

def mul(a,n):
    r=[]
    for _ in range(n): r=r+a
    return r

def fmt(a):
    if is_zero(a): return "0"
    def fp(p):
        _,v,b=p
        idx="w" if v==INF else str(v)
        return f"D_{idx}({fmt(b)})"
    return "("+",".join(fp(p) for p in a)+")" if len(a)>1 else fp(a[0])

# Find a body b with domB b = TBv u and a v<=u so the xseq branch fires.
# Simplest: b = D_2 0, domB(b) = T_1 (Tv,1). Then a = D_v (D_2 0) with v<=1.
# v=0: a = D_0 (D_2 0).  domB(a): dom(b)=T_1, v=0<=1 -> N. xseq branch fires.
print("=== Test 1: a = D_0 (D_2 0), z = n ===")
b = [D(2,ZERO)]
print("domB(b=D_2 0) =", domB(b), "(expect (Tv,1))")
for n in range(5):
    CALLS.update({'operB':0,'xseq':0,'domB':0})
    z = [D(0,ZERO)]*n
    r = operB([D(0,b)], z)
    print(f"  operB(D_0(D_2 0), {n}) = {fmt(r)}   calls={dict(CALLS)}")

print("\n=== Test 2: xseq directly: xseq (D_2 0) 1 i ===")
for i in range(6):
    CALLS.update({'operB':0,'xseq':0,'domB':0})
    r = xseq([D(2,ZERO)], 1, i)
    print(f"  xseq(D_2 0, u=1, i={i}) = {fmt(r)}   calls={dict(CALLS)}")

print("\n=== Test 3: deeper body b = D_3 (D_2 0), find a tower ===")
b3 = [D(3, [D(2,ZERO)])]
print("domB(D_3(D_2 0)) =", domB(b3))
# dom(D_2 0)=T_1, v=3>1 -> dom = T_1. So D_3(D_2 0) has dom T_1.
# a = D_v(b3) with v<=1: a=D_0(D_3(D_2 0)) or D_1(...). xseq fires.
for i in range(5):
    CALLS.update({'operB':0,'xseq':0,'domB':0})
    r = xseq(b3, 1, i)
    print(f"  xseq(D_3(D_2 0), u=1, i={i}) = {fmt(r)[:80]}   calls={dict(CALLS)}")

print("\n=== Test 4: nested xseq-within-operB tower ===")
# Need a body b such that operB b z' itself triggers the xseq branch.
# That requires b = D_v c with domB c = Tv u and v <= u (then operB b fires xseq).
# But ALSO domB b must be Tv u' for the OUTER xseq to fire on a=D_w b.
# domB(D_v c) with dom(c)=Tv u, v<=u -> dom = N (([].4)(ii)), NOT Tv. So domB b = N.
# Then for outer a=D_w b: domB(b)=N -> operB a uses else branch (iii): D_w (operB b z). NO xseq.
# So nesting xseq inside xseq requires domB b = Tv, which for single principal needs v>u.
# Conclusion: within ONE operB b z evaluation, the xseq branch fires at most for the
# OUTERMOST principal whose dom(body)=Tv & v<=u; deeper recursion is else/iii (no new xseq)
# OR db={0} (mult).  Let me verify operB b z never has TWO nested xseq for single-spine b.
import itertools
def count_xseq_in_operB(a, z, seen_depth=0):
    """count how deep xseq calls nest starting from operB a z (single spine)."""
    if is_zero(a): return 0
    if len(a)>=2: return count_xseq_in_operB([a[-1]], z)
    _,v,b = a[0]
    if is_zero(b): return 0
    db = domB(b)
    if db==('zero',): return 0  # mult, operB b 0 -> recurse but body smaller
    if db[0]=='Tv' and v<=db[1]:
        return 1  # xseq fires; xseq then calls operB b (...) again = SAME b -> could renest
    return count_xseq_in_operB(b, z)

# brute test: build all single-spine BTs up to depth 4 with indices 0..3, check tower terminates
def spines(depth, maxv=3):
    if depth==0:
        yield ZERO
        return
    for v in range(maxv+1):
        for sub in spines(depth-1, maxv):
            yield [D(v, sub)]

bad=0; tested=0
for b in spines(4, 3):
    db = domB(b)
    if db[0] != 'Tv': continue
    u = db[1]
    for v in range(u+1):  # v<=u so a=D_v b triggers xseq on body b... wait a's xseq is on b
        # outer a = D_v b, domB(b)=Tv u, v<=u -> xseq branch
        for i in range(8):
            CALLS.update({'operB':0,'xseq':0,'domB':0})
            try:
                r = xseq(b, u, i)
                tested += 1
            except RecursionError:
                bad += 1
                print("NONTERM:", fmt(b), "u=",u,"i=",i)
                break
print(f"Test4: tested={tested} towers, nonterminating={bad}")
