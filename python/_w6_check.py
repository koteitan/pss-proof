#!/usr/bin/env python3
"""Empirical truth-check of p_8_2_condIIIV_terminal_slice_Trans (§8.2, article 3314).
Scratch; not committed."""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng, entry, P, monoT, seg, TrMax, Br, FirstNodes, Joints,
                       Red, reduced)
from trans_model import Trans, Dpt, ZB, addBT

def descending(Q):
    n = len(Q)
    for J0 in range(n):
        for J1 in range(J0, n):
            a0 = entry(Q[J0],0,0); a1 = entry(Q[J1],0,0)
            if not (a0 >= a1): return False
            if a0 == a1 and not (entry(Q[J0],1,0) >= entry(Q[J1],1,0)):
                return False
    return True

def LastStep(M):
    Br_M = Br(M)
    if not Br_M: return 0
    J1 = len(Br_M)-1
    if entry(Br_M[J1],0,0) == entry(Br_M[J1],1,0):
        return J1
    cands = [J for J in range(len(Br_M))
             if entry(Br_M[J1],0,0)==entry(Br_M[J],0,0)
             and entry(Br_M[J],1,0) < entry(Br_M[J],0,0)]
    return min(cands)

def in_DT_PS(M):
    # cheap filters first
    if not monoT(M): return False
    if not descending(Br(M)): return False
    return reduced(M)

def gen(maxlen, maxval):
    # standard-style: M[0]=(0,0), and require it be a candidate quickly
    for L in range(2, maxlen+1):
        for vals in itertools.product(range(maxval+1), repeat=2*(L-1)):
            M = [(0,0)] + [(vals[2*i], vals[2*i+1]) for i in range(L-1)]
            yield M

def check(M):
    """Return None if hypotheses fail, else (ok, info)."""
    if not in_DT_PS(M): return None
    BrM = Br(M)
    if not BrM: return None  # Br M != []
    j1 = Lng(M)-1
    J1 = len(BrM)-1
    j0p = Joints(M)[J1]
    j1p = FirstNodes(M)[J1]
    if not (0 < j0p < TrMax(M)): return None
    if not (entry(M,0,j1p) > entry(M,1,j1p)): return None
    # the proposition
    J0 = LastStep(M)
    m1 = FirstNodes(M)[J0]-1
    N  = seg(M,0,m1)
    Np = seg(M,j0p,m1)
    Mp = seg(M,j0p,j1)
    e10  = entry(M,1,0)
    e1j0 = entry(M,1,j0p)
    TN  = Trans(N); TNp = Trans(Np); TMp = Trans(Mp); TM = Trans(M)
    # (1) Trans N = D_{e10} t1  -> t1 = bpHeadT if single-principal headed by e10
    # extract t1 from (1):
    if len(TN[1]) != 1 or TN[1][0][1] != e10:
        return (False, f"(1) shape: TN={TN} e10={e10}")
    t1 = ('T', [TN[1][0][2][1][k] for k in range(len(TN[1][0][2][1]))]) if False else TN[1][0][2]
    # (2) Trans N' = D_{e1j0} t1
    if TNp != Dpt(e1j0, t1):
        return (False, f"(2) fail TNp={TNp} expect D_{e1j0}({t1})")
    # (3) Trans M' = D_{e1j0}(t1 + t2), t2!=0
    if len(TMp[1]) != 1 or TMp[1][0][1] != e1j0:
        return (False, f"(3) shape TMp={TMp}")
    body = TMp[1][0][2]  # = t1 + t2
    # body must extend t1 on the left: body[1] starts with t1[1]
    if body[1][:len(t1[1])] != t1[1]:
        return (False, f"(3) t1 not prefix of body: t1={t1} body={body}")
    t2 = ('T', body[1][len(t1[1]):])
    if t2 == ZB:
        return (False, f"(3) t2 == 0: TMp={TMp} t1={t1}")
    # (4) Trans M = D_{e10}(t1 + D_{e1j0}(t1+t2))
    expect4 = Dpt(e10, addBT(t1, Dpt(e1j0, addBT(t1, t2))))
    if TM != expect4:
        return (False, f"(4) fail TM={TM} expect={expect4}")
    return (True, "ok")

def main():
    maxlen = int(sys.argv[1]) if len(sys.argv)>1 else 6
    maxval = int(sys.argv[2]) if len(sys.argv)>2 else 3
    tot=0; passed=0; fails=[]
    for M in gen(maxlen, maxval):
        r = check(M)
        if r is None: continue
        tot+=1
        ok,info = r
        if ok: passed+=1
        else: fails.append((M,info))
    print(f"DT_PS cases matching hyps: {tot}, pass={passed}, fail={len(fails)}")
    for M,info in fails[:20]:
        print("FAIL", M, "::", info)

if __name__=='__main__':
    main()
