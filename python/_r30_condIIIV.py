#!/usr/bin/env python3
# r30 CONDIIIV: validate p_8_2_condIIIV_terminal_slice_Trans on genuine DT_PS
# hosts, AND validate the not-leftDj0 guard for c2sx.
import sys, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, monoT, reduced, seg, parent, Adm, adm, nadm,
                       oper, diagSeq, le0, leR, Br, FirstNodes, Joints, Red,
                       hasParent, fmt, TrMax, Pred, is_standard)
import trans_model as tm
from trans_model import (Dpt, ZB, bpHeadT, bpHeadV, addBT, PB, SigmaB, flatBT,
                         unflatBT, Trans, Mark)

def pr(*a): print(*a, flush=True)

def is_reduced(M): return Red(list(M)) == list(M)

def descending(bs):
    for J0 in range(len(bs)):
        for J1 in range(J0, len(bs)):
            a0, b0 = bs[J0][0]; a1, b1 = bs[J1][0]
            if not (a0 >= a1 and (a0 != a1 or b0 >= b1)): return False
    return True

def in_DT_PS(M):
    return is_reduced(M) and monoT(M) and descending(Br(M))

def LastStep(M):
    b = Br(M)
    if not b: return 0
    J1 = len(b)-1
    lastb = b[J1]
    if entry(lastb,0,0) == entry(lastb,1,0): return J1
    cands = [J for J in range(len(b))
             if entry(lastb,0,0)==entry(b[J],0,0) and entry(b[J],1,0)<entry(b[J],0,0)]
    return min(cands)

# -------- p_8_2_condIIIV existence/uniqueness --------
def check_condIIIV(M):
    # hypotheses
    if not in_DT_PS(M): return None
    b = Br(M)
    if not b: return None
    j1 = Lng(M)-1
    J1 = len(b)-1
    j0p = Joints(M)[J1]
    j1p = FirstNodes(M)[J1]
    if j0p is None: return None
    if not (0 < j0p and j0p < TrMax(M)): return None
    if not (entry(M,0,j1p) > entry(M,1,j1p)): return None
    J0 = LastStep(M)
    m1 = FirstNodes(M)[J0] - 1
    N  = seg(M, 0, m1)
    Np = seg(M, j0p, m1)
    Mp = seg(M, j0p, j1)
    TN, TNp, TMp, TM = Trans(N), Trans(Np), Trans(Mp), Trans(M)
    # solve for t1 from (1): Trans N = D_{M1,0}(t1)
    if not TN[1] or TN[1][0][1] != entry(M,1,0): return ('fail1', M)
    t1 = TN[1][0][2]
    # (2) Trans N' = D_{M1,j0'}(t1)
    if TNp != Dpt(entry(M,1,j0p), t1): return ('fail2', M, TNp, Dpt(entry(M,1,j0p),t1))
    # (3) Trans M' = D_{M1,j0'}(t1 + t2), t2!=0
    if not TMp[1] or TMp[1][0][1] != entry(M,1,j0p): return ('fail3a', M)
    body3 = TMp[1][0][2]  # = t1 + t2
    # t2 = body3 with t1 stripped from the front
    if body3[1][:len(t1[1])] != t1[1]: return ('fail3b', M, t1, body3)
    t2 = ('T', body3[1][len(t1[1]):])
    if t2 == ZB: return ('fail3c-t2zero', M)
    # (4) Trans M = D_{M1,0}(t1 + D_{M1,j0'}(t1+t2))
    rhs4 = Dpt(entry(M,1,0), addBT(t1, Dpt(entry(M,1,j0p), addBT(t1, t2))))
    if TM != rhs4: return ('fail4', M, TM, rhs4)
    return ('ok', M, t1, t2)

# -------- not-leftDj0 guard for c2sx --------
def transJ0(M): return parent(M, 0, Lng(M)-1)

def condII(M):
    n = Lng(M)
    if n < 3: return False
    if not hasParent(M, 0, n-1): return False
    j0 = transJ0(M)
    return entry(M,1,n-1) == 0 and not adm(M, j0)

def genuineII(M):
    if not condII(M): return False
    if Lng(M)-1 <= 1: return False
    if not monoT(M): return False
    return is_reduced(M)

def c2sx_ldj(M):
    j0 = transJ0(M); jm1 = Adm(M, j0)
    c1 = Mark(Pred(M), jm1)
    t2 = bpHeadT(c1)
    if t2 == ZB: return None
    pj = PB(t2)[-1]
    return bpHeadV(pj) == entry(M,1,j0)

def guard_class(R, d):
    if not (is_reduced(R) and monoT(R)): return 'RnotRedMono'
    b = Br(R)
    if not b:
        return 'trunk' if TrMax(R) == Lng(R)-1 else 'BrEmpty-nontrunk'
    jl = Joints(R)[len(b)-1]
    if jl is None: return 'jointNone'
    if d < jl: return 'reg-lt'
    if d == jl:
        fn = FirstNodes(R)[len(b)-1]
        if entry(R,0,fn) == entry(R,1,fn) and descending(b): return 'reg-eqdiag'
        return 'eq-BAD'
    return 'gt-BAD'

def main():
    t0 = time.time()
    # (A) p_8_2_condIIIV
    A_ok=A_fail=A_hosts=0; A_examples=[]
    # (B) guard
    B_ok=B_bad=B_hosts=0; B_examples=[]; ldj_classes={}
    Lmax = int(sys.argv[1]) if len(sys.argv)>1 else 7
    vmax = int(sys.argv[2]) if len(sys.argv)>2 else 4
    cells = [(a,b) for a in range(vmax) for b in range(vmax)]
    for L in range(3, Lmax+1):
        if time.time()-t0 > 1200: pr(f"[budget] stop L={L}"); break
        for tup in itertools.product(cells, repeat=L-1):
            if time.time()-t0 > 1200: break
            M = [(0,0)] + list(tup)
            # (A)
            r = check_condIIIV(M)
            if r is not None:
                A_hosts += 1
                if r[0]=='ok': A_ok += 1
                else:
                    A_fail += 1
                    if len(A_examples)<6: A_examples.append(r)
            # (B)
            if genuineII(M):
                ld = c2sx_ldj(M)
                if ld is None: continue
                j0=transJ0(M); jm1=Adm(M,j0); d=j0-jm1
                R = Red(seg(M, jm1, Lng(M)-2))
                gc = guard_class(R, d)
                if ld:
                    ldj_classes[gc] = ldj_classes.get(gc,0)+1
                else:
                    B_hosts += 1
                    if gc in ('trunk','reg-lt','reg-eqdiag'): B_ok += 1
                    else:
                        B_bad += 1
                        if len(B_examples)<8: B_examples.append((fmt(M), gc, is_standard(M)))
        pr(f"[L={L}] condIIIV ok={A_ok}/{A_hosts} guard ok={B_ok}/{B_hosts} bad={B_bad} t={time.time()-t0:.0f}s")
    pr("="*60)
    pr(f"[A p_8_2_condIIIV] ok={A_ok}/{A_hosts} fail={A_fail}")
    for e in A_examples: pr("   FAIL:", e[0], fmt(e[1]) if len(e)>1 else '')
    pr(f"[B guard notLDJ] ok={B_ok}/{B_hosts} bad={B_bad}")
    for e in B_examples: pr("   BAD:", e)
    pr(f"[LDJ class distribution] {ldj_classes}")

if __name__ == '__main__':
    main()
