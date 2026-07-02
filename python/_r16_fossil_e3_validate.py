#!/usr/bin/env python3
"""r16-E3 validation: the A32-corrected p_8_4_Trans_oper_exchange and every
intermediate of the planned Isabelle route (kind-1 fseq form at head e1jm3,
X-/A-towers, base compares, the (3)-residual HB3).

Route being validated (uniform across the L5 regime jm3=jm1 and L6 regime
jm3<jm1):
  N   = seg M jm3 j1,  TN = Trans N = D_e3 bodyN (principal, head e3=M1,jm3)
  (U0,V0) = the kind-1 pair of Trans M around flat(TN)   [m_8_4_Trans_scb]
  (SS,BB) = the inner scb of bodyN around flat(D_{M1,j1} 0)
  domB bodyN = T_{M1,j1 - 1},  M1,jm2 = M1,j1 - 1  (condition (A))
  fseq form:  flat(Trans(M)[numBT n])
            = U0 [D_e3] (SS [D_e2])^n [D_e2, Z] BB^n V0        (engine A24)
  A-tower: A_0 = bodyPredN = bpHeadT(Trans(Pred N));
           A_{k+1} = unflat(SS + flat(D_e2 A_k) + BB)
  X-tower: X_0 = D_e2 0;  X_{k+1} = unflat(SS + flat(D_e2 X_k) + BB)
  M[n] form:  flat(Trans(M[n])) = U0 + flatBP(DB e3 A_{n-1}) + V0
  (1) strict: A_{n-1} < X_n  (base A_0 < X_1, step scbext)
  (2):        A_{n-1} < bodyN (base A_0 < bodyN via c1<c2, step head e2<M1,j1)
  (3) shifted at n-1 (incl. 0): X_{n-1} < A_{n-1}  (base HB3: D_e2 0 < A_0)
      then printed (3) via Trans(M[n]) < Trans(M[n+1]) (Pred chain).

Usage: python3 _r16_e3_validate.py [quick|std|iv]
"""
import sys, time, signal
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from _r15_vx_lib import (Trans, Mark, lessBT, leBT, lessBP, numBT, operB, domB,
                         gen_pool, mono_hosts, Tally, guarded, SKIP, internals)
from red_model import Lng, entry, parent, hasParent, oper, seg, monoT, diagSeq, P, multiT
from trans_model import (Dpt, addBT, PB, SigmaB, bpHeadV, bpHeadT, flatBT, flatBP,
                         unflatBT, scb_decomps, ZB, adm, Adm, Pred, condIII, condVI,
                         isPTB_str, _c2)
from _r15_vx_lib import condIV
import random

INF = float('inf')

def kind1_ok(t, cflat):
    """scb_kind1 check of a decomposition core cflat inside t (RightNodes valley)."""
    p = unflatBT(cflat)
    if len(p[1]) != 1: return False
    r = []
    x = p
    while x[1]:
        last = x[1][-1]
        r.append(last[1]); x = last[2]
    j1 = len(r) - 1
    return j1 >= 1 and r[0] < r[j1] and all(r[j] >= r[j1] for j in range(1, j1))

def check_host(M, T, nmax=3):
    j1 = Lng(M) - 1
    j0 = parent(M, 0, j1)
    jm2 = parent(M, 1, j1)
    jm1 = Adm(M, j0)
    jm3 = Adm(M, jm2)
    cIII = condIII(M); cIV = condIV(M)
    e3 = entry(M, 1, jm3); e2 = entry(M, 1, jm2)
    v1e = entry(M, 1, j1); e1m1 = entry(M, 1, jm1)
    regime = 'L5' if jm3 == jm1 else 'L6'
    tag = ('III' if cIII else 'IV') + '-' + regime

    # S0 regime facts
    T.add('S0_jm3_le_jm1', jm3 <= jm1, (M, 0))
    if cIII: T.add('S0_III_L6', jm3 < jm1, (M, 0))
    T.add('S0_condA_e2', e2 == v1e - 1, (M, 0))
    T.add('S0_e3_lt_v1', e3 < v1e, (M, 0))

    N = seg(M, jm3, j1)
    TN = Trans(N)
    TM = Trans(M)
    # S1 TN principal head e3 + kind-1 of Trans M around TN
    okp = len(TN[1]) == 1 and TN[1][0][1] == e3
    T.add('S1_TN_prin_e3', okp, (M, 0))
    if not okp: return
    bodyN = bpHeadT(TN)
    ds = scb_decomps(TM, flatBT(TN))
    T.add('S1_TM_TN_scb1', len(ds) == 1, (M, 0))
    if len(ds) != 1: return
    U0, V0 = ds[0]
    T.add('S1_kind1', kind1_ok(TM, flatBT(TN)), (M, 0))
    if regime == 'L5':
        ii = internals(M)
        T.add('S1_L5_TN_eq_c2', ii is not None and TN == ii['c2'], (M, 0))

    # S2 domB + inner scb of bodyN
    T.add('S2_domB', domB(bodyN) == ('TB', v1e - 1), (M, 0))
    dsi = scb_decomps(bodyN, flatBT(Dpt(v1e, ZB)))
    T.add('S2_inner_scb1', len(dsi) == 1, (M, 0))
    if len(dsi) != 1: return
    SS, BB = dsi[0]

    # S4 Trans(Pred N) principal head e3, A0
    TPN = Trans(Pred(N))
    okpp = len(TPN[1]) == 1 and TPN[1][0][1] == e3
    T.add('S4_TPN_prin_e3', okpp, (M, 0))
    if not okpp: return
    A0 = bpHeadT(TPN)
    # A0's flat vs (SS,BB)? not directly (uu1-level); but towers use SS/BB.

    # towers
    def wrap(t):
        return unflatBT(SS + flatBP(('D', e2, t)) + BB)
    try:
        A = [A0]; X = [Dpt(e2, ZB)]
        for k in range(nmax + 1):
            A.append(wrap(A[-1])); X.append(wrap(X[-1][1][0] if len(X[-1][1])==1 and False else X[-1]))
    except Exception:
        T.add('S5_tower_parse', False, (M, 0)); return
    # X tower: X[k+1] = unflat(SS + flat(D_e2 X_k) + BB) -- wrap takes term
    X = [Dpt(e2, ZB)]
    for k in range(nmax + 1):
        X.append(unflatBT(SS + [('D', e2)] + flatBT(X[-1]) + BB))
    A = [A0]
    for k in range(nmax + 1):
        A.append(unflatBT(SS + [('D', e2)] + flatBT(A[-1]) + BB))
    T.add('S5_tower_parse', True, (M, 0))

    # S3 fseq string form; S6 fseq core value = D_e3 X_n
    for n in range(0, nmax + 1):
        fs = guarded(operB, TM, numBT(n), budget=10)
        if fs is SKIP:
            T.add('S3_fseq_form', SKIP); continue
        want = (U0 + [('D', e3)]
                + sum([SS + [('D', e2)] for _ in range(n)], [])
                + [('D', e2), 'Z']
                + sum([BB for _ in range(n)], []) + V0)
        T.add('S3_fseq_form', flatBT(fs) == want, (M, n))
        T.add('S6_fseq_core', flatBT(fs) == U0 + [('D', e3)] + flatBT(X[n]) + V0, (M, n))

    # S5 M[n] closed form via A-tower
    for n in range(1, nmax + 1):
        Mn = guarded(oper, M, n, budget=5)
        if Mn is SKIP:
            T.add('S5_Mn_form', SKIP); continue
        tmn = guarded(Trans, Mn, budget=10)
        if tmn is SKIP:
            T.add('S5_Mn_form', SKIP); continue
        want = U0 + [('D', e3)] + flatBT(A[n - 1]) + V0
        T.add('S5_Mn_form', flatBT(tmn) == want, (M, n))

    # S7 base compares + residual
    T.add('S7_base1_A0_lt_X1', lessBT(A0, X[1]), (M, 0))
    T.add('S7_base2_A0_lt_bodyN', lessBT(A0, bodyN), (M, 0))
    T.add('S7_HB3_De20_lt_A0', lessBT(Dpt(e2, ZB), A0), (M, 0))
    # per-branch value shapes (S9)
    ii = internals(M)
    if ii is not None:
        v, t2, c2b, t3, t4, ld = ii['v'], ii['t2'], ii['c2'], ii['t3'], ii['t4'], ii['leftDj0']
        T.add('S9_v_e1jm1', v == e1m1, (M, 0))
        if cIII:
            T.add('S9_III_c2', c2b == Dpt(v, addBT(t2, Dpt(v1e, ZB))), (M, 0))
        if cIV:
            if t2 == ZB:
                T.add('S9_IV_c2z', c2b == Dpt(v, Dpt(entry(M,1,j0), Dpt(v1e, ZB))), (M, 0))
            elif ld:
                T.add('S9_IV_t2split', t2 == addBT(t3, Dpt(entry(M,1,j0), t4)), (M, 0))
                T.add('S9_IV_c2ld', c2b == Dpt(v, addBT(t3, Dpt(entry(M,1,j0),
                                              addBT(t4, Dpt(v1e, ZB))))), (M, 0))
            else:
                T.add('S9_IV_c2nl', c2b == Dpt(v, addBT(t2, Dpt(entry(M,1,j0),
                                              addBT(t2, Dpt(v1e, ZB))))), (M, 0))

    # S8 conclusions
    for n in range(1, nmax + 1):
        Mn = guarded(oper, M, n, budget=5)
        Mn1 = guarded(oper, M, n + 1, budget=5)
        if Mn is SKIP or Mn1 is SKIP:
            T.add('S8_1_strict', SKIP); continue
        tmn = guarded(Trans, Mn, budget=10)
        tmn1 = guarded(Trans, Mn1, budget=10)
        fsn = guarded(operB, TM, numBT(n), budget=10)
        fsn1 = guarded(operB, TM, numBT(n - 1), budget=10)
        if SKIP in (tmn, tmn1, fsn, fsn1):
            T.add('S8_1_strict', SKIP); continue
        T.add('S8_1_strict', lessBT(tmn, fsn), (M, n))
        T.add('S8_2', lessBT(tmn, TM), (M, n))
        T.add('S8_3_printed', lessBT(fsn1, tmn1), (M, n))
        T.add('S8_3s_chain', lessBT(fsn1, tmn), (M, n))       # shifted-3 at n-1
        T.add('S8_pred_chain', lessBT(tmn, tmn1), (M, n))
        # towers vs conclusions consistency
        T.add('S8_1_tower', lessBT(A[n-1], X[n]), (M, n))
        T.add('S8_3s_tower', lessBT(X[n-1], A[n-1]), (M, n))
        T.add('S8_2_tower', lessBT(A[n-1], bodyN), (M, n))

def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else 'std'
    T = Tally()
    t0 = time.time()
    stats = {'III-L5':0, 'III-L6':0, 'IV-L5':0, 'IV-L6':0}
    seen = set()

    def run_pool(pool, budget):
        tseg = time.time()
        for M in mono_hosts(pool):
            if time.time() - tseg > budget: break
            j1 = Lng(M) - 1
            if j1 <= 1 or not monoT(M): continue
            if not hasParent(M, 1, j1): continue
            if not (condIII(M) or condIV(M)): continue
            k = tuple(M)
            if k in seen: continue
            seen.add(k)
            j0 = parent(M, 0, j1); jm2 = parent(M, 1, j1)
            reg = 'L5' if Adm(M, jm2) == Adm(M, j0) else 'L6'
            stats[('III' if condIII(M) else 'IV') + '-' + reg] += 1
            r = guarded(check_host, M, T, budget=45)
            if r is SKIP:
                T.add('HOST', SKIP)

    if mode == 'quick':
        run_pool(gen_pool(maxlen=8, maxn=3, maxseed=3, cap=1500), 300)
    elif mode == 'iv':
        # deep condIV mining (r15-S4d params)
        import _r15_s4d_validate as V
        for seed, mlen, cap, ns, um, vx, bud in (
                (202, 16, 12000, (1,2), 2, 7, 300),
                (303, 18, 12000, (1,2), 2, 8, 300)):
            pool = V.gen_pool(max_len=mlen, cap=cap, seed=seed, ns=ns, umax=um, vextra=vx)
            pool = [M for M in pool if monoT(M) and Lng(M) > 2
                    and hasParent(M, 1, Lng(M)-1) and condIV(M)]
            run_pool(pool, bud)
    else:
        run_pool(gen_pool(maxlen=9, maxn=4, maxseed=3, cap=4000), 500)
        run_pool(gen_pool(maxlen=8, maxn=3, maxseed=5, cap=3000), 250)

    print('regimes:', stats, ' hosts:', len(seen), f' ({time.time()-t0:.0f}s)')
    print(T.report('r16-E3 validation [%s]' % mode))

if __name__ == '__main__':
    main()
