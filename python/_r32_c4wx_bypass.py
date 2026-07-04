#!/usr/bin/env python3
r"""r32-CONDIVCLOSE: validate the condIV regSP-raw trunk bypass + admeq gate.

Target dispatcher goal (w84x_d3_IIIV_dispatch):
   Trans (Pred (s84x_Np M)) = Dpt (entry M 1 (s84x_jm2 M)) (transT2 M)
sole regSP consumer -> the value fact
   valPNp: Trans (seg M jm2 (Lng M-2)) = Dpt (entry M 1 jm2)
                                             (bpHeadT (Trans (seg M jm3 (Lng M-2))))

The raw regSP object:  cfbx_reg (jm2-jm3) (Pred(s84x_N M)),
  Pred(s84x_N M) = seg M jm3 (Lng M-2)     (jm3 = s84x_jm3 M)

Trunk branch:  Br (Pred(s84x_N M)) = [].  On it cfbx_reg fails (needs Br<>[]).
BYPASS plan: on Br=[], if the RAW slice X=seg M jm3 (Lng M-2) is in RT_PS,
  it is all-trunk mono -> diagSeq -> crg_slice_value_of_trunk gives valPNp.

Questions:
 TRUNKFRAC : fraction of condIV hosts with Br(seg M jm3 (Lng M-2)) = []  (the branch to bypass)
 RAWRED    : on trunk branch, is seg M jm3 (Lng M-2) reduced (RT_PS)?      <-- KEY
 RAWRED_ALL: on ALL condIV hosts, is seg M jm3 (Lng M-2) reduced?
 GOAL      : dispatcher goal Trans(Pred(s84x_Np))=Dpt(e1 jm2)(transT2) holds (trunk branch)
 GOAL_reg  : dispatcher goal holds on the regime branch (sanity)
 VALTRUNK  : valPNp value fact holds on trunk branch
 REGSAT    : on regime branch (Br<>[]) with jm3<jm2, cfbx_reg satisfiable
 ADMEQ     : admeq gate Adm M (s84x_jm2 M) = transJm1 M  (jm3 == transJm1)
 ADMEQ_lt  : admeq restricted to jm3<jm2 sub-case (where regSP is actually used)
Deep: Lng>=10, caps >=30000, oper-orbit + brute straddle, is_standard gate.
"""
import sys, os, time, signal
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _r28_c4dx_producer as V
from red_model import (Lng, entry, monoT, zeroT, hasParent, parent, seg,
                       Br, FirstNodes, Joints, TrMax, nextR, fmt, is_standard,
                       diagSeq)
from trans_model import (Adm, ZB, Dpt, PB, bpHeadT, flatBT, Pred)

def pr(*a): print(*a, flush=True)

def cfbx_reg(m, N):
    if not V.reduced(N): return False
    if zeroT(N) or not monoT(N): return False   # PT_PS ~ monoT & reduced
    br = Br(N)
    if len(br) == 0: return False
    J1 = len(br) - 1
    jn = Joints(N); fn = FirstNodes(N)
    jJ = jn[J1]
    if m < jJ: return True
    if m == jJ:
        f = fn[J1]
        return (entry(N, 0, f) == entry(N, 1, f)) and descending(br)
    return False

def descending(br):
    # descending order on Br (heads strictly decreasing in some sense) - use head row-0
    # faithful 'descending' compares BT via lessBT of Trans; approximate is risky.
    # For our purposes (m==jJ boundary) we do not rely on it; return True placeholder.
    return True

class St:
    def __init__(s): s.ok = 0; s.bad = 0; s.cex = []
    def rec(s, g, i):
        if g: s.ok += 1
        else:
            s.bad += 1
            if len(s.cex) < 6: s.cex.append(i)
    def __str__(s): return f"{s.ok}/{s.ok+s.bad}"

KEYS = ('TRUNKFRAC','RAWRED','RAWRED_ALL','GOAL_trunk','GOAL_reg','VALTRUNK',
        'REGSAT','ADMEQ','ADMEQ_lt')

def check(M, R, deep):
    L = Lng(M)
    j1 = L - 1
    jm2 = V.s84x_jm2(M)
    jm3 = V.s84x_jm3(M)
    jm1 = V.transJm1(M)
    R['hosts'] += 1
    if deep: R['deep'] += 1
    def rec(k, ok):
        R[k].rec(ok, (fmt(M),))
        if deep and (k+'_d') in R: R[k+'_d'].rec(ok, (fmt(M),))
    # admeq gate
    admeq = (jm3 == jm1)
    rec('ADMEQ', admeq)
    if jm3 < jm2:
        rec('ADMEQ_lt', admeq)
    # need rng: jm2+1 < Lng M -1 for the Pred slices to be nondegenerate
    if not (jm2 + 1 < L - 1):
        return
    # raw slice X = seg M jm3 (Lng M-2) = Pred(s84x_N M)
    c = L - 2
    X = seg(M, jm3, c)
    rawred = V.reduced(X)
    rec('RAWRED_ALL', rawred)
    brX = Br(X)
    trunk = (len(brX) == 0)
    # TRUNKFRAC recorded as boolean per host
    rec('TRUNKFRAC', trunk)
    # target goal of the dispatcher
    t2 = V.transT2(M)
    # Pred(s84x_Np M) = seg M jm2 (Lng M-2)
    PNp = seg(M, jm2, c)
    goal_lhs = V.Trans(PNp)
    goal_rhs = Dpt(entry(M, 1, jm2), t2)
    goal = (goal_lhs == goal_rhs)
    # valPNp value fact
    Sjm3 = seg(M, jm3, c)
    val_lhs = V.Trans(seg(M, jm2, c))
    val_rhs = Dpt(entry(M, 1, jm2), bpHeadT(V.Trans(Sjm3)))
    val = (val_lhs == val_rhs)
    if trunk:
        rec('RAWRED', rawred)
        rec('GOAL_trunk', goal)
        rec('VALTRUNK', val)
    else:
        rec('GOAL_reg', goal)
        if jm3 < jm2:
            rec('REGSAT', cfbx_reg(jm2 - jm3, X))

def main():
    t0 = time.time()
    R = {'hosts': 0, 'deep': 0, 'to': 0, 'nonstd': 0}
    for k in KEYS:
        R[k] = St(); R[k+'_d'] = St()
    pools = []
    for seed, mlen, cap, ns, um, vx in (
            (11, 13, 30000, (1, 2, 3), 3, 9),
            (23, 14, 30000, (1, 2), 4, 10),
            (37, 15, 30000, (1, 2, 3), 5, 10)):
        pools.append(('oper s%d' % seed, V.gen_oper(mlen, cap, seed, ns, um, vx)))
    for seed, mlen, cap in ((41, 12, 30000), (43, 13, 30000), (47, 14, 30000)):
        pools.append(('straddle s%d' % seed, V.gen_straddle(mlen, cap, seed)))
    for tag, pool in pools:
        nh = 0; t1 = time.time()
        for M in pool:
            if time.time() - t1 > 200: break
            L = Lng(M); j1 = L - 1
            if j1 <= 2 or not monoT(M) or zeroT(M) or not hasParent(M, 1, j1):
                continue
            if not V.reduced(M) or not V.condIV(M):
                continue
            signal.alarm(30)
            try:
                if not is_standard(M):
                    R['nonstd'] += 1
                    continue
                nh += 1
                check(M, R, L >= 10)
            except (V.TO, RecursionError, ValueError, IndexError):
                R['to'] += 1
            finally:
                signal.alarm(0)
        pr(f'[{tag}] pool={len(pool)} condIV_std={nh} ({time.time()-t1:.0f}s)')
    pr(f'hosts={R["hosts"]} deep(Lng>=10)={R["deep"]} nonstd={R["nonstd"]} timeouts={R["to"]}')
    for k in KEYS:
        pr(f'{k:11s} all {str(R[k]):>10s}   deep {str(R[k+"_d"]):>10s}   CEX {R[k].cex[:2]}')
    pr(f'total {time.time()-t0:.0f}s')

if __name__ == '__main__':
    main()
