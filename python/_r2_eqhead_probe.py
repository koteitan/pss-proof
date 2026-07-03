#!/usr/bin/env python3
"""Characterize the §8.7 equal-head tail residual.

In keystone cases (3)/(4), equal-head subcase:
  Trans(Pred M) body = ps @ [DB x qp]    (proper prefix ps, trailing principal at head x)
  Trans M       body = ps @ [DB x q]
  last ps = DB x qb                       (equal head: prefix's last also has head x)
The dstep residual is  leBT q qb.
We measure the relationships:
  (a) qp <= qb   (from predecessor descP / IH)        -- expected TRUE
  (b) qp <  q    (from m_7_3_Pred_Trans_descend)       -- expected TRUE (q GROWS)
  (c) q  <= qb   (the GOAL / residual)                 -- expected TRUE empirically
  (d) q  == qb   (periodic-copy subcase)
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import Lng, monoT, Br
from trans_model import Trans, Pred, reduced
from fast_pss import diagSeq, oper

ZB = ('T', [])
def lessBT(a, b):
    pa, pb = a[1], b[1]
    if not pa: return bool(pb)
    if not pb: return False
    return lessBP(pa[0], pb[0]) or (pa[0] == pb[0] and lessBT(('T', pa[1:]), ('T', pb[1:])))
def lessBP(p, q):
    u, a = p[1], p[2]; v, b = q[1], q[2]
    return u < v or (u == v and lessBT(a, b))
def leBT(a, b): return lessBT(a, b) or a == b

def gen_ST_PS(max_seed=4, max_n=4, max_len=11, rounds=4):
    seen = set(); frontier = []
    for a in range(max_seed+1):
        for b in range(a, max_seed+1):
            s = tuple(diagSeq(a, b))
            if s and s not in seen:
                seen.add(s); frontier.append(list(s))
    for _ in range(rounds):
        newf = []
        for M in frontier:
            for n in range(1, max_n+1):
                Mp = oper(M, n)
                if 1 <= Lng(Mp) <= max_len:
                    t = tuple(Mp)
                    if t not in seen:
                        seen.add(t); newf.append(Mp)
        frontier = newf
        if not frontier: break
    return [list(t) for t in seen]

def main():
    Ms = gen_ST_PS()
    n_eqhead = 0
    cnt = {'a_qp_le_qb':0, 'b_qp_lt_q':0, 'c_q_le_qb':0, 'd_q_eq_qb':0,
           'c_FAIL':0, 'a_FAIL':0, 'b_FAIL':0}
    fails = []
    for M in Ms:
        if Lng(M) < 1 or not reduced(M) or not monoT(M) or Br(M) == []: continue
        if not (Lng(M) - 1 > 1): continue
        try:
            tM = Trans(M); tP = Trans(Pred(M))
        except Exception:
            continue
        if tM == ZB or tP == ZB: continue
        if len(tM[1]) != 1 or len(tP[1]) != 1: continue
        psM = tM[1][0][2][1]      # Trans M body principal list
        psP = tP[1][0][2][1]      # Trans Pred body principal list
        if len(psM) < 2 or len(psP) < 1: continue
        # cases (3)/(4): psM and psP share the prefix psM[:-1] == psP[:-1] and same trailing head
        if psM[:-1] != psP[:-1]: continue            # not the proper-prefix surgery shape
        lastM = psM[-1]; lastP = psP[-1]; prev = psM[-2]
        x, q   = lastM[1], lastM[2]
        xp, qp = lastP[1], lastP[2]
        hd, qb = prev[1], prev[2]
        if x != xp:        # trailing heads must coincide (the deepen keeps head)
            continue
        if x != hd:        # equal-head subcase only
            continue
        n_eqhead += 1
        a = leBT(qp, qb); b = lessBT(qp, q); c = leBT(q, qb); d = (q == qb)
        if a: cnt['a_qp_le_qb'] += 1
        else: cnt['a_FAIL'] += 1
        if b: cnt['b_qp_lt_q'] += 1
        else: cnt['b_FAIL'] += 1
        if c: cnt['c_q_le_qb'] += 1
        else:
            cnt['c_FAIL'] += 1
            if len(fails) < 6: fails.append((M, ('x',x), ('q',q), ('qb',qb), ('qp',qp)))
        if d: cnt['d_q_eq_qb'] += 1
    print(f"equal-head proper-prefix samples: {n_eqhead}")
    print(f"  (a) qp <= qb : {cnt['a_qp_le_qb']}  FAIL={cnt['a_FAIL']}")
    print(f"  (b) qp <  q  : {cnt['b_qp_lt_q']}  FAIL={cnt['b_FAIL']}")
    print(f"  (c) q  <= qb : {cnt['c_q_le_qb']}  FAIL={cnt['c_FAIL']}   <-- the GOAL")
    print(f"  (d) q  == qb : {cnt['d_q_eq_qb']}")
    if fails:
        print("GOAL FAILS:")
        for f in fails: print("   ", f)
    print("RESULT:", "GOAL HOLDS" if cnt['c_FAIL']==0 and n_eqhead>0 else
          ("NO SAMPLES" if n_eqhead==0 else "GOAL FAILS"))

if __name__ == '__main__':
    main()
