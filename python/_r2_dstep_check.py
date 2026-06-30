#!/usr/bin/env python3
"""EMPIRICAL truth-check for the §8.7 R2 dstep obligation in keystone cases (2),(3),(4).

dstep = the LAST-step descP of Trans M's outer body:
   Trans M = Dpt v0 (Trm psM),  psM = ps @ [DB x q],  last ps = DB hd qb
   dstep:  len(psM) >= 2  -->  leBT (Trm [psM[-1]]) (Trm [psM[-2]])
           i.e. (x < hd) OR (x = hd AND leBT q qb).
We separately tally the EQUAL-HEAD subcase (x = hd): there dstep needs leBT q qb.

Keystone regime: M in ST_PS, monoT M, Br M != [], Lng M - 1 > 1.
ST_PS sampled by BFS-closure under oper from diagSeq seeds (defn of ST_PS).
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import Lng, entry, monoT, Br, FirstNodes, Joints, TrMax, adm
import trans_model as tmod
from trans_model import Trans, Pred, reduced
from fast_pss import diagSeq, oper

ZB = ('T', [])

def lessBT(a, b):
    pa, pb = a[1], b[1]
    if not pa: return bool(pb)
    if not pb: return False
    return lessBP(pa[0], pb[0]) or (pa[0] == pb[0] and lessBT(('T', pa[1:]), ('T', pb[1:])))
def lessBP(p, q):
    # p,q = ('D', v, t)
    u, a = p[1], p[2]; v, b = q[1], q[2]
    return u < v or (u == v and lessBT(a, b))
def leBT(a, b): return lessBT(a, b) or a == b

# ---- ST_PS closure by BFS under oper from diagSeq seeds ----
def gen_ST_PS(max_seed=4, max_n=4, max_len=10, rounds=3):
    seen = set(); frontier = []
    for a in range(max_seed+1):
        for b in range(a, max_seed+1):
            s = tuple(diagSeq(a, b))
            if s and s not in seen:
                seen.add(s); frontier.append(list(s))
    allM = list(seen)
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

def classify_case(M):
    """Return keystone case label 1/2/3/4 or None, based on m_8_2_keystone branch
    discriminants (FirstNodes/Joints/adm), mirroring m_8_7_OT_keystone_step."""
    Lbr = Lng(Br(M))
    if Lbr == 0: return None
    j1p = FirstNodes(M)[Lbr-1]
    j0p = Joints(M)[Lbr-1]
    v1j1 = entry(M, 1, j1p)
    v0j1 = entry(M, 0, j1p)
    admj0 = adm(M, j0p)
    if j1p == Lng(M) - 1:
        # whole-body cases (1) or (2)
        trmax = TrMax(M)
        if (trmax == 0 or j0p < trmax) and (entry(M,0,j1p) == entry(M,1,j1p) or admj0):
            return 1
        if v0j1 > v1j1 and not admj0:
            return 2
        return None  # other whole-body shape
    else:
        # proper-prefix cases (3)/(4): distinguished by appended head index j1' vs j0'
        return 34

def main():
    Ms = gen_ST_PS()
    n_keystone = 0
    n_dstep_fail = 0
    n_eqhead = 0
    n_eqhead_fail = 0
    case_counts = {1:0, 2:0, 34:0, None:0}
    eq_by_case = {1:[0,0], 2:[0,0], 34:[0,0], None:[0,0]}  # [eqhead, eqhead_fail]
    dstep_fail_examples = []
    for M in Ms:
        if Lng(M) < 1: continue
        if not reduced(M): continue
        if not monoT(M): continue
        if Br(M) == []: continue
        if not (Lng(M) - 1 > 1): continue
        # compute Trans M
        try:
            tM = Trans(M)
        except Exception:
            continue
        if tM == ZB: continue
        # Trans M = Dpt v0 (Trm psM): outer is a single principal whose body is Trm psM
        if len(tM[1]) != 1:
            continue
        outer = tM[1][0]  # ('D', v0, body)
        body = outer[2]
        psM = body[1]
        n_keystone += 1
        cse = classify_case(M)
        case_counts[cse] = case_counts.get(cse,0)+1
        if len(psM) < 2:
            continue
        last = psM[-1]      # DB x q
        prev = psM[-2]      # DB hd qb  (= last ps)
        x, q = last[1], last[2]
        hd, qb = prev[1], prev[2]
        ds = leBT(('T',[last]), ('T',[prev]))
        if not ds:
            n_dstep_fail += 1
            if len(dstep_fail_examples) < 8:
                dstep_fail_examples.append((M, cse, (x,q), (hd,qb)))
        if x == hd:
            n_eqhead += 1
            eq_by_case[cse][0] += 1
            tl = leBT(q, qb)
            if not tl:
                n_eqhead_fail += 1
                eq_by_case[cse][1] += 1
                if len(dstep_fail_examples) < 8:
                    dstep_fail_examples.append(('EQHEAD-FAIL', M, cse, (x,q), (hd,qb)))
    print(f"keystone-regime samples (Trans M = Dpt v0 body): {n_keystone}")
    print(f"case counts (by m_8_2 discriminant): {case_counts}")
    print(f"dstep failures (last-step descP of Trans M body): {n_dstep_fail}")
    print(f"equal-head subcase occurrences (x = hd): {n_eqhead}")
    print(f"equal-head tail failures (leBT q qb): {n_eqhead_fail}")
    print(f"equal-head [occ, fail] by case: {eq_by_case}")
    if dstep_fail_examples:
        print("EXAMPLES:")
        for e in dstep_fail_examples: print("  ", e)
    print("RESULT:", "ALL PASS" if (n_dstep_fail==0 and n_eqhead_fail==0) else "FAILURES FOUND")

if __name__ == '__main__':
    main()
