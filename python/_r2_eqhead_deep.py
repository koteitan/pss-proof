#!/usr/bin/env python3
"""DEEP, keystone-classified probe of the §8.7 R2 equal-head tail residual.

Within the GENUINE keystone-fire regime (the 4-case m_8_2_keystone discriminant),
equal-head subcase (x = hd), tally:
  - whether q == qb is FORCED (=> lemma is refl, trivial)
  - or q < qb strictly occurs (=> genuine subtree bound needed)
Stress at greater depth/length to heed the rank-depth warning.
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import Lng, entry, monoT, Br, FirstNodes, Joints, TrMax, adm
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

def gen_ST_PS(max_seed, max_n, max_len, rounds):
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

def classify(M):
    Lbr = Lng(Br(M))
    if Lbr == 0: return None
    j1p = FirstNodes(M)[Lbr-1]; j0p = Joints(M)[Lbr-1]
    v1j1 = entry(M,1,j1p); v0j1 = entry(M,0,j1p); admj0 = adm(M,j0p)
    if j1p == Lng(M)-1:
        trmax = TrMax(M)
        if (trmax==0 or j0p<trmax) and (v0j1==v1j1 or admj0): return 1
        if v0j1>v1j1 and not admj0: return 2
        return None
    return 34

def main():
    import sys as _s
    cfg = (int(_s.argv[1]), int(_s.argv[2]), int(_s.argv[3]), int(_s.argv[4])) \
          if len(_s.argv)>4 else (5,5,12,5)
    Ms = gen_ST_PS(*cfg)
    n_eq=0; n_strict=0; n_eqq=0; n_fail=0; cases={}
    strict_ex=[]; fail_ex=[]
    for M in Ms:
        if Lng(M)<1 or not reduced(M) or not monoT(M) or Br(M)==[]: continue
        if not (Lng(M)-1>1): continue
        try:
            tM=Trans(M); tP=Trans(Pred(M))
        except Exception: continue
        if tM==ZB or tP==ZB: continue
        if len(tM[1])!=1 or len(tP[1])!=1: continue
        psM=tM[1][0][2][1]; psP=tP[1][0][2][1]
        if len(psM)<2 or len(psP)<1: continue
        if psM[:-1]!=psP[:-1]: continue
        lastM=psM[-1]; lastP=psP[-1]; prev=psM[-2]
        x,q=lastM[1],lastM[2]; xp,qp=lastP[1],lastP[2]; hd,qb=prev[1],prev[2]
        if x!=xp or x!=hd: continue
        cse=classify(M)
        n_eq+=1; cases[cse]=cases.get(cse,0)+1
        if q==qb: n_eqq+=1
        elif lessBT(q,qb):
            n_strict+=1
            if len(strict_ex)<5: strict_ex.append((cse,len(M),M,('x',x)))
        else:
            n_fail+=1
            if len(fail_ex)<5: fail_ex.append((cse,M,('q',q),('qb',qb)))
    print(f"cfg={cfg}  total ST_PS={len(Ms)}")
    print(f"equal-head samples: {n_eq}   by case: {cases}")
    print(f"  q == qb (trivial/refl): {n_eqq}")
    print(f"  q <  qb (genuine bound): {n_strict}")
    print(f"  q  > qb (RESIDUAL FAIL): {n_fail}")
    if strict_ex:
        print("STRICT q<qb examples (case,len,M):")
        for e in strict_ex: print("   ",e)
    if fail_ex:
        print("FAIL examples:")
        for e in fail_ex: print("   ",e)
    print("RESULT:", "GOAL HOLDS" if n_fail==0 else "GOAL FAILS")

if __name__=='__main__': main()
