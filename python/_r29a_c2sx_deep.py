#!/usr/bin/env python3
# r29a-CONDII deep corpus probe: bigger/deeper ST pool aimed at genuine condII
# hosts (esp. hunting leftDj0=True on ST). Reports the same [H][W][I][N][R]
# checks as _r29a_c2sx_probe plus is_standard on brute hosts.
import sys, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, monoT, reduced, seg, parent, Adm, adm, nadm,
                       oper, diagSeq, le0, Br, FirstNodes, Joints, Red,
                       hasParent, fmt, TrMax, marked, Pred, is_standard)
import _r29a_c2sx_probe as P
from _r29a_c2sx_probe import (pr, newst, report, check_host, genuine, gen_oper)

def main():
    t0=time.time()
    pool = gen_oper(maxlen=15, maxn=6, maxseed=6, cap=120000, budget=600)
    pr(f"[genD] pool={len(pool)} t={time.time()-t0:.0f}s")
    st=newst(); exs=[]
    nge=0
    cand=[M for M in pool if genuine(M)]
    pr(f"[genD] genuineCondII={len(cand)} t={time.time()-t0:.0f}s")
    for M in cand:
        check_host(M, st, exs)
    report('DEEP', st, exs)
    # standardness of brute leftDj0 hosts (L<=6)
    pr("[stdchk] brute leftDj0 hosts standardness:")
    cells=[(a,b) for a in range(4) for b in range(4)]
    t1=time.time(); found=0
    for L in range(4, 7):
        for tup in itertools.product(cells, repeat=L-1):
            if time.time()-t1>420: break
            M=[(0,0)]+list(tup)
            if not genuine(M): continue
            j1=Lng(M)-1; j0=parent(M,0,j1); jm1=Adm(M,j0)
            c1=P.Mk(Pred(M), jm1)
            if c1 is None or not c1[1]: continue
            from trans_model import PB, bpHeadV, bpHeadT
            t2=bpHeadT(c1)
            if t2==('T',[]): continue
            pj=PB(t2)[-1]
            ldj=(bpHeadV(pj)==entry(M,1,j0))
            if ldj:
                found+=1
                pr(f"   ldj host {fmt(M)} standard={is_standard(M)}")
    pr(f"[stdchk] found={found} t={time.time()-t0:.0f}s")

if __name__ == '__main__':
    main()
