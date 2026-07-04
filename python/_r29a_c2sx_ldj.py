#!/usr/bin/env python3
# r29a-CONDII focused probe: run the FULL [H][W][I][N][R] battery on all brute
# leftDj0 genuine condII hosts up to L=7 (the ldj branch of the tailval residual),
# reporting standardness per host.
import sys, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, parent, Adm, adm, fmt, Pred, is_standard)
import _r29a_c2sx_probe as P
from _r29a_c2sx_probe import pr, newst, report, check_host, genuine
from trans_model import PB, bpHeadV, bpHeadT

def main():
    t0=time.time()
    st=newst(); exs=[]
    cells=[(a,b) for a in range(4) for b in range(4)]
    nstd=0; nldj=0
    for L in range(4, 7):
        if time.time()-t0 > 900: pr(f"[budget] stop at L={L}"); break
        for tup in itertools.product(cells, repeat=L-1):
            if time.time()-t0 > 900: break
            M=[(0,0)]+list(tup)
            if not genuine(M): continue
            j1=Lng(M)-1; j0=parent(M,0,j1); jm1=Adm(M,j0)
            c1=P.Mk(Pred(M), jm1)
            if c1 is None or not c1[1]: continue
            t2=bpHeadT(c1)
            if t2==('T',[]): continue
            pj=PB(t2)[-1]
            if bpHeadV(pj)!=entry(M,1,j0): continue   # ldj only
            nldj+=1
            if is_standard(M): nstd+=1
            check_host(M, st, exs)
        pr(f"[LDJ] L={L} done hosts={st['hosts']} std={nstd} t={time.time()-t0:.0f}s")
    report('LDJ', st, exs)
    pr(f"[LDJ] ldj hosts={nldj} standard={nstd}")

if __name__ == '__main__':
    main()
