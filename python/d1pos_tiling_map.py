#!/usr/bin/env python3
"""§6.8 d0pos ¬brle TILING MAP.
Classify EVERY in-context ¬brle case by (j0' vs jm2, A vs jm2, A vs Lng N-1, j0' vs Lng N-1)
where A = j0' + TrMax(M') + 1.  For each cell report:
  - which existing assembly lemma covers it:
       regA  cond: A < jm2
       regB  cond: jm2 <= A < Lng N-1  AND  jm2 <= j0'
  - whether the formula-G witness (j0red,j1red,shamt) satisfies the FULL stub existential.
Report UNCOVERED cells (no regA/regB).
"""
import sys, os
from collections import defaultdict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, multiT, Br, le0)
from d1pos_j0j1red_search import gen_std, is_d1pos_mono, brle, full_facts

def covers(cell_regA, cell_regB):
    if cell_regA: return "regA"
    if cell_regB: return "regB"
    return "UNCOVERED"

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (12, 5, 6)
    Ns = [N for N in gen_std(maxlen, maxval, KMAX) if is_d1pos_mono(N)]
    tot=0
    cells=defaultdict(lambda: {'n':0,'full':0,'cov':defaultdict(int),'ex':None})
    cov_count=defaultdict(int)
    for N in Ns:
        LN = Lng(N); jm2 = parent(N, 1, LN-1); w = LN-1-jm2
        if w<=0: continue
        delta=entry(N,0,LN-1)-entry(N,0,jm2)
        for n in (1,2,3):
            M = oper(N, n)
            if Lng(M) < 2: continue
            for j0p in range(Lng(M)):
                for j1p in range(j0p+1, Lng(M)):
                    if j1p < LN-1: continue          # bge: Lng N-1 <= j1'
                    if not le0(M, j0p, j1p): continue # le0 M
                    Mp = seg(M, j0p, j1p)
                    if not monoT(Mp): continue
                    if brle(Mp): continue             # ¬brle
                    tot += 1
                    t=TrMax(Mp); A=j0p+t+1
                    # 4 classification dims
                    d_j0jm2  = "j0<jm2" if j0p < jm2 else "j0>=jm2"
                    d_Ajm2   = "A<jm2"  if A < jm2  else "A>=jm2"
                    d_AN     = "A<LN1"  if A < LN-1 else "A>=LN1"
                    d_j0N    = "j0<LN1" if j0p < LN-1 else "j0>=LN1"
                    key=(d_j0jm2,d_Ajm2,d_AN,d_j0N)
                    # regime-lemma applicability (EXACT hypotheses)
                    regA = (A < jm2)
                    regB = (jm2 <= A < LN-1) and (jm2 <= j0p)
                    cov = covers(regA, regB)
                    cov_count[cov]+=1
                    # formula-G witness
                    q0=(j0p-jm2)//w if j0p>=jm2 else 0
                    j0red=jm2+(j0p-jm2)%w if j0p>=jm2 else j0p
                    j1red=min(j0red+(j1p-j0p),LN-1)
                    shamt=q0*delta
                    full = (j0red<j1red<=LN-1) and le0(N,j0red,j1red) and full_facts(N,j0red,j1red,Mp,shamt)
                    c=cells[key]
                    c['n']+=1
                    if full: c['full']+=1
                    c['cov'][cov]+=1
                    if c['ex'] is None:
                        from red_model import fmt
                        c['ex']=(fmt(N),n,j0p,j1p,'A',A,'jm2',jm2,'LN1',LN-1,'j0red',j0red,'j1red',j1red,'shamt',shamt,'full',full)
    print(f"#cases={tot} KMAX={KMAX} len<={maxlen} val<={maxval}")
    print(f"coverage: {dict(cov_count)}")
    print("\n=== CELLS (j0vsjm2, Avsjm2, AvsLN1, j0vsLN1): n full coverage ===")
    for key in sorted(cells):
        c=cells[key]
        print(f"  {key}: n={c['n']} full={c['full']}/{c['n']} cov={dict(c['cov'])}")
        print(f"      ex={c['ex']}")
    # Uncovered cells summary
    print("\n=== UNCOVERED witness check ===")
    unc_n=0; unc_full=0
    for key in sorted(cells):
        c=cells[key]
        if c['cov'].get('UNCOVERED',0)>0:
            unc_n+=c['cov']['UNCOVERED']
    print(f"  total UNCOVERED cases: {cov_count.get('UNCOVERED',0)}")

if __name__=='__main__': main()
