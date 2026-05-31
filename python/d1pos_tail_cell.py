#!/usr/bin/env python3
"""Deep-characterize the UNCOVERED periodic-tail cell (j0'>=Lng N-1, A>=Lng N-1).
Also: is the 'boundary-crossing' cell {j0'<jm2, jm2<=A} EVER non-empty?
Report for the tail cell:
  - relation of q0, shamt, j0red, j1red to the period;
  - whether the WHOLE slice seg M j0' j1' lies in the periodic repeat (j0'>=Lng N-1=jm2+w means
    j0' is in some block q>=1);
  - whether the formula-G witness reduces it to an N-slice seg N j0red j1red with j0red<Lng N-1.
"""
import sys, os
from collections import defaultdict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, multiT, Br, le0, fmt)
from d1pos_j0j1red_search import gen_std, is_d1pos_mono, brle, full_facts

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (12, 5, 6)
    Ns = [N for N in gen_std(maxlen, maxval, KMAX) if is_d1pos_mono(N)]
    boundary_cross=0   # j0'<jm2 AND jm2<=A
    tail_n=0; tail_full=0
    tail_jeq=0         # j0red == jm2+(j0'-jm2)%w and < LN-1
    tail_shpos=0       # shamt>0
    examples=[]
    # invariants we want for the proof:
    inv_j0red_lt_LN1=0; inv_q0_eq=0; inv_A_blk=0
    for N in Ns:
        LN = Lng(N); jm2 = parent(N, 1, LN-1); w = LN-1-jm2
        if w<=0: continue
        delta=entry(N,0,LN-1)-entry(N,0,jm2)
        for n in (1,2,3):
            M = oper(N, n)
            if Lng(M) < 2: continue
            for j0p in range(Lng(M)):
                for j1p in range(j0p+1, Lng(M)):
                    if j1p < LN-1: continue
                    if not le0(M, j0p, j1p): continue
                    Mp = seg(M, j0p, j1p)
                    if not monoT(Mp): continue
                    if brle(Mp): continue
                    t=TrMax(Mp); A=j0p+t+1
                    if j0p < jm2 and jm2 <= A:
                        boundary_cross+=1
                        if len(examples)<5:
                            examples.append(('BC',fmt(N),n,j0p,j1p,'A',A,'jm2',jm2,'LN1',LN-1,'t',t))
                        continue
                    # tail cell: A>=LN-1 (==> j0'>=LN-1 too in data, but classify by A)
                    if A < LN-1: continue
                    tail_n+=1
                    q0=(j0p-jm2)//w if j0p>=jm2 else 0
                    j0red=jm2+(j0p-jm2)%w if j0p>=jm2 else j0p
                    j1red=min(j0red+(j1p-j0p),LN-1)
                    shamt=q0*delta
                    full = (j0red<j1red<=LN-1) and le0(N,j0red,j1red) and full_facts(N,j0red,j1red,Mp,shamt)
                    if full: tail_full+=1
                    if j0red < LN-1: inv_j0red_lt_LN1+=1
                    if shamt>0: tail_shpos+=1
                    # is j0' itself in a periodic block q>=1?  j0'>=jm2+w=LN-1
                    if j0p>=LN-1: inv_A_blk+=1
                    # the A (LOW source start) is also in some block: A-jm2 in block (A-jm2)//w
                    Ablk=(A-jm2)//w if A>=jm2 else 0
                    Ared=jm2+(A-jm2)%w if A>=jm2 else A
                    if len(examples)<14 and full:
                        examples.append(('TAIL',fmt(N),'n',n,'j0p',j0p,'j1p',j1p,'A',A,'jm2',jm2,'w',w,'LN1',LN-1,
                                         'q0',q0,'j0red',j0red,'j1red',j1red,'shamt',shamt,
                                         'Ablk',Ablk,'Ared',Ared,'delta',delta))
    print(f"boundary-cross cell {{j0'<jm2, jm2<=A}}: {boundary_cross} cases")
    print(f"TAIL cell (A>=LN-1): n={tail_n} full={tail_full}/{tail_n}")
    print(f"  j0red<LN-1: {inv_j0red_lt_LN1}/{tail_n}   shamt>0: {tail_shpos}/{tail_n}   j0'>=LN-1: {inv_A_blk}/{tail_n}")
    print("examples:")
    for e in examples: print("  ",e)

if __name__=='__main__': main()
