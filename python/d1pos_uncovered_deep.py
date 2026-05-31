#!/usr/bin/env python3
"""DEEP-VERIFY (rank>=10) the two UNCOVERED cells with FULL stub existential.
Cell BC  (boundary-cross): j0'<jm2 AND jm2<=A<Lng N-1
Cell TAIL (periodic-tail) : A>=Lng N-1  (== j0'>=Lng N-1 in data)
For each: check the EXACT stub hyps (NT,monoN,LNgt,notzeroN,hasparN,i1zN,M=N[n],n>=1,
  M'T,le0M,j0'<j1',j1'<Lng M,bge,notbrle) and that formula-G witness satisfies the FULL
  existential.  Also tabulate the *geometry discriminators* used by the regime lemmas:
  A vs jm2, A vs LN-1, c vs cN vs m, shamt, j0red vs j0' / jm2.
"""
import sys, os
from collections import defaultdict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, multiT, Br, le0, IdxSum, fmt)
from d1pos_j0j1red_search import gen_std, is_d1pos_mono, brle, full_facts

def stub_hyps(N,M,n,j0p,j1p):
    LN=Lng(N); j1=LN-1
    if not (Lng(N)>1): return False
    if entry(N,0,j1)==0 and entry(N,1,j1)==0: return False
    if not hasParent(N,idx1(N,j1),j1): return False
    if idx1(N,j1)!=1: return False
    if n<1: return False
    Mp=seg(M,j0p,j1p)
    if not (len(Mp)>0): return False           # M'T (T_PS)
    if not le0(M,j0p,j1p): return False
    if not (j0p<j1p): return False
    if not (j1p<Lng(M)): return False
    if not (LN-1<=j1p): return False           # bge
    if brle(Mp): return False                   # notbrle
    return True

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (12, 5, 10)
    Ns = [N for N in gen_std(maxlen, maxval, KMAX) if is_d1pos_mono(N)]
    BC=dict(n=0,full=0,hyp=0,sh0=0,j0red_eq_j0=0,Aub=0,ex=[])
    TAIL=dict(n=0,full=0,hyp=0,shpos=0,j0red_lt_LN1=0,q0ge1=0,ex=[])
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
                    q0=(j0p-jm2)//w if j0p>=jm2 else 0
                    j0red=jm2+(j0p-jm2)%w if j0p>=jm2 else j0p
                    j1red=min(j0red+(j1p-j0p),LN-1)
                    shamt=q0*delta
                    full = (j0red<j1red<=LN-1) and le0(N,j0red,j1red) and full_facts(N,j0red,j1red,Mp,shamt)
                    hyp = stub_hyps(N,M,n,j0p,j1p)
                    if j0p<jm2 and jm2<=A<LN-1:
                        BC['n']+=1
                        if full: BC['full']+=1
                        if hyp: BC['hyp']+=1
                        if shamt==0: BC['sh0']+=1
                        if j0red==j0p: BC['j0red_eq_j0']+=1
                        if A<=jm2+ (0):  # A<=jm2? no. record A vs jm2
                            pass
                        if len(BC['ex'])<6:
                            BC['ex'].append((fmt(N),'n',n,'j0',j0p,'j1',j1p,'A',A,'jm2',jm2,'LN1',LN-1,'j0red',j0red,'j1red',j1red,'sh',shamt,'full',full,'hyp',hyp))
                    elif A>=LN-1:
                        TAIL['n']+=1
                        if full: TAIL['full']+=1
                        if hyp: TAIL['hyp']+=1
                        if shamt>0: TAIL['shpos']+=1
                        if j0red<LN-1: TAIL['j0red_lt_LN1']+=1
                        if q0>=1: TAIL['q0ge1']+=1
                        if len(TAIL['ex'])<6:
                            TAIL['ex'].append((fmt(N),'n',n,'j0',j0p,'j1',j1p,'A',A,'jm2',jm2,'LN1',LN-1,'j0red',j0red,'j1red',j1red,'sh',shamt,'q0',q0,'full',full,'hyp',hyp))
    print("=== BC (boundary-cross  j0'<jm2 AND jm2<=A<LN-1) ===")
    print(f"  n={BC['n']} full={BC['full']} hyp={BC['hyp']} shamt0={BC['sh0']} j0red==j0'={BC['j0red_eq_j0']}")
    for e in BC['ex']: print("   ",e)
    print("=== TAIL (periodic  A>=LN-1) ===")
    print(f"  n={TAIL['n']} full={TAIL['full']} hyp={TAIL['hyp']} shamt>0={TAIL['shpos']} j0red<LN-1={TAIL['j0red_lt_LN1']} q0>=1={TAIL['q0ge1']}")
    for e in TAIL['ex']: print("   ",e)

if __name__=='__main__': main()
