#!/usr/bin/env python3
"""BC0-A STANDALONE lemma verification (the clean faithful statement).

  redle_le0_anchor_fwd:
    for B with monoT B and B_0=(0,0) (anchored core),
    and any offset a (0<=a<Lng B) with le0 B a (Lng B - 1):
       le0 (Red B) a (Lng (Red B) - 1).

This is exactly what A=coreReduce M is (A mono, A_0=(0,0), anchor a=m10).
We enumerate B over: (i) gen_std reachable standard forms (deep, "rank>=12"),
and (ii) a broad bounded mono-anchored class. Report BOTH counts:
 - antecedent-true & consequent-true   (support)
 - antecedent-true & consequent-false  (counterexample, MUST be 0)
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, zeroT, multiT, monoT, fmt, le0, Red)
from d1pos_j0j1red_search import gen_std

cnt={'ant_true_cons_true':0,'ant_true_cons_false':0,'ant_false':0,'B_eligible':0}
ce=[]

def test_B(B):
    if not monoT(B): return
    if entry(B,0,0)!=0 or entry(B,1,0)!=0: return   # anchored core B_0=(0,0)
    n=Lng(B)
    if n<2: return
    cnt['B_eligible']+=1
    N=Red(B); jN=Lng(N)-1
    for a in range(0,n):
        ant=le0(B,a,n-1)
        if not ant:
            cnt['ant_false']+=1; continue
        # the right end of Red B is jN; the anchor edge maps a -> jN
        cons=le0(N,a,jN)
        if cons: cnt['ant_true_cons_true']+=1
        else:
            cnt['ant_true_cons_false']+=1
            ce.append((fmt(B),a,fmt(N)))

def all_anchored_mono(maxlen,maxval):
    from itertools import product
    out=[]
    for n in range(2,maxlen+1):
        for cells in product(product(range(maxval+1),repeat=2),repeat=n):
            B=[tuple(c) for c in cells]
            if B[0]==(0,0): out.append(B)
    return out

if __name__=='__main__':
    mode=sys.argv[1] if len(sys.argv)>1 else 'std'
    if mode=='std':
        L,V,K=(int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4])) if len(sys.argv)>4 else (12,5,7)
        Bs=gen_std(L,V,K)
        print(f"# gen_std L={L} V={V} K={K}: {len(Bs)} standard forms")
    else:
        L,V=(int(sys.argv[2]),int(sys.argv[3])) if len(sys.argv)>3 else (4,2)
        Bs=all_anchored_mono(L,V)
        print(f"# all anchored mono len<=%d val<=%d : %d"%(L,V,len(Bs)))
    for B in Bs:
        try: test_B(B)
        except Exception as e: print("ERR",fmt(B),e)
    print(f"# eligible B (mono, B0=(0,0)): {cnt['B_eligible']}")
    print(f"ANTECEDENT TRUE  & consequent TRUE  : {cnt['ant_true_cons_true']}")
    print(f"ANTECEDENT TRUE  & consequent FALSE : {cnt['ant_true_cons_false']}  <== MUST be 0")
    print(f"antecedent FALSE (vacuous)          : {cnt['ant_false']}")
    if ce:
        print("=== COUNTEREXAMPLES ===")
        for e in ce[:10]: print("   ",e)
