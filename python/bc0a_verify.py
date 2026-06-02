#!/usr/bin/env python3
"""BC0-A target verification. EXACT statement:

For mono M with m10 = entry M 1 0 > 0,
  A  := diagSeq 0 (m10-1) @ IncrFirst^m10 M
  jA := Lng A - 1
  N  := Red A
  jN := Lng N - 1
SHOW:  le0 A m10 jA  -->  le0 N m10 jN.

We sweep a BROAD class of M (all_pairseqs M0=(0,0)) -- NOT only reachable std --
to make the antecedent non-vacuous, and report BOTH counts:
  - antecedent-true & consequent-true  (the supportive cases)
  - antecedent-true & consequent-false (counterexamples; MUST be 0)
Also for context: antecedent-false rows (where the implication is vacuous).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, zeroT, multiT, monoT, diagSeq, IncrFirst,
                       funpow, seg, fmt, le0, Red)

def all_pairseqs(maxlen, maxval):
    from itertools import product
    out=[]
    for n in range(1,maxlen+1):
        for cells in product(product(range(maxval+1),repeat=2),repeat=n):
            M=[tuple(c) for c in cells]
            # recursion node: m00 = row0[0] = 0 (article keeps row0 left end 0)
            if M[0][0]==0: out.append(M)
    return out

cnt={'ant_true_cons_true':0,'ant_true_cons_false':0,'ant_false':0,
     'M_mono_total':0,'m10pos_evals':0}
ce=[]

def test(M):
    # M is a recursion node: M0=(0,0) so m00=0, and the m10>0 branch fires.
    if entry(M,0,0)!=0: return
    m10=entry(M,1,0)
    if m10<=0: return
    A=diagSeq(0,m10-1)+funpow(IncrFirst,m10,M)
    # A must be mono+anchored (coreReduce_monoT_m10_pos): restrict to that domain.
    if not monoT(A): return
    cnt['m10pos_evals']+=1
    jA=Lng(A)-1
    N=Red(A)
    jN=Lng(N)-1
    ant=le0(A,m10,jA)
    cons=le0(N,m10,jN)
    if ant:
        if cons: cnt['ant_true_cons_true']+=1
        else:
            cnt['ant_true_cons_false']+=1
            ce.append((fmt(M),m10,fmt(A),fmt(N)))
    else:
        cnt['ant_false']+=1

if __name__=='__main__':
    L,V=(int(sys.argv[1]),int(sys.argv[2])) if len(sys.argv)>2 else (4,2)
    Ms=all_pairseqs(L,V)
    for M in Ms:
        try: test(M)
        except Exception as e:
            print("ERR",fmt(M),e)
    print(f"# all_pairseqs M0=(0,0) len<=%d val<=%d : %d"%(L,V,len(Ms)))
    print(f"# mono M with m10>0 (evals): {cnt['m10pos_evals']}")
    print(f"ANTECEDENT TRUE  & consequent TRUE  : {cnt['ant_true_cons_true']}")
    print(f"ANTECEDENT TRUE  & consequent FALSE : {cnt['ant_true_cons_false']}  <== MUST be 0")
    print(f"antecedent FALSE (implication vacuous): {cnt['ant_false']}")
    if ce:
        print("=== COUNTEREXAMPLES ===")
        for e in ce[:10]: print("   ",e)
