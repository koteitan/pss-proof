#!/usr/bin/env python3
"""§6.8 d1pos -- pin the cdom (consecutive-component) mechanism for descending(Br M').

Br M' = P(Y'), Y' = seg M' (TrMax M'+1)(Lng M'-1).  Every component monoT/zeroT.
For descending we need: for consecutive components C_{J-1}, C_J (= P-cut slices of Y'),
  cdom C_{J-1} C_J  :  head0(C_J) <= head0(C_{J-1})  AND
                       head0 equal => head1(C_J) <= head1(C_{J-1}).
Heads are entries of M' at the P-cut starts c_{J-1} < c_J (relative to M'),
which are absolute indices p_{J-1} < p_J in M, all >= j0N+ (TrMax region) in the fold.

Mechanism hypothesis (M'-trunk-direct, uses oper_d1pos geometry, delta>0):
  Each cut start p is in some block, absolute (entry M 0 p) = entry N 0 j + k*delta
  where j in [j0N..Lng N-2], k = block index.  P-cut points are le0-anchors:
  entry M' 0 (c_J) <= entry M' 0 (c_{J-1})  because consecutive P-cuts of a monoT
  branch have weakly decreasing left-ends (m_6_4_P_leftend_mono -- ROW-0 part FREE).
  The HARD part is row-1 tie-break when entry M 0 p_J == entry M 0 p_{J-1}.

Tests:
 (T1) row-0 weakly decreasing across cuts  (m_6_4_P_leftend_mono)  -- expect 0 fail
 (T2) WHEN row-0 ties, the two cut starts are in the SAME residue-mod-w block-phase
      (same j-offset within a block) so row-1 (= entry N 1 j, block-invariant) ties,
      OR row-1 strictly drops.  Characterize the tie source.
 (T3) The single mono TAIL = last P-component; everything before it: are the
      non-last components exactly the higher (smaller-k) ... NO: verify the head0
      values are NON-increasing because P lists trunk-first = the LARGER-row0 first.
 (T4) Closed identity attempt:  Br M' = P (seg M' (TrMax M'+1) (Lng M'-1)) and this
      equals  map (\(a,b)-> seg M' a b) (zip cuts (tl cuts ++ [end])).  (taut.)
 (T5) Each component C_J = seg M' c_J d_J  is monoT via H1 (oper_d1pos_seg_mono):
      need c_J to be a block-start-anchored le0 point:  le0 M' 0?  Actually H1 wants
      a = j0N + q*w + ... ; test: is each abs cut start p_J expressible as
      j0N + q*w + r with the slice [p_J .. d] satisfying le0 M (p_J) (d)?  i.e. each
      component is a le0-confined slice (monoT) -- equivalently monoT(C_J) directly.
"""
import sys, itertools
sys.path.insert(0,'/home/koteitan/pss-brmap/python')
from red_model import (Lng, entry, seg, oper, P, Br, TrMax,
                       is_standard, parent, idx1, le0, leR, monoT, multiT,
                       zeroT, hasParent)
def all_pairseqs(maxlen,maxval):
    cells=list(itertools.product(range(maxval+1),repeat=2))
    for L in range(1,maxlen+1):
        for tup in itertools.product(cells,repeat=L): yield list(tup)
def head(c): return (entry(c,0,0),entry(c,1,0))
def kind(c):
    if zeroT(c): return 'Z'
    return 'M' if monoT(c) else 'X'
MAXLEN=int(sys.argv[1]); MAXVAL=int(sys.argv[2]); NMAX=int(sys.argv[3])
wit=0
t1_fail=0
tie_same_phase=0; tie_diff_phase=0; tie_row1_drop=0; tie_row1_eq=0
tail_mono=0; tail_zero=0; tail_other=0
each_comp_monoZ_fail=0
# T5: every component slice is monoT or zeroT (==H1 applies to each)
for N in all_pairseqs(MAXLEN,MAXVAL):
    if not is_standard(N): continue
    LN=Lng(N)
    if LN<2: continue
    if entry(N,1,LN-1)==0: continue
    if idx1(N,LN-1)!=1: continue
    if not hasParent(N,1,LN-1): continue
    j0N=parent(N,1,LN-1)
    if not (j0N<LN-1): continue
    w=(LN-1)-j0N; delta=entry(N,0,LN-1)-entry(N,0,j0N)
    if delta<=0: continue
    for n in range(2,NMAX+1):
        M=oper(N,n); LM=Lng(M)
        for j0p in range(0,LM-1):
            for j1p in range(j0p+1,LM):
                if not leR(M,0,j0p,j1p): continue
                Mp=seg(M,j0p,j1p)
                if not monoT(Mp): continue
                if j1p<=j0N: continue
                Tm=TrMax(Mp)
                if Tm==Lng(Mp)-1: continue
                wit+=1
                BrMp=Br(Mp); kM=len(BrMp)
                # tail kind
                tk=kind(BrMp[-1])
                if tk=='M': tail_mono+=1
                elif tk=='Z': tail_zero+=1
                else: tail_other+=1
                # each comp monoT/zeroT
                for c in BrMp:
                    if kind(c)=='X': each_comp_monoZ_fail+=1
                # cut starts absolute
                base=j0p+Tm+1
                starts=[]; acc=base
                for c in BrMp:
                    starts.append(acc); acc+=len(c)
                for J in range(1,kM):
                    p0=starts[J-1]; p1=starts[J]
                    e00=entry(M,0,p0); e01=entry(M,0,p1)
                    e10=entry(M,1,p0); e11=entry(M,1,p1)
                    if e01>e00: t1_fail+=1
                    elif e01==e00:
                        # phase = (p - j0N) % w  (block offset) when in fold
                        ph0=(p0-j0N)%w if p0>=j0N else -1
                        ph1=(p1-j0N)%w if p1>=j0N else -1
                        if ph0==ph1: tie_same_phase+=1
                        else: tie_diff_phase+=1
                        if e11<e10: tie_row1_drop+=1
                        elif e11==e10: tie_row1_eq+=1
                        else: pass # row1 increase => descending VIOLATION (should be 0)
print("=== d1pos Br cdom mechanism ===")
print(f"params {MAXLEN}/{MAXVAL}/{NMAX} witnesses={wit}")
print(f"(T1) row0 increase across cut FAIL = {t1_fail}  (expect 0)")
print(f"tail: mono={tail_mono} zero={tail_zero} other={tail_other}")
print(f"each component monoT/zeroT FAIL(multi found)={each_comp_monoZ_fail} (expect 0)")
print("--- row0-tie transitions ---")
print(f"  same-phase(block offset eq)={tie_same_phase} diff-phase={tie_diff_phase}")
print(f"  row1 drops={tie_row1_drop} row1 eq={tie_row1_eq}  (row1 increase would break descending)")
