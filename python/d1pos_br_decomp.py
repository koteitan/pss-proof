#!/usr/bin/env python3
"""§6.8 d1pos (i1=1, article's 'd0pos: False' branch) Br(M') decomposition probe.

Setting (mirrors pss_mechanized.thy line ~12751 'case d0pos: False'):
  N      : standard parent, N in SkT_PS k, i1 = idx1 N (Lng N-1) = 1 (row-1 of last node > 0)
  M      = oper(N, n) = N[n]   (the fundamental-sequence / delta-block fold)
  j0N    = parent N 1 (Lng N-1)         (row-1 parent of the last node = j_{-2}^N)
  w      = Lng N - 1 - j0N              (block width)
  delta  = entry N 0 (Lng N-1) - entry N 0 j0N   ( > 0 always)
  layout : M = take j0N N @ concat_{k<n} [ (N0_j + k*delta, N1_j) : j in [j0N .. Lng N-2] ]
           i.e. n copies of the half-open block, row-0 raised by k*delta, row-1 fixed.

  slice  M' = seg M j0' j1',  with j0' < j1', j1' <= Lng M - 1, le0 M j0' j1'  (=> monoT M').
  N'     = seg N j0' (Lng N - 1)   (the corresponding N-side slice; called ?Np in the thy)

Goal: pin the EXACT structure of Br(M') and test the hypothesis
   Br M' = <prefix from N'-branches in the slice> @ [<single mono tail from the delta-fold>].

Two regimes on j0' vs j0N:
   (A) j0' <  j0N
   (B) j0N <= j0'

We tabulate: #components, head row-0 sequence (weakly decreasing?), monoT/multi of
each component, and test candidate identities. KMAX>=6, length<=5, n<=3.
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/pss-brmap/python')
from red_model import (Lng, entry, seg, oper, P, Br, TrMax, FirstNodes,
                       is_standard, parent, idx1, le0, leR, monoT, multiT,
                       zeroT, hasParent)

def all_pairseqs(maxlen, maxval):
    cells = list(itertools.product(range(maxval+1), repeat=2))
    for L in range(1, maxlen+1):
        for tup in itertools.product(cells, repeat=L):
            yield list(tup)

def head(comp):  # (row0,row1) of head of a component
    return (entry(comp,0,0), entry(comp,1,0))

def kind(comp):
    if zeroT(comp): return 'Z'
    if monoT(comp): return 'M'
    return 'X'  # multi

MAXLEN = int(sys.argv[1]) if len(sys.argv)>1 else 5
MAXVAL = int(sys.argv[2]) if len(sys.argv)>2 else 3
NMAX   = int(sys.argv[3]) if len(sys.argv)>3 else 3

stat = {
    'wit': 0, 'A': 0, 'B': 0,
    'row0_desc_fail': 0,           # head row-0 weakly decreasing across Br M'
    'cdom_fail': 0,                # full descending (row0 strict-down, ties => row1 down)
    'tail_mono_fail': 0,          # last component is monoT
    'A_idA_fail': 0, 'A_idB_fail': 0, 'A_id_any': 0,
    'B_idA_fail': 0, 'B_idB_fail': 0, 'B_id_any': 0,
    'hyp_prefix_is_takeN': 0,      # prefix == take (#-1) of Br(N') ?
    'hyp_prefix_is_takeN_fail': 0,
}
# component-count histogram keyed by (regime, #BrM', #BrN')
ccount = {}
# how the M'-component count relates to N'-component count
relhist = {}

def row0_descending(comps):
    for J in range(1, len(comps)):
        if head(comps[J])[0] > head(comps[J-1])[0]:
            return False
    return True

def cdom_descending(comps):
    # row-0 weakly decreasing, and on row-0 tie row-1 weakly decreasing
    for J in range(1, len(comps)):
        h0p,h1p = head(comps[J-1]); h0,h1 = head(comps[J])
        if h0 > h0p: return False
        if h0 == h0p and h1 > h1p: return False
    return True

for N in all_pairseqs(MAXLEN, MAXVAL):
    if not is_standard(N): continue
    LN = Lng(N)
    if LN < 2: continue
    # d1pos last node: i1 = 1  (row-1 of last node > 0), not zeroT trivially
    if entry(N,1,LN-1) == 0: continue
    if idx1(N,LN-1) != 1: continue
    if not hasParent(N,1,LN-1): continue
    j0N = parent(N,1,LN-1)
    if not (j0N < LN-1): continue
    w = (LN-1) - j0N
    delta = entry(N,0,LN-1) - entry(N,0,j0N)
    if delta <= 0: continue  # should never happen for d1pos
    for n in range(2, NMAX+1):
        M = oper(N, n); LM = Lng(M)
        for j0p in range(0, LM-1):
            for j1p in range(j0p+1, LM):
                if not leR(M,0,j0p,j1p): continue
                Mp = seg(M, j0p, j1p)
                if not monoT(Mp): continue
                # require the slice to cross j0N (the genuine hard regime, per thy crossesA0)
                if j1p <= j0N: continue
                Np = seg(N, j0p, LN-1)
                BrMp = Br(Mp)
                BrNp = Br(Np)
                kM = len(BrMp); kN = len(BrNp)
                stat['wit'] += 1
                regime = 'A' if j0p < j0N else 'B'
                stat[regime] += 1

                # --- descending / cdom checks ---
                if not row0_descending(BrMp): stat['row0_desc_fail'] += 1
                if not cdom_descending(BrMp): stat['cdom_fail'] += 1
                if kM >= 1 and not monoT(BrMp[-1]) and not zeroT(BrMp[-1]):
                    # tail allowed to be zeroT only in degenerate; else must be mono
                    stat['tail_mono_fail'] += 1

                ccount[(regime, kM, kN)] = ccount.get((regime, kM, kN), 0) + 1
                relhist[(regime, kM - kN)] = relhist.get((regime, kM - kN), 0) + 1

                # --- candidate decompositions ---
                # Hypothesis (continued-25): Br M' = (N'-branch comps in slice) @ [single mono tail]
                # Concretely test:
                #   prefix = take (kM-1) (Br N')   [the earlier comps come from N' branches]
                #   tail   = some delta-fold mono component
                if kM >= 1:
                    prefix = BrMp[:-1]
                    tail = BrMp[-1]
                    if prefix == BrNp[:len(prefix)]:
                        stat['hyp_prefix_is_takeN'] += 1
                    else:
                        stat['hyp_prefix_is_takeN_fail'] += 1

                # FirstNodes-based candidate (mirror caseC of d0zero):
                # tail = seg M (FN[J1]+j0') j1' with J1 = kN-1, prefix = take J1 (Br N')
                if kN >= 1:
                    J1 = kN - 1
                    FN = FirstNodes(Np)
                    # FN entries are absolute indices in N' (start at TrMax(Np)+1).
                    tailC = seg(M, FN[J1] + j0p, j1p)
                    expectC = BrNp[:J1] + [tailC]
                    # alt: tail starts at the delta-fold trunk junction
                    if regime == 'A':
                        if BrMp == expectC: stat['A_id_any'] += 1
                        else: stat['A_idA_fail'] += 1
                    else:
                        if BrMp == expectC: stat['B_id_any'] += 1
                        else: stat['B_idA_fail'] += 1

print("=== d1pos Br(M') decomposition probe ===")
print(f"params: MAXLEN={MAXLEN} MAXVAL={MAXVAL} NMAX={NMAX}")
for k,v in stat.items():
    print(f"  {k:24s} = {v}")
print("--- component-count histogram (regime, #BrM', #BrN') -> count ---")
for k in sorted(ccount):
    print(f"  {k} -> {ccount[k]}")
print("--- (regime, #BrM' - #BrN') histogram ---")
for k in sorted(relhist):
    print(f"  {k} -> {relhist[k]}")
