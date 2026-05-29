#!/usr/bin/env python3
"""d1pos TrMax formula search.

Goal: find the CORRECT closed form for TrMax(seg (oper N n) j0prime j1prime)
for STANDARD d1pos opers, where:
  - i1 = idx1 N (Lng N-1) = 1            (entry N 1 (Lng N-1) > 0)
  - hasParent N 1 (Lng N-1)
  - j0N = parent N 1 (Lng N-1), w = (Lng N-1) - j0N
  - delta = entry N 0 (Lng N-1) - entry N 0 j0N > 0   (= d0 in oper; note d1=0 for i1=1)

The TrMax_seg_oper_d1pos_eq_caseA equality
  TrMax(seg M' j0p j1p) = TrMax(seg N j0p (Lng N-1))
is FALSE (counterexample N=(0,0)(1,1)(2,2)(3,3), n=1, j0p=0, j1p=2: 2 != 3).

We enumerate standard d1pos witnesses, restrict to the slices that arise in the
Red d1pos reduction (monoT slice with j0p <=_M0 j1p), compute the actual
TrMax(seg M' j0p j1p), and test candidate closed forms with a 0-failure target.
We also classify exactly when TrMax M' = TrMax N' holds vs fails.
"""
import sys, itertools
sys.path.insert(0, __file__.rsplit('/',1)[0])
from red_model import (Lng, entry, seg, oper, P, Br, TrMax, FirstNodes,
                       is_standard, parent, idx1, le0, le1, leR, monoT,
                       hasParent, nextrel1, fmt)

def all_pairseqs(maxlen, maxval):
    for L in range(2, maxlen+1):
        cells = list(itertools.product(range(maxval+1), repeat=2))
        for tup in itertools.product(cells, repeat=L):
            yield list(tup)

def d1pos_N(maxlen, maxval):
    """Yield (N, j0N, w, delta) for standard d1pos N."""
    for N in all_pairseqs(maxlen, maxval):
        if not is_standard(N):
            continue
        LN = Lng(N); j1N = LN-1
        if entry(N,1,j1N) == 0: continue
        if idx1(N,j1N) != 1: continue
        if not hasParent(N,1,j1N): continue
        j0N = parent(N,1,j1N)
        if not (j0N < j1N): continue
        delta = entry(N,0,j1N) - entry(N,0,j0N)
        if delta <= 0: continue
        w = j1N - j0N
        yield (N, j0N, w, delta)

def Mprime_trunk_end(Mp):
    """The actual TrMax: largest k with nextrel1(Mp,j',j'+1) for all j'<k."""
    return TrMax(Mp)

# ----------------------------------------------------------------------------
# VERIFIED CLOSED FORM (0 failures over the enumerated d1pos domain).
#
# Setup: N standard d1pos, j1N = Lng N - 1, i1 = idx1 N j1N = 1,
#        j0N = parent N 1 j1N, w = j1N - j0N, delta = entry N 0 j1N - entry N 0 j0N > 0.
#        M' = oper N n.  (For i1=1 the oper increments row 0 by k*delta and leaves
#        row 1 CONSTANT across the replicated tail; the original last column j1N is
#        DROPPED.)  Slice = seg M' j0p j1p, monoT, with j0p <=_{M',0} j1p.
#
# Two-level decomposition:
#   (1)  TrMax (seg M' j0p j1p) = min ( trunkM' , j1p - j0p )
#        where trunkM' = TrMax (seg M' j0p (Lng M' - 1))   [prefix-cap, generic].
#   (2)  trunkM' is expressed from the N-side:
#          if j0p <= j0N:
#              trunkM' = min ( TrMax (seg N j0p j1N) , j1N - 1 - j0p )
#                      = min ( TrMax (seg N j0p (Lng N-1)) , j0N + w - 1 - j0p )
#          else (j0p inside the replicated tail, off = (j0p - j0N) mod w):
#              trunkM' = min ( TrMax (seg N (j0N+off) j1N) , w - 1 - off )
#   The "-1" relative to N's own trunk is the d1pos correction: oper drops column
#   j1N and resets row 1 at each block boundary, so the consecutive le1-chain in M'
#   can reach at most column j1N-1 of the first block, not j1N.  That single
#   off-by-one is exactly why TrMax_seg_oper_d1pos_eq_caseA (= TrMax N') is FALSE.
# ----------------------------------------------------------------------------

def trunk_Mprime_pred(N, j0N, w, n, j0p):
    """Predicted TrMax(seg (oper N n) j0p (Lng(oper N n)-1)) from N-side data."""
    j1N = Lng(N) - 1
    if j0p <= j0N:
        return min(TrMax(seg(N, j0p, j1N)), j1N - 1 - j0p)
    off = (j0p - j0N) % w
    return min(TrMax(seg(N, j0N + off, j1N)), w - 1 - off)

def trmax_slice_pred(N, j0N, w, n, j0p, j1p):
    """Full predicted TrMax(seg (oper N n) j0p j1p)."""
    return min(trunk_Mprime_pred(N, j0N, w, n, j0p), j1p - j0p)

def run(maxlen=4, maxval=3, nmax=3, verbose=False):
    # candidate formulas keyed by name -> function(ctx)->value
    # ctx: dict with j0p,j1p,j0N,w,delta,n,LN,LM,TrNp,Mp,N,M
    cands = {}
    cands['caseA: TrNp'] = lambda c: c['TrNp']
    cands['min(TrNp, LMp-1)'] = lambda c: min(c['TrNp'], c['LMp']-1) if c['TrNp'] is not None else None
    cands['min(TrNp, j0N - j0p)'] = lambda c: min(c['TrNp'], c['j0N']-c['j0p']) if c['TrNp'] is not None else None
    # the M-prime trunk = consecutive le1 chain from j0p. In M-index it ends where the
    # replicated tail breaks the row-1 monotonic ancestry. Candidate: the prefix length
    # of N's trunk confined to [j0p, j0N], i.e. min(TrNp, j0N - j0p), but n>1 may extend.
    # candidate based on M-side directly is the ground truth; we test structural guesses:
    cands['min(TrNp, j0N+1 - j0p - 1)'] = lambda c: min(c['TrNp'], c['j0N']-c['j0p']) if c['TrNp'] is not None else None
    # the VERIFIED closed form (two-level N-side decomposition)
    cands['VERIFIED full d1pos form'] = lambda c: trmax_slice_pred(c['N'], c['j0N'], c['w'], c['n'], c['j0p'], c['j1p'])

    stats = {k: {'tested':0,'fail':0,'examples':[]} for k in cands}
    # also: when does TrMp == TrNp?
    eq_hold = 0; eq_fail = 0; eq_fail_ex = []
    # classify failing family
    fail_trunkfill = 0; fail_other = 0; fail_other_ex = []
    # conditional caseA: rule out (i) trunk-filling N' (TrNp = Lng Np-1) AND (ii) window cap (j1p-j0p < TrNp)
    condA_tested = 0; condA_fail = 0; condA_fail_ex = []

    total_slices = 0; n_N = 0
    for (N, j0N, w, delta) in d1pos_N(maxlen, maxval):
        n_N += 1
        LN = Lng(N); j1N = LN-1
        for n in range(1, nmax+1):
            M = oper(N, n); LM = Lng(M)
            for j0p in range(0, LM):
                for j1p in range(j0p+1, LM):
                    Mp = seg(M, j0p, j1p)
                    if not monoT(Mp): continue
                    if not leR(M,0,j0p,j1p): continue
                    total_slices += 1
                    TrMp = TrMax(Mp)
                    LMp = Lng(Mp)
                    # N-prime reference slice TrMax(seg N j0p (Lng N -1))
                    if j0p <= j1N:
                        Np = seg(N, j0p, j1N)
                        TrNp = TrMax(Np)
                    else:
                        Np = None; TrNp = None
                    ctx = dict(j0p=j0p,j1p=j1p,j0N=j0N,w=w,delta=delta,n=n,
                               LN=LN,LM=LM,TrNp=TrNp,LMp=LMp,N=N,M=M,Mp=Mp)
                    for k,f in cands.items():
                        try:
                            v = f(ctx)
                        except Exception:
                            v = '<err>'
                        stats[k]['tested'] += 1
                        if v != TrMp:
                            stats[k]['fail'] += 1
                            if len(stats[k]['examples'])<5:
                                stats[k]['examples'].append((fmt(N),n,j0p,j1p,'got',v,'want',TrMp,'TrNp',TrNp))
                    # conditional caseA: hypotheses ruling out the two break families.
                    # (i) N' not trunk-filling: TrNp < Lng Np - 1
                    # (ii) slice window not the binding cap: j1p - j0p >= TrNp
                    # (iii) start before/at parent edge: j0p <= j0N
                    if TrNp is not None:
                        notfill = (TrNp < Lng(Np) - 1)
                        nowin = (j1p - j0p >= TrNp)
                        before = (j0p <= j0N)
                        if notfill and nowin and before:
                            condA_tested += 1
                            if TrMp != TrNp:
                                condA_fail += 1
                                if len(condA_fail_ex) < 10:
                                    condA_fail_ex.append((fmt(N),n,j0p,j1p,'TrMp',TrMp,'TrNp',TrNp))
                    # eq classification
                    if TrNp is not None:
                        if TrMp == TrNp:
                            eq_hold += 1
                        else:
                            eq_fail += 1
                            # is N' trunk-filling? TrNp == Lng Np -1
                            trunkfill = (TrNp == Lng(Np)-1)
                            if trunkfill: fail_trunkfill += 1
                            else:
                                fail_other += 1
                                if len(fail_other_ex)<10:
                                    fail_other_ex.append((fmt(N),n,j0p,j1p,'TrMp',TrMp,'TrNp',TrNp,'Lng Np-1',Lng(Np)-1))
                            if len(eq_fail_ex)<8:
                                eq_fail_ex.append((fmt(N),n,j0p,j1p,'TrMp',TrMp,'TrNp',TrNp,'trunkfill',trunkfill))
    return dict(n_N=n_N,total_slices=total_slices,stats=stats,
                eq_hold=eq_hold,eq_fail=eq_fail,eq_fail_ex=eq_fail_ex,
                fail_trunkfill=fail_trunkfill,fail_other=fail_other,fail_other_ex=fail_other_ex,
                condA_tested=condA_tested,condA_fail=condA_fail,condA_fail_ex=condA_fail_ex)

if __name__=='__main__':
    ML=int(sys.argv[1]) if len(sys.argv)>1 else 4
    MV=int(sys.argv[2]) if len(sys.argv)>2 else 3
    NM=int(sys.argv[3]) if len(sys.argv)>3 else 3
    R=run(ML,MV,NM)
    print(f"d1pos N count: {R['n_N']}  monoT slices tested: {R['total_slices']}")
    print("--- candidate formulas (target 0 fail) ---")
    for k,v in R['stats'].items():
        print(f"  {k}: tested={v['tested']} fail={v['fail']}")
        if v['fail']:
            for e in v['examples']: print("      ", e)
    print("--- caseA equality TrMp == TrNp classification ---")
    print(f"  hold={R['eq_hold']} fail={R['eq_fail']}  (of fails: trunkfill={R['fail_trunkfill']} other={R['fail_other']})")
    print("  fail examples:")
    for e in R['eq_fail_ex']: print("      ",e)
    if R['fail_other_ex']:
        print("  NON-trunkfill fail examples (would break a conditional caseA):")
        for e in R['fail_other_ex']: print("      ",e)
    print("--- CONDITIONAL caseA (notfill & nowindow & j0p<=j0N): target 0 fail ---")
    print(f"  tested={R['condA_tested']} fail={R['condA_fail']}")
    for e in R['condA_fail_ex']: print("      ",e)
