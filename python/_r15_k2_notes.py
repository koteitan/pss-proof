#!/usr/bin/env python3
"""ROUND 15, front K2 — R2a non-trunk-stuck leR + full anchor colcase.

===============================================================================
TASK
===============================================================================
Close the NON-trunk-stuck disjunct of m_8_5_anchor_fold_mixed's colcase
(R2a leR), do the round-14 hasParent composition stub, discharge the full
colcase (m_8_5_colcase_full) and feed it to m_8_5_anchor_fold_mixed.

===============================================================================
EMPIRICAL RESULTS (harnesses: _r15_k2_colcase.py, _r15_k2_blockpat.py,
_r15_k2_parr0.py; genuine keystone regime = EXACT r13/r14 filters:
reduced base M, block exists (M[Suc q] = M[q] @ B), condV(M[q]),
hasParent(M[q],1,j1), parR nextrel0 + coin at M[q], jm1 > 0, non-reset
fst(B!0) > 0, reduced+multiT M[q]; maxv=3, u in 0..4, q in 1..5)
===============================================================================
Notation: N_m = M[q] @ take m B (fold host at column m), L = Lng (M[q]),
N_1 = M[q] @ [B!0], jm1 = Adm(M[q], parent(M[q],0,L-1)),
ok1   = le0 N_1 jm1 L          (jm1 reaches the first appended column),
hp0N1 = hasParent N_1 0 L      (the first appended column has a row-0 parent),
stuck(m) = multiT N_m and jm1 < Pcut N_m.

blockpat totals (11 seeds, 68 blocks; i1=0: 62, i1=1: 6; w=1: 43, w>=2: 25):
  hp0N1 <=> ok1                                 68/68 (48 both, 20 neither)
  jm1 <= parent N_1 0 L   (on hp0N1 blocks)     48/48
  block patterns:  D1ALL (disjunct1 at EVERY column)      48   = the ok1 blocks
                   FAIL0 (m=0 fails BOTH disjuncts,
                          all m>=1 trunk-stuck)           20   = the !hp0N1 blocks
                   MIXED (d1 at 0, d2 later)               0
                   OTHER                                   0
  DANGER rows (non-stuck m>=1 column with R2a false)      0 / 10 non-stuck m>=1
  stuck-suffix violations (stuck then unstuck)             0
  parent of appended column >= L (m>=1)                   50/50
  ok1 blocks containing any stuck column                   0
  Mark opening identity Mark(N_1,jm1)==Mark(M[q],jm1)      0/67  (REFUTED)
colcase harness (first run, 3 seeds, 21 blocks, 37 columns):
  COLFULL (disj1 | disj2 per column)     29/37  (failures = the 8 m=0 columns
                                                 of !hp0N1 blocks)
  R2a at m=0 (marked(M[q],jm1))          21/21
  adm conjunct of R2a                    never the obstruction (as in r8)
  non-stuck columns at m>=1              0 (in this smaller sample)
  hostP monoT(N_{m+1}) per column        0/37   (REFUTED in-regime, see MAP)
parR0M base edge nextrel0(M, j0M, j1M):  i1=0: 38/38 (derivable from hp anyway),
                                         i1=1: 0 instances in sample (hypothesis
                                         carried; it is the kernel parR/coin
                                         shape at the base).

===============================================================================
NEGATIVE FINDINGS (new)
===============================================================================
N1. The colcase disjunction of m_8_5_anchor_fold_mixed is UNSATISFIABLE at
    column 0 on 20/68 (~29%) genuine blocks — exactly the blocks that later go
    trunk-stuck.  Mechanism: B!0's row-0 value equals the host minimum (e.g.
    u-opening hosts with fst(B!0) = u = entry(M,0,0)), so hasParent(N_1,0,L)
    FAILS, transJm1(N_1) is THE-underspecified, R2b/R2c unprovable; and column
    0 is never trunk-stuck (m_8_5_Pcut_le_Adm_parent0), so disjunct 2 is
    unavailable.  Example: M = (1,1)(2,2)(2,2)(2,0), q = 2.
    CONSEQUENCE: trunk-stuck and non-stuck routes NEVER genuinely mix inside
    one satisfiable fold; a fold with fully dischargeable colcase is
    d1-everywhere (ok1 blocks have NO stuck column).  The r14 trunk-stuck
    machinery is needed exactly on folds whose OPENING column has no
    transC1-shaped obligation discharge; those folds need a different
    (non-transC1) treatment of column 0.
N2. The opening step is NOT the identity: Mark(N_1, jm1) == Mark(M[q], jm1)
    failed 67/67 (so one cannot simply start the fold at m=1).
N3. hostP (monoT of every extended host, required by m_8_5_Mark_netfold_condV
    and m_8_5_Mark_fold_C_commute) is FALSE at EVERY genuine fold column
    (0/37).  ALL genuine hosts stay multiT (reach0L = 0/68: index 0 never
    reaches the appended block).  So the netfold/fold_C_commute bridge as
    stated is uninstantiable on genuine deepen blocks — see the ROUND 15 MAP
    in _keystone_residual_summary.py.

===============================================================================
GREEN LEMMAS (layerC/pss_scratch.thy, appended r15-K2 block)
===============================================================================
  m_8_5_hasParent0_of_edge     (sub-goal 2) edge into last index => hasParent;
                               discharges r14's hp0Mq from parRq
  m_8_5_Marked_Adm_edge        the m=0 basepoint (M, Adm M j0) in Marked from a
                               row-0 edge (row-1 ancestry chain + one edge)
  m_8_5_le0_cross_block        chains from below L into the block factor
                               through L (strong induction, last-edge decomp)
  m_8_5_le0_block_climb        from le0 x L, x reaches every appended column
                               (strong induction through in-block parents)
  m_8_5_entry_block_at         host value at appended position = fst(B!r)
  m_8_5_block_base_min         fst(B!0) < fst(B!m) for 0 < m (both i1 branches;
                               parR0M interior clause + explicit block forms)
  m_8_5_fold_blocker           no nextrel0 edge jumps from below L into the
                               block (position L breaks all-between)
  m_8_5_fold_parentwit         every appended column has a parent >= L
                               (seed c = L into m_5_1_parent_exists_1)
  m_8_5_ok_of_ok1              R2a le0 at every column from ok1
  m_8_5_R2a_of_ok1             R2a Marked at every column from ok1
  m_8_5_stuck_suffix           stuck(1) => stuck(m) for all m >= 1
  m_8_5_colcase_cols_ge1       trunk-stuck disjunct for all m >= 1 from stuck1
                               (r14 witness with stuck/hp0Mq DERIVED)
  m_8_5_colcase_full           THE DELIVERABLE: full colcase at every column
                               from base-level facts only (residuals: hp0N1,
                               disc = ok1 \/ stuck1, colRT)
  m_8_5_anchor_fold_kernel     colcase_full fed to m_8_5_anchor_fold_mixed:
                               the per-column anchor chain, no per-column
                               hypothesis left (except colRT)

===============================================================================
HONEST RESIDUALS / CAVEATS
===============================================================================
- hp0N1 and disc are CARRIED base-level hypotheses, not derived: N1 shows no
  theorem can remove hp0N1 while the colcase keeps its two-disjunct shape;
  disc's danger zone (hp0N1 & !ok1 & !stuck1) is empirically empty (0/68) but
  not proven empty.
- parR0M (base row-0 edge at the idx1-parent): derivable from hp for i1=0
  bases; for i1=1 it is a carried hypothesis (kernel parR/coin shape); 0
  i1=1 instances arose in this round's validation samples (r14 saw 6-21).
- Empirical samples: 68 blocks / 11 seeds (blockpat), 21 blocks / 37 columns
  (per-column detail run).  Population = random reduced hosts through the
  keystone filters, NOT certified ST_PS members (same caveat as rounds 6-14).

Re-run:
  python3 python/_r15_k2_blockpat.py 40 555 321 7 99 2024 13 42 1234 777 11 222
  python3 python/_r15_k2_colcase.py 35 555 321 7
  python3 python/_r15_k2_parr0.py
"""
