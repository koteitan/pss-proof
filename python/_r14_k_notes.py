"""ROUND 14, front K — the §8.5 keystone trunk-stuck non-reset witness
residual: CLOSED (green, sorry/oops=0, both oper branches, m=0 discharged).

=====================================================================
WHAT ROUND 13 LEFT OPEN
=====================================================================
The residual `entry Mq 0 (Pcut Mq) < fst (B!m)` for TRUNK-STUCK non-reset
deepen-block columns (Mq = oper(M,q), M[q+1] = Mq @ B, host N = Mq @ take m B
multiT with jm1 < Pcut N, fst(B!m) > 0), blocked on: "the genuine block B is
not governed by any available explicit lemma" (round 13:
_r13_block_dichotomy.py found 0 blocks passing the M-level i1=1 filter, and
B is not the 1-step block of Mq).

=====================================================================
THE UNBLOCKING OBSERVATION (this round)
=====================================================================
Read directly off oper_def: oper(M, Suc q) = oper(M, q) @ copy_q in BOTH i1
branches, where copy_q = map (λj. (entry M 0 j + q*d0, entry M 1 j))
[j0..<j1], j1 = Lng M - 1, i1 = idx1 M j1, j0 = parent M i1 j1, and d0 =
entry M 0 j1 - entry M 0 j0 if i1 = 1 else 0.  So the genuine block IS
explicit at the BASE M level; round 13 only tested the i1=1 form
(m_8_5_deepen_block_explicit).  The genuine regime is DOMINATED by i1=0
bases (entry M 1 (Lng M-1) = 0), where d0 = 0 and B is the VERBATIM segment
M[j0..<j1], q-independent.  Under maxv=3 broadening, i1=1 blocks also occur
(d0 = 2 observed), so both branches were formalized.  Sanity B == copy_q:
100% of all genuine blocks (sane fraction in _r14_k_broad.py).

The witness then needs NO structure of Pcut(Mq) at all.  Instead feed
m_8_5_Pcut_witness_of_smaller_at (round 13, proven) a DIFFERENT interior
index c:

  i1=0, column m>0:  c = j0.  entry(M[q],0,j0) = entry M 0 j0 (copy 0 is
      unshifted) and fst(B!m) = entry M 0 (j0+m) >= entry M 0 j1
      > entry M 0 j0 by nextrel0's own "interior >= target" clause.  Pure
      base-level arithmetic.
  i1=0, column m=0:  the comparison is genuinely FALSE (round 13: 0/50) but
      column 0 is NEVER trunk-stuck: proven unconditionally as
      Pcut(M[q]) <= jm1 = Adm (M[q]) (parent (M[q]) 0 (Lng (M[q])-1)).
      Mechanism: (a) NEW general fact adm M (Pcut M) for multiT M
      (m_8_5_Pcut_adm): a non-admissible Pcut would give
      nextrel1 M (Pcut M - 1) (Pcut M), whose le0 conjunct chains
      (le0_trans) with le0 M (Pcut M) (Lng M - 1) to make Pcut M - 1 a
      smaller row-0 cut — contradicting Least-minimality (or monoT via
      m_6_2_not_multi_iff_le when Pcut M = 1);  (b) Pcut(M[q]) <= p0 by
      Least_le (p0 = row-0 parent of the last index is itself a cut,
      positive by multiT);  (c) adm_Adm_max lifts (a)+(b) through the
      admissibilization:  Pcut <= Adm(M[q], p0) = jm1.
  i1=1, ANY m (incl. m=0):  c = Lng(M[q-1]) + m, the SAME-OFFSET column of
      the PREVIOUS period copy: value entry M 0 (j0+m) + (q-1)*d0, exactly
      d0 below fst(B!m) = entry M 0 (j0+m) + q*d0, and d0 >= 1 because the
      row-1 parent's le0 conjunct forces strict row-0 increase
      (m_5_1_ancestor_basic_1).
      NB round 13's refuted "previous copy same offset: 0/80" was the i1=0
      population (d0=0 makes it non-strict); gated on i1=1 it is exact.

=====================================================================
GREEN LEMMAS (layerC/pss_scratch.thy, appended block; build green
`Finished PSS_C`==1, real-error grep 0, sorry/oops 0; no p_* citations)
=====================================================================
  m_8_5_oper_genform0            i1=0 general form of M[n] (missing sibling
                                 of m_8_4_oper_genform; verbatim copies)
  m_8_5_deepen_block_explicit0   i1=0 explicit deepen block (q-independent)
  m_8_5_Pcut_adm                 adm M (Pcut M) for M in T_PS, multiT M
                                 (NEW general fact, no regime content)
  m_8_5_Pcut_le_Adm_parent0      Pcut M <= Adm M (parent M 0 (Lng M-1))
                                 (the m=0 / "column 0 never trunk-stuck"
                                 exclusion; general, no oper content)
  m_8_5_witness_of_small_prefix  host transport: interior-index witness on
                                 prefix Y => Pcut-witness on Y @ Z
  m_8_5_basecut_small0           i1=0, 0<m: the c=j0 seed  EX c < Lng M[q]
  m_8_5_basecut_small1           i1=1, any m: the previous-copy seed
  m_8_5_basecut_residual         THE ROUND-13 RESIDUAL literally:
                                 entry (M[q]) 0 (Pcut (M[q])) < fst (B!m),
                                 trunk-stuck-gated, both branches, m=0
                                 discharged (not hypothesized)
  m_8_5_trunkstuck_basecut_witness  the witness at the fold host
                                 entry N 0 (Pcut N) < fst(B!m),
                                 N = M[q] @ take m B (the `strict` hyp of
                                 m_8_5_anchor_col_trunkstuck_regime2, now
                                 DERIVED from the regime)
  m_8_5_anchor_col_trunkstuck_basecut  wiring: the R2a trunk-stuck ANCHOR
                                 scb_decomp obligation with no witness
                                 hypothesis left (via ..._regime2)
  m_8_5_colcase_trunkstuck_basecut  the literal SECOND DISJUNCT of
                                 m_8_5_anchor_fold_mixed's colcase at
                                 Y = M[q], n0 = jm1

Hypotheses carried by the composed lemmas (all regime facts, all checked
empirically as automatically-true in the genuine regime, see coverage):
  Lng M - 1 > 0;  last column not (0,0);  hasParent M (idx1 M j1) j1
  (equivalently: the oper copy branch is taken — otherwise B = [], vacuous);
  0 < q;  M[Suc q] = M[q] @ B;  m < Lng B;  M[q]@take m B in RT_PS, multiT;
  hasParent (M[q]) 0 (Lng (M[q]) - 1)   [E4: 100% in regime];
  stuck: jm1 < Pcut (M[q] @ take m B)   [the trunk-stuck gate itself].

=====================================================================
EMPIRICAL COVERAGE (genuine regime = random RT_PS members through the EXACT
keystone filters condV(Mq)/hasParent(Mq,1,j1)/nextrel0(Mq,p1,j1)/
p1=parent(Mq,0,j1)/jm1>0/oper-extension/non-reset/reduced/multiT — same
population style as rounds 10-13, BROADENED to maxv=3, u in 0..4, q in 1..7,
maxlen 6; harnesses python/_r14_k_broad.py, python/_r14_k_branch.py)
=====================================================================
  _r14_k_branch.py (7 seeds 11/222/3333/44444/5/606/7007, q 1..5;
  110 genuine blocks = 89 i1=0 + 21 i1=1, 91 trunk-stuck non-reset rows):
  - E5 final witness entry(Nprev,0,Pcut Nprev) < fst(B!m): 91/91 (100%).
  - E1a stuck => m>0 (i1=0): 91/91;  E1b fc == entry M 0 (j0+m): 188/188;
    E1c interior >= entry M 0 j1: 91/91;  E1d entry(Mq,0,j0)=entry(M,0,j0):
    91/91.
  - E2a fc formula: 60/60;  E2b previous-copy value: 60/60;  E2c d0>=1:
    21/21;  E2d strict prevcopy < fc (ALL m): 60/60.
  - E3 Pcut(Mq) <= jm1: 110/110;  E3b adm(Mq, Pcut Mq): 110/110;
    E4 hasParent(Mq,0,last): 110/110.
  - NOTE: stuckrows within i1=1 blocks: 0 — every OBSERVED trunk-stuck row
    came from an i1=0 block; the i1=1 lemma (m_8_5_basecut_small1) covers
    ALL m unconditionally (strictly stronger than the stuck-gated need),
    but its stuck-regime instances are vacuous in-sample.  Honest caveat.
  high-q robustness (in-module sweep, q 2..7, seeds 91..94, see
  scratch log r14k_hiq.log / re-runnable via _r14_k_branch.sweep):
  100% again on all checks (first seed: E5 24/24, E3 28/28, E1a 24/24).

  _r14_k_broad.py (seeds 555/321/7/99/2024/13 aggregated at wrap-up time —
  12 of the 18 scheduled runs; the remaining seeds 42/1234/777 were still
  running at commit time, re-run to extend; q 1..5, rand + stps
  populations):
  - 86 genuine blocks = 74 i1=0 + 12 i1=1; sanity B == copy_q: 86/86.
  - RESIDUAL entry Mq 0 (Pcut Mq) < fst(B!m) on stuck non-reset cols:
    75/75 (100%).
  - V <= fst(B!0): 86/86;  Vdist {1: 42, 2: 33};  min fst(B!m) = 2;
    m0stuck = 0.
  - K2 Pcut(Mq) <= jm1: 86/86;  K2b adm(Mq, Pcut Mq): 86/86;
    K2c Pcut(Mq) <= p0: 86/86;  K3 fc > fst(B!0) on stuck m>0: 75/75;
    K4 entry(Nprev,0,j0M) < fc: 75/75.
  COMBINED final-witness coverage across all three harness runs at commit
  time: 75/75 (broad) + 91/91 (branch) + 41/41 (hiq seeds 91-92) =
  207/207 trunk-stuck non-reset rows, 15 independent seeds, q 1..7,
  ZERO exceptions.
  - V = entry Mq 0 (Pcut Mq) is NOT constant 1 under maxv=3 (values 1 AND 2
    observed) — round 13's "constant 1" was a maxv=2 artifact, as suspected;
    the closed proof never uses any bound on V.
  - m==0 never trunk-stuck: 0 occurrences (and now a THEOREM,
    m_8_5_Pcut_le_Adm_parent0).
  - diagSeq-iterate population (gen_stps): 0 genuine blocks — condV(Mq)
    never fires on short diagSeq oper-iterates (their last-column parent
    links give condIII, and genuine condV instances exceed the Lng<=16
    budget), so the RT_PS-random population remains the only practical
    genuine-regime sampler at this size; this matches rounds 10-13.

=====================================================================
WHAT REMAINS (NOT this front's residual, recorded for the roadmap)
=====================================================================
  - The colcase disjunct for NON-trunk-stuck columns (R2a's leR gap) is
    still the separate named open — m_8_5_colcase_trunkstuck_basecut covers
    exactly the trunk-stuck disjunct; a future end-to-end fold driver must
    cases-combine the two.
  - The assembly wall (F q-independence, keystone itself) — out of scope.
  - The composed lemmas take `hasParent (M[q]) 0 (Lng (M[q]) - 1)` and the
    regime facts as hypotheses; deriving hp0(M[q]) from condV(M[q]) +
    hasParent(M[q],1,·) + parR (where the kernel supplies them) is trivial
    in the wiring context (idxsum_parent0_unique on parR's nextrel0), not a
    mathematical gap.

REFUTED/NEGATIVE this round: none new (the round confirmed rather than
refuted); the two prior refutations relevant here were RE-SCOPED, not
contradicted: "previous copy same offset 0/80" (round 13) is an i1=0-only
failure (d0=0), exact on i1=1; "Pcut(Mq)==j0M" (round 12, 21/174) remains
false in general (0/17 to 4/12 per seed here) — the closed proof needs only
Pcut(Mq) <= jm1, never its exact location.

Re-run: python3 python/_r14_k_broad.py 110 555 321 7 99 2024 13 42 1234 777
        python3 python/_r14_k_branch.py 100 11 222 3333 44444 5 606 7007
"""
