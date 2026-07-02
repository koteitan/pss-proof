#!/usr/bin/env python3
"""r15-VX REPORT -- A28 index-shift propagation + exchange-shape audit
(python-only front; NO Isabelle changes).  2026-07-02.

Harness: _r15_vx_lib.py (shared: A23-form operB model, lessBT/leBT, Trans
internals, memoized Trans/Mark, genuine ST_PS pools, SIGALRM guards),
_r15_vx_audit.py (8 sections), _r15_vx_c3crash.py (crash root-cause + inject
demo).  Genuine regime = diagSeq seeds closed under oper (the ST_PS inductive
definition, pss_defs.thy 439-441), plus mono P-components of multi members
(in ST_PS by m_6_7_standard_P_components); per-instance SIGALRM budgets
8-20 s (timeouts counted as 'skip', never as pass/fail).

RUNS BACKING THE NUMBERS BELOW:
  [R1] `_r15_vx_audit.py all small` -- pool 1200 distinct ST members, 974 mono
       hosts, n in {1,2,3}: sections calib85/s84x/s84b/exch4/s81/s83/s86.
  [R2] `_r15_vx_audit.py s83 wide2` -- rare-regime miner (seeds u<6), pool
       8569 ST members / 7178 mono hosts: 68 condII hosts (fixed module).
  [R3] `_r15_vx_audit.py s86a small` -- exhaustive small T_B terms (<=5
       D-nodes, heads <=2) + 400 genuine Trans images: 3296 scb-core
       instances (fixed module).
  [R4] calibration: A28 minimal CEX reproduced bit-exactly; the PROVEN
       closed form m_8_5_scbdec_fseq_condV re-derived vs the python operB
       120/120 (40 hosts x n in {0,1,2}) on the FIXED module.
  [R5] `_r15_vx_c3crash.py 9 3000` -- exact r14 pool replay, 132829
       Trans/Mark call sites.
  Wider std/wide2 coverage runs for the remaining sections were still
  executing at wrap-up (small-first host order; interim signals identical);
  their logs are NOT included in the fractions below.  All FAIL claims are
  additionally backed by foreground-verified minimal counterexamples on the
  fixed module.

===============================================================================
EXECUTIVE SUMMARY
===============================================================================
1. A28 PROPAGATES TO SS 8.4 (NEW refutation): p_8_4_Trans_oper_exchange (1)
   as printed is FALSE (0/465 condIII, 0/18 condIV); the A28-shifted index
   numBT n holds STRICTLY 465/465 + 18/18.  (3) is TRUE as printed (and
   shifted).  (2) descent TRUE.
2. p_8_4_oper_basic (2) is FALSE as printed AND under EVERY (index-shift,
   iterate-count) combination -- NOT an index typo; equality is structurally
   impossible under the project operB (A23/A24 xseq re-seeding).  (1) and (3)
   are TRUE as printed ((3)'s printed numBT n is already the correct index).
3. F7 exchIV bound: min k with leBT(Trans(N[m]), operB (Trans N) (numBT k))
   is EXACTLY k = m on every reachable genuine condIV instance (never m-1).
4. SS 8.1 condI: printed indices CORRECT (equality at numBT(n-1) 1506/1506)
   and the stepT residual holds 1506/1506.  Provers may proceed verbatim.
5. SS 8.3 condII: printed m_n bookkeeping CORRECT (kind-0 multBT branch has
   no xseq tower, so no A24 shift to inherit): 68 hosts, (1) 8/8,
   (2) 196/196, (3) 204/204, (4) 204/204.
6. p_8_6_Trans_fseq_condVI: (2) printed indices CORRECT (297/297 equality),
   (3) TRUE; BUT (1) (n=1 & adm j0 leg) is FALSE on 22/117 genuine instances
   (NEW refutation).
7. p_8_6_trailing_principal_annihilable is FALSE as printed (NEW refutation;
   the mechanism behind 6): printed 2347/3296; the empirically-exact safe
   region is core-clean (v=0 or u>=v) AND ctx-clean (all D-heads of s >= v):
   1699/1699 there, bulk failures in all three other cells.
8. r14-C3 AssertionError ROOT-CAUSED AND FIXED (trans_model.py): a model
   ROBUSTNESS bug -- isPTB_str's bare `except Exception` swallowed SIGALRM
   timeouts mid-parse, returning a wrong False; scb_decomps then dropped a
   legitimate candidate and Trans crashed with "no scb decomposition
   (invariant breach)".  Deterministic injection reproduces the exact
   message; the 132829-site replay is 100% clean (no genuine invariant
   breach).  Pre-fix, a swallowed timeout could also SILENTLY flip an
   empirical scb-existence check to False (a spurious refutation) -- the
   "poisons every front" scenario.  Fixed: catch only (ValueError,
   IndexError); verified post-fix that injected timeouts propagate.

===============================================================================
PER-ITEM DETAIL
===============================================================================

ITEM 1 -- p_8_4_Trans_oper_exchange (pss_paper.thy 1906; article 4235). [R1]
  Regime: mono ST host, hasParent M 1 j1, j1>1, condIII/condIV; n in {1,2,3}.
  155 condIII + 6 condIV hosts, 465 + 18 (host,n) instances:
  (1) printed  leBT (Trans (M[n])) (Trans(M)[n-1]) : 0/465 III, 0/18 IV  FALSE
      shifted  leBT @ numBT n                      : 465/465, 18/18
      shifted STRICT lessBT @ numBT n              : 465/465, 18/18
  (2) lessBT (Trans (M[n])) (Trans M)              : 465/465, 18/18
  (3) printed  lessBT (Trans(M)[n-1]) (Trans(M[n+1])): 465/465, 18/18   TRUE
      shifted  lessBT (Trans(M)[n]) (Trans(M[n+1])): 465/465, 18/18
  Minimal CEX for (1): M = (0,0)(1,1)(2,1) (condIII), n = 1:
    Trans M = D_0 D_1 D_1 0;  M[1] = Pred M = (0,0)(1,1); Trans(M[1]) = D_0 D_1 0
    Trans(M)[0] = D_0 D_0 0  <  Trans(M[1])            -- printed (1) fails
    Trans(M)[1] = D_0(D_1 0 + D_0 D_0 0) > Trans(M[1]) -- shifted holds
  condIV minimal CEX: M = (0,0)(1,1)(2,2)(2,1), n = 1.
  CORRECTION CANDIDATE (extends A28 to SS 8.4): (1) index n-1 -> n (strict).
  Affected: task.md SS 8.4 命題（条件(III)か(IV)の下での交換関係） -- any prover
  consuming (1) as printed would chase a false statement.

ITEM 2 -- p_8_4_oper_basic (pss_paper.thy 2014; article 5000). [R1]
  (1) printed M[n] = ([1]-iter ^(j1-jm2))(M[n+1])  : 465/465, 18/18   TRUE
      (matches the proven m_8_4_oper_basic_part1 -- part (1) only).
  (2) printed Trans(M)[n-1] = Trans(([1]-iter ^(j1-1-jm2))(M[n+1]))
                                                   : 0/465, 0/18      FALSE
      A28 shift @n, same exponent                  : 0/465, 0/18      FALSE
      ANY grid d in {-1,0,+1} x e in {0..j1-jm2+1} : foreground probe on the
      minimal host: NO combination matches ('ANY (d,e) grid equality' key in
      the extended run).  NOT an index typo.  Mechanism: operB(Trans M)
      (numBT k) plants a bare innermost D_{j0} 0 seed (A24 xseq re-seeding)
      where every Trans-image carries t2.  Example M = (0,0)(1,1)(2,1), n=1:
        Trans(M)[0] = D_0 D_0 0;  Trans(M)[1] = D_0(D_1 0 + D_0 D_0 0);
        Trans-values of [1]-iterates of M[2] = (0,0)(1,1)(2,0)(3,1):
        D_0 D_1 D_0 D_1 0 / D_0 D_1 D_0 0 / D_0 D_1 0 / 0 -- no match.
      CORRECTION CANDIDATE: (2) unfixable by re-indexing; the faithful form
      must be the scb-level pairing (conclusion (3) shape) or the closed
      form (SS 8.4 analogue of m_8_5_scbdec_fseq_condV).
  (3) printed pairing Trans(M[n]) vs Trans(M)[n]   : 465/465, 18/18   TRUE
      also true at numBT(n+1) (465/465, 18/18); FALSE at numBT(n-1) (0/465,
      0/18) -- the printed n in (3) is ALREADY the A28-correct index.

ITEM 3 -- p_8_1_Trans_fseq_condI + stepT residual. [R1]  502 condI hosts:
  (1) printed EQUALITY Trans(M[n]) = Trans(M)[n-1] : 1506/1506        TRUE
  (2) descent                                      : 1506/1506        TRUE
  stepT (m_8_1_Trans_fseq_condI_comm_append_reduce hypothesis):
      Trans((M[k]) @ B) = operB (Trans M) (numBT k), B = M_[j0..<j1],
      k in {1,2,3}                                 : 1506/1506        TRUE
  NO A28 shift in SS 8.1 (kind-0 exact commutation).

ITEM 4 -- SS 8.3 condII exchange (article 3958). [R2: 68 condII hosts,
  leftDj0 split 60/8; fixed module]  m_n := n-1 if leftDj0 else n-2:
  (1) m_n = -1: Trans(M[n]) = s1 D_{M1,jm1} t2 b1  : 8/8              TRUE
  (2) m_n >= 0: Trans(M[n]) = Trans(M)[m_n]        : 196/196          TRUE
      (shifted m_n+1 fails 0/196 -- printed index confirmed exact)
  (3) Mark(M[n], jm1) = D_{M1,jm1}(t3 + (D_{M1,j0} t4) x (m_n+1))
                                                   : 204/204          TRUE
  (4) descent                                      : 204/204          TRUE
  condII inherits NO A28 shift.  (Kind-0: operB's {0}-domain multBT branch.)

ITEM 5 -- F7 exchIV intermediate bound. [R1]  6 condIV hosts, m in {1..4}:
  existence EX k <= m+3                            : 24/24            TRUE
  at printed k = m-1                               : 0/24             FALSE
  at k = m                                         : 24/24            TRUE
  min-k distribution: {m=1:{1:6}, m=2:{2:6}, m=3:{3:6}, m=4:{4:6}} --
  min k = m EXACTLY.  exchIV discharge witness is k = m, never m-1.

ITEM 6 -- p_8_6_Trans_fseq_condVI (pss_paper.thy 2215). [R1]  138 condVI:
  (2) printed EQUALITY at m_n = n-2 (adm) / n-1    : 297/297          TRUE
      (shifted m_n+1 fails 0/297 -- printed index confirmed exact)
  (3) descent                                      : 414/414          TRUE
  (1) printed (n=1 & adm j0): EX k in (1, M1j1+1],
      Trans(M[1]) = Trans(M)[0]^k                  : 95/117           FALSE
      (k searched up to M1j1+7; the 95 passes all satisfy the printed bound)
      minimal CEX: M = (0,0)(1,1)(2,2)(3,1)(4,2), j0 = 3 adm, M1j1 = 2:
        Trans M = D_0 D_2 D_1 D_2 0, Trans(M[1]) = D_0 D_2 D_1 0
        tower: [0]^1 = D_0 D_2 D_1 D_1 0; [0]^2 = D_0 D_0 0 (the outer D_0
        CAPTURES the TB(0) domain, 0 <= 0 -> xseq restart discards the tail);
        equality never holds.
      NOTE: M[1] = Pred M always, so the n=1 leg is NOT needed by the SS 8.7
      dispatcher (case [A] Pred-descent); the falsity threatens only a
      verbatim proof of p_8_6_Trans_fseq_condVI.  Weakened forms (leBT with
      the printed bound / single-operB exchVI shape) tallied in the extended
      run under keys 86(1w)/86(1x).

ITEM 6b (NEW) -- p_8_6_trailing_principal_annihilable (pss_paper.thy 2188)
  FALSE as printed. [R3: 3296 scb-core instances]
  printed EX k <= v+1                              : 2347/3296        FALSE
  core-clean (v=0|u>=v) & ctx-clean (s-heads >= v) : 1699/1699        TRUE
  core-clean & ctx-DIRTY                           : 174/522
  core-DIRTY & ctx-clean                           : 84/491
  core-DIRTY & ctx-DIRTY                           : 390/584
  Minimal CEX: t = D_0(D_1 0 + D_1 0), s = b = [], core = t (u=0, t'=D_1 0,
  v=1): t[0]^1 = D_0 D_0 0, t[0]^2 = D_0 0 -- target never reached.
  Mechanism: an s-context head u_c <= v-1 captures the escaping TB(v-1)
  domain and restarts its own xseq from the prime basis (A23/A24 semantics),
  destroying the tail the lemma wants to keep.  The proven clean-core peel
  m_8_6_trailing_principal_peel (bare, one step) is unaffected.
  CORRECTION CANDIDATE: add the context guard (all D-heads of s >= v, plus
  the core guard) to the statement.

ITEM 7 -- calib85 (A28 reproduction; harness sanity). [R1]  103 condV hosts:
  85(1) printed leBT@mn : 17/309 (FALSE, matches A28; the 17 are incidental
  equalities on the wider pool); A28 strict @mn+1 : 309/309; (2) descent
  309/309; (3) printed 309/309 and shifted 309/309 (both-index truth of (3)
  matches the A28 entry).  Plus [R4]: the A28 minimal CEX
  M=(0,0)(1,1)(1,1) reproduced value-exactly, and the PROVEN
  m_8_5_scbdec_fseq_condV closed form re-derived 120/120.

===============================================================================
C3 CRASH ROOT CAUSE (r14-S4p-C3) -- MODEL BUG, FIXED
===============================================================================
  * The assert can only fire genuinely if the SS 7.3 invariant
    (m_7_3_Trans_Mark_MarkedB, proven on RT_PS >= ST_PS) fails -- impossible
    on the chain-check pools.  [R5] replay: 132829 call sites, 0 crashes.
  * True cause: trans_model.isPTB_str `except Exception` swallowed the
    watchdog's SIGALRM exception raised mid-parse (the r14 run was
    UN-memoized under a 10 s alarm, so alarms constantly fired at random
    points); the timeout became False -> scb_decomps dropped the legitimate
    candidate -> "no scb decomposition (invariant breach)".  Deterministic
    injection (`_r15_vx_c3crash.py inject`) reproduced the exact message
    pre-fix; post-fix the injected timeout propagates.
  * FIX in trans_model.py: catch only (ValueError, IndexError).
  * No r14 recorded refutation depended on a lone scb-existence False
    (A28-A31 all have closed-form/value counterexamples), so no earlier
    conclusion is invalidated.

===============================================================================
AFFECTED task.md ITEMS
===============================================================================
  * SS 8.4 命題（条件(III)か(IV)の下での交換関係）: (1) must be proven at
    numBT n (A28-style correction entry needed); engine EX-k reductions
    unaffected.
  * SS 8.4 補題（基本列の基本性質） parts (2)(3): (2) UNPROVABLE as printed
    (not an index typo); (3) fine at printed numBT n; part (1)
    (m_8_4_oper_basic_part1) unaffected.
  * SS 8.7 dispatcher exchIV: discharge witness k = m.
  * SS 8.6 命題 (1) n=1 leg + 補題（末尾単項の零化可能性）: corrections
    needed (context guard); m>1 legs and descent chain unaffected.
  * SS 8.1 / SS 8.3: printed indices confirmed exact -- provers may proceed
    verbatim (positive assurance).

===============================================================================
COVERAGE (fractions are over the GENUINE ST_PS regime unless noted)
===============================================================================
  [R1] small pool: 1200 distinct ST members (BFS closure, maxlen 8, seeds
       u<3), 974 mono hosts; regime hosts: condI 502, condIII 155, condIV 6,
       condV 103, condVI 138, condII 4; instances n in {1,2,3} as above;
       skips 0 except a handful of >15 s Trans timeouts counted separately.
  [R2] wide2 pool: 8569 distinct ST members (seeds u<6), 7178 mono hosts,
       68 condII hosts (leftDj0 60/8) -> 204 instances, 0 skips.
  [R3] 3296 scb-core instances over exhaustive small T_B + 400 genuine
       Trans images (term-level lemma: exhaustive small terms ARE the
       genuine regime).
  [R5] 132829 Trans/Mark call sites, seeds 1..9 replay, 0 skips.
  Caveats: condIV reachable hosts are scarce (6 in [R1]; the wide2 s84x/
  exch4 re-runs were still executing at wrap-up); n range {1,2,3(,4)}.

Files: _r15_vx_lib.py, _r15_vx_audit.py, _r15_vx_c3crash.py, this report;
trans_model.py fixed (shared infra).  No .thy files touched.
"""

if __name__ == '__main__':
    print(__doc__)
