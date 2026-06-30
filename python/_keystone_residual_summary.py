"""§8.5 keystone -- residual state after the 2026-07-01 R2-anchor round
(follows the same-day telescoping round; see git log for both commits).

=====================================================================
ROUND 1 (telescoping; layerC/pss_scratch.thy, m_8_5_keystone_telescope /
_recursion / _allq / _fold_C_commute):
=====================================================================

  The keystone was previously a FLAT obligation: for every outer tower level q,
      bpHeadT (Trans (slice_q @ B)) = C (bpHeadT (Trans slice_q))        (*)
  "47/47 empirical, NOT mechanically reducible" (per the b3_markstep_skeleton
  text block), i.e. q-many independent instances of the same hard fact.

  This round formalizes (proves, green, unconditionally) a pure function-
  iteration lemma: writing z(n) for the value at tower level n and F for the
  period-fold,

      m_8_5_keystone_allq:
        zrec: z(Suc n) = F (z n)
        base: F (z 0) = C (z 0)                          -- ONE instance
        Cinv, commute: Inv (z0) closed under C, F(Cw)=C(Fw) on Inv  -- GENERIC
        ==> F (z n) = C (z n)                             -- ALL n

  So (*) for ALL q now reduces to TWO strictly smaller, independently-named
  residuals instead of one flat forall-q claim:

    R1 (BASE). The keystone at q=2 alone: F(z0)=C(z0), i.e. ONE concrete
       instance of (*) for the smallest valid q.  STILL NOT attempted/closed
       (see below) -- likely the same composition-of-w-columns difficulty as
       the general case, just frozen at one instance.

    R2 (COMMUTE).  F(Cw) = C(Fw) for w on the C-orbit of z0.  Reduced FURTHER,
       concretely, by m_8_5_fold_C_commute, to:
         anchor: for every column m < w, scb_decomp (fold op [0..<m] acc0)
                  sx (flatBT (c1 m)) bx  -- i.e. the scb-context of column m's
                  substituted core c1(m) is found WITHIN the accumulated z-part
                  at every step of the period fold.

=====================================================================
ROUND 2 (this round; layerC/pss_scratch.thy, m_8_5_anchor_col /
m_8_5_anchor_fold): R2's `anchor` MECHANICALLY REDUCED to MarkedB-nesting.
=====================================================================

  Key realization: `anchor` at column m asks for a scb_decomp of the
  accumulator `Mark N n0` (N = the host BEFORE column m, n0 = the GLOBAL
  tracked index) at `flatBT (c1 m)` where `c1 m = transC1 N' = Mark (Pred N')
  (transJm1 N') = Mark N (transJm1 N')` (N' = N @ [col], Pred N' = N).  I.e.
  `anchor` at column m is EXACTLY membership

      (Mark N n0, Mark N (transJm1 N')) in MarkedB

  -- a NESTING of two Mark-images of the SAME host N at two DIFFERENT marks.
  This is *exactly* the shape of the ALREADY-PROVEN, UNCONDITIONAL frozen-base
  theorem `Mark_MarkedB_nest` (layerB/pss_wip.thy:9245 -- "Marked nesting: for
  a reduced M and two marked columns m <= m', (Mark M m, Mark M m') in
  MarkedB", proven 0/770 empirical failures, no sorry in pss_wip.thy at all).

  New lemmas (green, unconditional, committed):
    m_8_5_anchor_col   (single column): from N in RT_PS, (N,n0) in Marked,
       (N, transJm1(N@[col])) in Marked, n0 <= transJm1(N@[col]) ==> anchor
       at that column.  Pure composition of Mark_MarkedB_nest + transC1_def +
       Pred_def (N != [] since N in RT_PS ==> N in T_PS).
    m_8_5_anchor_fold  (the \\<And>m wrapper, matching m_8_5_fold_C_commute's
       `anchor` hypothesis shape exactly): packages the per-column hyps as
       colRT / colMarked0 / colMarkedJ / colMono over m < Lng B.

  So `anchor` (raw, mysterious scb_decomp existence) now reduces to THREE
  named, much more tractable per-column conditions:
    R2a. (N, n0) in Marked            -- the GLOBAL index n0 stays marked
         w.r.t. the growing intermediate host N = Y @ take m B.
    R2b. (N, transJm1 (N @ [col])) in Marked  -- the NEXT column's own
         admissible parent index is ALSO marked w.r.t. the CURRENT host N.
    R2c. n0 <= transJm1 (N @ [col])   -- per-column MONOTONICITY of the
         tracked admissible index.
  `N in RT_PS` is FREE (no new condition): for genuine fold hosts (prefixes
  of a standard M[Suc q]) it follows from ST_PS.oper + ST_PS_take +
  m_6_7_ST_PS_subseteq_RT_PS, all already proven/frozen.

  EMPIRICAL CHECK (python/_r2_anchor_nest2.py, python/_r2_anchor_nest3.py,
  this directory): across ~164 per-column instances (randomized standard/
  reduced seeds via the yaBMS oracle, q in {2,3}, maxlen<=4/5):
    - "R2a & R2b & R2c & reduced(N) ==> anchor" held with ZERO
      counterexamples in BOTH runs (0/102 and 0/62-of-the-I/III/V-regime
      subset) -- i.e. the Mark_MarkedB_nest-based reduction ITSELF is sound,
      strong evidence the new Isabelle lemmas are not just vacuously true.
    - anchor alone (not gated on R2a/b/c) held more often (82/102, 44/62)
      than R2a&R2b&R2c (42/102, 22/62) -- i.e. there are OTHER scb_decomp
      witnesses outside the Mark_MarkedB_nest route too; that's fine, R2a-c
      is a SUFFICIENT (not necessary) route.
    - R2a/R2b/R2c do NOT hold universally: of the ~20/102 anchor failures,
      most have R2a (marked(N,n0)) FALSE, a couple have R2c (n0<=jmid)
      FALSE.  Filtering hosts to transCondI/III/V (matching the `_c2`/
      transC2 case-split that treats I/III/V uniformly) did NOT noticeably
      raise the closure rate (71% vs 80% unfiltered) -- so the true domain
      boundary is NOT simply "host in condI/III/V", it is something finer
      not yet characterized.  condV(M) of the OUTER base seed also does NOT
      suffice alone (one m=0 counterexample has condV(M)=True yet R2c
      fails: jmid=3 < n0=4) -- this is a DIFFERENT (finer-grained, per-
      column) boundary than the outer q-tower's condV(M) scoping found in
      Round 1's _rnav_descend3.py work.

  NET: R2's open content is now PRECISELY "R2a + R2b + R2c", three clean
  Marked-membership / <=  facts (not a raw scb_decomp mystery), backed by
  the already-proven Mark_MarkedB_nest.  This is a genuine further
  sharpening, in the same spirit as Round 1's R1+R2 split of the flat
  keystone.  R2a/R2b/R2c remain OPEN (not closed this round).

EMPIRICAL EVIDENCE for the Round-1 telescoping premise itself (q-uniform C;
see _rnav_descend.py/_2/_3 in this directory): across 8 hand-built seeds,
q=2..7,
  z(Suc q) = C(z q)   with C the SAME (W, vm1) pinned once at q=2->3
held in EVERY seed with condV(M) = True (the kernel's own scoping regime),
and FAILED in the one seed with condV(M) = False -- i.e. failure tracks
exactly the documented domain boundary, not a counterexample to the keystone.

WHAT WAS *NOT* ATTEMPTED / NOT CLOSED (real remaining work, for the next
pass):
  - Closing R1 (the q=2 base instance) directly -- candidate routes: (a) try
    the SAME per-column composition machinery already in the file
    (m_8_5_Mark_bpHeadT_step_condV/condVI/tt2zero/else) composed w times for
    the SMALLEST concrete w, hoping smallness makes it tractable where the
    general case wasn't; (b) look for a structural reason q=2 is special
    (e.g. Pred(M[2]) = M, no prior "history" to track) that the existing
    m_8_3_kind1_base_basepoint / m_8_5_basepoint family may already supply.
    NOT attempted this round either (focus was on R2).
  - Closing R2a/R2b/R2c (this round's new, sharper residual) -- candidate
    routes: (a) R2a looks like a per-column generalisation of
    m_8_3_kind1_base_basepoint / m_8_5_basepoint's "(M[n], jm1) in Marked
    for all n" persistence argument (currently proven only at whole-PERIOD
    q-tower granularity, M[n] for integer n -- NOT yet for the fractional
    intermediate hosts Y @ take m B with 0<m<w); generalizing that proof's
    technique (adm_prefix_agree_eq + Adm_eq_of_adm_below, both already
    proven/frozen) from "whole period steps" to "single column steps" is
    the natural next attempt.  (b) R2c (monotonicity of transJm1 across
    columns) is the least understood piece -- no existing engine addresses
    it directly; needs fresh empirical characterization (e.g. is it implied
    by transCondV/I/III at EVERY intermediate column, not just the final
    one, or does it need the FirstNodes/Joints geometry of m_8_5_Joints_
    FirstNodes_basic?).  (c) R2b is structurally the "easy" one (an Adm-
    admissibilization fact about the CURRENT host's own next-column parent)
    and may follow from adm_Adm_adm + reachability lemmas already in the
    base with modest effort.

=====================================================================
ROUND 3 (2026-07-01, this round; layerC/pss_scratch.thy,
m_8_5_marked_adm_persist / m_8_5_marked_le0_step): R2a's `adm` conjunct
CLOSED unconditionally; the `leR` conjunct's failure mode root-caused to
MULTI-BRANCH structure (NEW, unexplored avenue).  R1 confirmed NOT
independently easier than R2 (a 14th refuted route).
=====================================================================

ATTEMPT 1 (R1, REFUTED -- 14th refuted route, add to the list).  Tried the
SAME direct value-level chaining suggested by the prior round's note (b):
does `transJm1 (host_m) = n0` (the GLOBAL q-level jm1) hold for EVERY
intermediate fold column, so the ALREADY-PROVEN per-column closed-form
m_8_5_Mark_bpHeadT_step_condV/condVI/tt2zero/else (which compute `bpHeadT
(Mark M (transJm1 M))` from `Pred M`, i.e. M's OWN admissible mark) could be
chained directly, bypassing scbSubst/anchor (R2) entirely?  REFUTED
empirically (only 3/168 instances across q in {2,3,4}; q=2 is NOT
structurally special for this -- 1/82 vs 1/47 vs 1/39, statistically the
same rock-bottom rate at every q).  So R1 genuinely needs the SAME
off-diagonal-Mark machinery as R2 (computing `Mark M n0` for `n0 !=
transJm1 M` is unavoidable); R1 is not an independently-easier sub-case of
the keystone, it shares the R2 anchor bottleneck.  Do not re-attempt this
"transJm1-constancy" shortcut.

ATTEMPT 2-5 (R2a/R2c sharpening).  `(N,n0) in Marked` unfolds (Marked_def)
to `adm N n0 AND leR N 0 n0 (Lng N - 1)`.  Empirically (~340 genuine
fold-column instances): the `adm` conjunct is NEVER the obstruction (0/342
failures); ONLY `leR` fails (224/342).  This is not a coincidence: `adm N j`
(nadm_def) only inspects the TWO row-1 edges immediately adjacent to `j`,
which lie inside the prefix `N` shares with ANY extension `N @ C`, so it
transfers for free via the ALREADY-PROVEN `adm_prefix_agree_eq`.  This is
now FORMALIZED, green, unconditional, no regime hypothesis:

  m_8_5_marked_adm_persist: n0+1 < Lng N ==> adm N n0 = adm (N @ C) n0

So R2a's entire surviving open content is the `leR` (`le0`) reachability of
n0 to the GROWING right end.  Re-filtering PROPERLY to the keystone's own
regime this time (transCondV (M[q]) + the hp1/parR/coin/jm1pos hypotheses
of m_8_5_basepoint, NOT just condV(M) of the outer base seed as Round 2's
harness did -- that under-scopes and mixes in instances the keystone
machinery was never claimed to cover) gives a clean inductive picture:
writing `ok m` for `leR (host_m) 0 n0 (Lng host_m - 1)`,
  (i)  `ok (m-1) = False ==> ok m = False`, with ZERO exceptions (0/24 in
       the harness) -- once broken, le0-reachability never spontaneously
       recovers (monotone failure);
  (ii) `ok (m-1) AND nextrel0 host_m (Lng host_{m-1} - 1) (Lng host_m - 1)`
       (a DIRECT row-0 edge from the OLD last index to the NEW one)
       `==> ok m`, with ZERO exceptions (38/38) -- pure transitivity.
(ii) is now FORMALIZED as a generic (regime-independent) composition
lemma, reusable for ANY future per-column edge characterization:

  m_8_5_marked_le0_step: le0 N a c [c < Lng N], nextrel0 (N@C) c d
                          ==> le0 (N@C) a d

ROOT CAUSE of the leR failures (NEW finding, not previously identified):
genuine period blocks B frequently OPEN with a (0,0) "branch reset" column
-- entry0 does NOT increase from the previous entry, so `parent (host,0,
lastidx)` has NO row-0 parent at all (`None`): the new column starts a
FRESH `Br`/multiT branch SIBLING, not a row-0 successor of the prior entry.
Worked example (python/_r2a_branch_routing.py, `worked_example()`): for
M=(0,0)(1,1)(1,1)(1,0), q=2, appending B=[(0,0),(1,1),(1,1)] turns the host
multiT with THREE `Br` components, the growing one being its own local
subtree -- `parent(host,0,lastidx)` is genuinely `None` at the open column
and `leR` is False throughout, even though `adm` stays True the whole time.
So the `Mark_MarkedB_nest`-based "anchor via literal Marked-ness of n0"
reduction (Round 2's R2a/R2b/R2c route) is SOUND but demands something the
genuine fold does not actually need: GLOBAL row-0 trunk reachability from
n0 across branch boundaries.  HYPOTHESIS for the next round (NOT validated
or attempted as an Isabelle proof yet): Trans/Mark's own `multi` case is
`addBT (Trans trunk-part) (Trans last-branch)` (pure list-level sum, no
cross-branch substitution), so the REAL anchor witness for a freshly-opened
branch column likely lives ENTIRELY inside the trailing addBT summand (the
branch's own local Trans) and never needs n0's row-0 ancestry to reach
across branches at all.  This would explain Round 2's separate finding that
raw `anchor` (scb_decomp existence) holds MORE often (82/102, 44/62) than
the Mark_MarkedB_nest route (42/102, 22/62): the latter is sound-but-coarse.
This LOCAL/addBT route is a genuinely NEW, not-yet-explored avenue --
distinct from all 13 previously-refuted routes and from the R2a/R2b/R2c
Marked-nesting route itself (which should now be considered a closed-off
dead end for the multi-branch-opening columns specifically, though it
remains the right tool for within-branch / whole-period-boundary columns).

NET this round: R1 confirmed to share R2's bottleneck (not separately
attackable). R2a's `adm` half fully closed (unconditional). R2a's `leR`
half sharpened from "raw Marked-membership, ~40-60% empirical failure,
unclear regime" to a precise INDUCTIVE characterization (monotone-failure +
one-edge transitivity, both formalized) PLUS a root-cause diagnosis (multi-
branch opening columns) that points at a concrete, different next route
(branch-local addBT witness) rather than more case-splitting on
transCondV/I/III/VI of the moving host.

Re-run instructions: this file is documentation, not an executable check.
  - Round 1 numbers: _rnav_descend3.py (8-seed condV-scoped confirmation).
  - Round 2 numbers: _r2_anchor_nest2.py / _r2_anchor_nest3.py (per-column
    anchor / Mark_MarkedB_nest-reduction confirmation, ~164 instances).
  - Round 3 numbers: _r2a_branch_routing.py (adm/leR split, regime-proper
    filtering, monotone-failure + one-edge-transitivity confirmation, the
    worked multi-branch example).
"""
