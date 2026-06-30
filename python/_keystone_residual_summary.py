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

=====================================================================
ROUND 4 (2026-07-01, this round; layerC/pss_scratch.thy,
m_8_5_marked_requires_last_component / m_8_5_Mark_multi_raw /
m_8_5_PJ_marked0 / m_8_5_anchor_col_trunkstuck): R2a leR's trunk-stuck
failure PROVEN (not just empirical) AND a genuinely-working branch-local
replacement anchor witness found and formalized (51/51 empirical).
=====================================================================

BUG FIX (important, changes all downstream numbers vs Round 3): python/
trans_model.py's `Mark` multi/non-monoT case used Python's SIGNED `m - j0`
for the recursive call into the last P-component, diverging from Isabelle's
TRUNCATING `nat` subtraction whenever `m < j0` (negative-index Python list
wraparound vs Isabelle's `0`).  Fixed to `max(m - j0, 0)`.  Round 3's
_r2a_branch_routing.py numbers about raw `anchor` rates for multiT hosts
were computed on the BUGGY model and are UNRELIABLE; the corrected re-run
(below) tells a very different, much more positive story.

ATTEMPT 1 (formalize the Round-3 root-cause diagnosis as a THEOREM, not just
an empirical pattern).  The already-proven, frozen, unconditional
`multi_Marked_last_component` (layerB/pss_wip.thy:1220, 0/6,080 empirical):
for a multiT host M, `(M,m) \\in Marked` FORCES `Pcut M <= m`.  Its
contrapositive -- formalized as `m_8_5_marked_requires_last_component`,
green, unconditional -- says: whenever a fold column makes the host multiT
AND the tracked mark n0 still sits in the trunk (`n0 < Pcut N`), `(N,n0) \\in
Marked` is PROVABLY false.  This also revealed (by reading
`Mark_MarkedB_nest`'s OWN proof, and the existing §7.4 companion
`m_7_4_repr_multiT_step`, layerB/pss_wip.thy:11273) that the
`Mark_MarkedB_nest` route is ALREADY maximally branch-local internally (it
recurses into the SAME last P-component PJ via this SAME
`multi_Marked_last_component`) -- so reusing `Mark_MarkedB_nest` ON THE FULL
HOST N with marks n0/transJm1(N') CANNOT be rescued for trunk-stuck n0,
full stop.  This is genuinely refuted (route #15 in the strict sense: "R2a
on N itself cannot be rescued").  Committed (ee2661b).

ATTEMPT 2 (re-test raw `anchor`, the ACTUAL thing m_8_5_fold_C_commute
needs, with the bug fixed -- a DIFFERENT question from attempt 1, since
attempt 1 only refutes one ROUTE to it, not anchor itself).
_marked_last_component_probe.py (82 genuine fold-column instances, keystone's
own transCondV+hp1+parR+coin+jm1pos regime): "anchor | MONO: 54/54"; "anchor
| MULTI: 28/28" -- raw anchor holds EVERY TIME in this sample, even though
ALL 28 multiT instances are trunk-stuck (R2a provably false by attempt 1).
This means there IS a working witness, just not via Mark_MarkedB_nest-on-N.

ATTEMPT 3 (find the actual witness mechanism: hand-trace + broader sweep).
_trunk_stuck_equality.py (51 trunk-stuck multiT instances): tested whether
Mark(Nprev,n0) and transC1(Ncur) = Mark(Nprev, transJm1(Ncur)) are LITERALLY
EQUAL (a trivial reflexive scb_decomp would then suffice).  Result: equal in
45/51 (88%); for ALL 51, anchor still holds (the other 6 via a NON-trivial
but still simple scb_decomp -- a 2-symbol-prefix peel, `Dpt 0 (...)`).
Mechanism identified: Mark's OWN multiT recursion equation (NOT addBT --
that is Trans's shape; Mark's non-monoT case is the structurally simpler
`Mark M m = Mark PJ (m - Pcut M)` with PJ = drop (Pcut M) M, or the constant
`Dpt 0 0_B` when PJ=[(0,0)]) applies to BOTH n0 and transJm1(Ncur)
UNCONDITIONALLY -- no Marked-membership needed for the EQUATION itself, only
for the higher-level CLAIM that the result is the "intended" value.  Since
n0 < Pcut(Nprev) (trunk-stuck), nat subtraction clamps `n0 - Pcut Nprev` to
literal `0`: `Mark Nprev n0 = Mark PJ 0` ALWAYS.  And empirically (0/51 in
this regime) the next column's own jm1cur = transJm1(Ncur) is NEVER ALSO
trunk-stuck (jm1cur >= Pcut Nprev) -- so `transC1(Ncur) = Mark PJ (jm1cur -
Pcut Nprev)`, a REAL (non-clamped) recursive value.  `(PJ,0) \\in Marked` is
essentially FREE: `adm PJ 0` is unconditionally true for ANY pairseq
(`nadm _ 0` is never satisfiable, already-proven `adm_index0`), and `leR PJ
0 0 (Lng PJ-1)` holds because PJ -- the LAST P-component of any T_PS host --
is ALREADY KNOWN to be zero-or-mono (already-proven `m_6_2_P_components_1`,
frozen base A), and both cases give `leR` immediately (reflexively, or via
`monoT_def` directly).  So `Mark_MarkedB_nest` applied to the SMALLER PJ
(not N) at marks `0` and `jm1cur - Pcut Nprev` gives exactly the needed
`scb_decomp`, PROVIDED `(PJ, jm1cur - Pcut Nprev) \\in Marked` (a
smaller-scale analogue of R2b, call it R2b') and `Pcut Nprev <= jm1cur`
(trivial monotonicity, matching the 51/51 "never also stuck" empirical
finding).

FORMALIZED (green, layerC/pss_scratch.thy, this round):
  m_8_5_Mark_multi_raw: M \\in RT_PS, multiT M ==> Mark M m = (if drop
    (Pcut M) M = [(0,0)] then Dpt 0 0_B else Mark (drop (Pcut M) M)
    (m - Pcut M)).  UNCONDITIONAL (no Marked hypothesis) -- this is just
    Mark.psimps's non-monoT branch, extracted as a standalone reusable fact
    (mirrors the inline `raw` step already buried inside
    m_7_4_repr_multiT_step's proof, but without that lemma's Marked
    precondition).
  m_8_5_PJ_marked0: M \\in T_PS, multiT M ==> (drop (Pcut M) M, 0) \\in
    Marked.  UNCONDITIONAL.  Via adm_index0 + m_6_2_P_components_1.
  m_8_5_anchor_col_trunkstuck: N \\in RT_PS, multiT N, n0 < Pcut N,
    (drop (Pcut N) N, transJm1(N@[col]) - Pcut N) \\in Marked [R2b'],
    Pcut N <= transJm1(N@[col]) [monotonicity]
    ==> \\exists sx bx. scb_decomp (Mark N n0) sx (flatBT (transC1
    (N@[col]))) bx.  Two cases: PJ=[(0,0)] (both sides collapse to the
    SAME constant Dpt 0 0_B, trivial reflexive scb_decomp_self witness);
    PJ<>[(0,0)] (Mark_MarkedB_nest applied to PJ, via m_8_5_PJ_marked0 +
    the R2b'/monotonicity hypotheses).

NET this round: the "branch-local addBT witness" hope from Round 3 is
CONFIRMED REAL, just not in the form first guessed (it is a branch-local
Mark_MarkedB_nest-on-PJ witness, not an addBT decomposition -- addBT is
Trans's multi shape, Mark's is the simpler pure-recursion-into-PJ shape).
R2a's leR failure for trunk-stuck columns is now FULLY accounted for: it is
harmless, because anchor does not actually need it.  The genuinely OPEN
residual has SHRUNK again, from "raw leR/Marked failure, root cause
unclear" to two small, named, structurally-motivated facts about the
SMALLER PJ: R2b' (`(PJ, jm1cur - Pcut N) \\in Marked`) and the monotonicity
`Pcut N <= jm1cur`.  Both are STRONGLY supported empirically (0/51
exceptions to monotonicity in this round's sample; R2b' is exactly what
made markNj' computable in all 51 cases) but NOT YET derived from the
keystone's own transCondV regime -- that derivation (likely a structural
fact about where a freshly-opened branch's OWN admissible parent lands,
analogous to how R2b was always expected to be discharged for the
non-trunk-stuck case) is the next round's job.  Also not yet attempted: an
`_fold`-level wrapper (matching `m_8_5_anchor_fold`'s \\<And>m shape) that
case-splits each column between the existing m_8_5_anchor_col (mono /
not-trunk-stuck) and this round's m_8_5_anchor_col_trunkstuck (trunk-stuck),
to fully discharge m_8_5_fold_C_commute's `anchor` hypothesis end to end.

Re-run instructions for Round 4: python/_marked_last_component_probe.py
(monoT/multiT split + sanity checks of multi_Marked_last_component's
contrapositive), python/_trunk_stuck_equality.py (the equality/anchor
breakdown that found the 45/51 + 6/51 split), python/_branch_local_witness.py
(first exploratory pass, superseded by the other two once the bug was
found -- kept for the worked examples).

=====================================================================
ROUND 5 (2026-07-01, this round; layerC/pss_scratch.thy,
m_8_5_hasParent0_of_entry0_lt / m_8_5_R2b_of_hasParent0 /
m_8_5_trunkstuck_hyps_of_hasParent0 / m_8_5_anchor_col_trunkstuck_regime):
R2b' (mJpcut) AND pcutle BOTH reduced TOGETHER to ONE primitive numeric
hypothesis, via two ALREADY-PROVEN frozen lemmas neither previously cited
for this purpose.
=====================================================================

GOAL this round (per the task brief): derive Round 4's two remaining named
hypotheses of `m_8_5_anchor_col_trunkstuck` -- mJpcut (`(drop (Pcut N) N,
transJm1(N@[col]) - Pcut N) \\in Marked`, R2b' at PJ-scale) and pcutle
(`Pcut N <= transJm1(N@[col])`) -- from the keystone's own regime.

KEY REALIZATION (the actual route, found by re-reading `multi_Marked_last_
component`'s OWN statement rather than just its contrapositive, which is all
Round 4 had used): its FORWARD direction says, for `multiT N` and `(N,m) \\in
Marked`, `Pcut N <= m` AND `(drop (Pcut N) N, m - Pcut N) \\in Marked` --
i.e. instantiated at `m = transJm1(N@[col])`, it gives pcutle AND mJpcut
TOGETHER, for FREE, from a SINGLE hypothesis: `(N, transJm1(N@[col])) \\in
Marked`.  That hypothesis is EXACTLY R2b -- the SAME condition
`m_8_5_anchor_col` (the non-trunk-stuck case) already needs.  So Round 4's
"two small PJ-scale facts" were never independent of R2b at all; they are
literally its `multi_Marked_last_component` corollaries.

R2b on N is in turn EXACTLY the conclusion of the ALREADY-PROVEN, frozen,
UNCONDITIONAL `Marked_Pred_Adm` (layerB/pss_wip.thy:1183: for ANY `M \\in
T_PS` with `1 < Lng M` and `hasParent M 0 (Lng M-1)`, `(Pred M, Adm M
(parent M 0 (Lng M-1))) \\in Marked`) instantiated at `M = N @ [col]` --
since `Pred (N@[col]) = N` and `Adm (N@[col]) (parent (N@[col]) 0
(Lng(N@[col])-1)) = transJm1(N@[col])` by definition (`transC1_def`/
`transJm1_def`).  So R2b needs ONLY `hasParent (N@[col]) 0 (Lng(N@[col])-1)`
-- i.e. the appended column is not a fresh `(0,.)`-style branch reset
(Round 3's root-cause diagnosis), the one thing `Marked_Pred_Adm` cannot
give for free.

That `hasParent` fact reduces FURTHER, via the GENERAL (regime-free)
existence+uniqueness pattern already buried (but never extracted as a
standalone lemma) inside `oper_last_row0_haspar`'s tail
(`m_5_1_parent_exists_1` + `idxsum_parent0_unique`, both pre-existing frozen
lemmas), to the literal numeric fact `entry N 0 0 < fst col`: ANY earlier
index with row-0 value strictly less than the new column's row-0 value gives
EXISTENCE of a row-0 parent (`m_5_1_parent_exists_1`), and UNIQUENESS of
that parent is automatic from `nextrel0`'s own shape (`idxsum_parent0_
unique`) -- no extra hypothesis needed for uniqueness.

EMPIRICAL VALIDATION (python/_r4_pcutle_r2bprime.py, this round, NEW
harness; regime = the keystone's own transCondV(Mq)+hp1+parR+coin+jm1pos
filter, i.e. the exact same filter as Round 4's harnesses, re-run on the
FIXED trans_model.py):
  - 51 trunk-stuck instances (multiT(Nprev), n0 < Pcut(Nprev)) sampled
    (maxlen<=6, q in {2,3,4}, 360s budget): jm1cur (= transJm1(Ncur)) was
    DEFINED (i.e. hasParent held) in 51/51 -- ZERO "NOPARENT"/branch-reset
    cases.  pcutle held in 51/51 of those.  R2b' (mJpcut) held in 51/51 of
    the pcutle-ok cases.  entry0(col) > 0 held in ALL 51 (consistent with
    hasParent always defined).
  - Cross-checked against the INDEPENDENT, differently-coded Round-4 harness
    _marked_last_component_probe.py (28 trunk-stuck instances, q in {2,3}):
    R2b held 28/28, R2c (pcutle's un-shifted analogue, n0<=jm1cur) held
    28/28 -- fully consistent.
  - entry(N,0,0) = 0 (the prefix-anchor fact needed for the existence
    argument with j0=0) held in ALL 42 separately re-sampled hosts checked.
  - TOTAL across both harnesses: 79/79 trunk-stuck instances have a
    defined, non-reset next column (entry0(col) > entry N 0 0 = 0), and
    100% pcutle/mJpcut closure whenever that holds.  ZERO exceptions found
    to `entry N 0 0 < fst col` in this regime.

FORMALIZED (green, layerC/pss_scratch.thy, this round, e <pending merge>):
  m_8_5_hasParent0_of_entry0_lt: M \\in T_PS, 0 < Lng M - 1, entry M 0 0 <
    entry M 0 (Lng M-1) ==> hasParent M 0 (Lng M-1).  UNCONDITIONAL, GENERAL
    (no T_PS-specific machinery beyond `m_5_1_parent_exists_1` +
    `idxsum_parent0_unique`, both pre-existing).  A reusable extraction of
    `oper_last_row0_haspar`'s tail, decoupled from its row-1-derived
    `strict` hypothesis so it can be fed a DIFFERENT (here: literal index-0)
    witness.
  m_8_5_R2b_of_hasParent0: N <> [], hasParent (N@[col]) 0 (Lng(N@[col])-1)
    ==> (N, transJm1(N@[col])) \\in Marked.  UNCONDITIONAL.  Direct
    `Marked_Pred_Adm` instantiation at `N@[col]`.
  m_8_5_trunkstuck_hyps_of_hasParent0: N \\in T_PS, multiT N, N <> [],
    hasParent (N@[col]) 0 (Lng(N@[col])-1) ==> Pcut N <= transJm1(N@[col])
    [pcutle] AND (drop (Pcut N) N, transJm1(N@[col]) - Pcut N) \\in Marked
    [mJpcut].  UNCONDITIONAL.  `multi_Marked_last_component`'s FORWARD
    direction applied to the R2b fact above.
  m_8_5_anchor_col_trunkstuck_regime: N \\in RT_PS, multiT N, n0 < Pcut N,
    entry N 0 0 < fst col ==> \\exists sx bx. scb_decomp (Mark N n0) sx
    (flatBT (transC1 (N@[col]))) bx.  Assembles the chain above and feeds
    the two derived facts into the ALREADY-PROVEN (Round 4)
    `m_8_5_anchor_col_trunkstuck`, replacing its two named hypotheses
    (mJpcut, pcutle) with the SINGLE, more primitive `entry N 0 0 < fst col`.

NET this round: Round 4's "two small PJ-scale facts, not yet derived" are
now PROVEN (not just empirically supported) to be EQUIVALENT in strength to
ONE clean, primitive, numeric fact about the appended column -- the
trunk-stuck anchor case's ENTIRE remaining open content is `entry N 0 0 <
fst col` (with `entry N 0 0` itself empirically always `0`, so really just
"the appended column's row-0 value is positive", i.e. it does not open a
FRESH branch-reset).  This was NOT further reduced to an unconditional fact
of `transCondV`/the deepen-block periodicity formula this round (the
exact correspondence between `m_8_5_basepoint`'s generic "M" parameter and
the concrete per-q host `Mq` used throughout this file's surgery machinery
was not fully re-derived from first principles within this round's budget;
attempting that derivation is the natural next step, NOT a refuted route).

IMPORTANT CAVEAT found while scoping the further-closure attempt (read before
trying to discharge `entry N 0 0 < fst col` "for free"): `entry N 0 0 = 0` is
NOT a general ST_PS fact.  `ST_PS`'s base case is `diagSeq a b \\in ST_PS` for
ANY `a <= b` (`diagSeq a b ! 0 = (a,a)`, pss_defs.thy:347-348), so a base seed
can legitimately start with `entry _ 0 0 = a > 0`; `oper`/`M[n]` then PRESERVES
that same first entry verbatim (it only ever touches/extends the SUFFIX from
the row-i1 parent onward).  The python harness's `gen()` artificially restricts
to `M[0] == (0,0)` seeds only (a generator convenience, not a derived fact) --
so the "entry N 0 0 = 0 held in ALL 42 sampled hosts" empirical claim above is
true ONLY within that artificially-narrowed sample, NOT a property of ST_PS in
general.  Any future attempt to discharge `entry N 0 0 < fst col` unconditionally
must either (a) thread an explicit base-seed hypothesis `entry M_base 0 0 = 0`
(or more generally `entry M_base 0 0 < fst col`, which is all that is actually
needed) through from wherever the keystone's eventual q-tower driver fixes its
base seed, or (b) find that the keystone's true base is never a raw `diagSeq`
with `a>0` for unrelated reasons.  Neither was investigated this round -- this
is flagged so the next round does not waste a re-attempt assuming the `0` is
free.  Also unresolved (separately): which "M" `m_8_5_basepoint`/`m_8_5_deepen_
block_explicit`'s shared variable name actually binds to (the raw base seed vs
`Mq`) is not yet pinned down anywhere in `layerC/pss_scratch.thy` -- none of
`m_8_5_basepoint`, `m_8_5_deepen_block_explicit`, `m_8_5_anchor_fold`,
`m_8_5_fold_C_commute`, `m_8_5_keystone_allq` are yet jointly instantiated by a
single end-to-end driver lemma (grepped: zero hits for any of them used as
`OF` arguments to each other), so this question is open architecture, not a
one-line gap.

=====================================================================
ROUND 6 (2026-07-01, this round; layerC/pss_scratch.thy,
m_8_5_hasParent0_of_pcut_entry_lt / m_8_5_anchor_col_trunkstuck_regime2):
Round 5's `entry N 0 0 < fst col` REFUTED as a regime fact (not a "didn't get
to it" gap -- a genuine counterexample); REPLACED by a robust witness
`entry N 0 (Pcut N) < fst col`, validated 245/245 on the exact adversarial
sample that refuted the old one.  Two further sub-attempts (the end-to-end
driver, and the non-trunk-stuck leR case) explored but not closed.
=====================================================================

ATTEMPT 1 (test Round 5's caveat empirically, per a teammate's request: is
`entry N 0 0 < fst col` really harness-specific, or does it survive when M[0]
is allowed to vary?).  First confirmed (`python/_r5_entry00_varied.py`) that
even REMOVING the artificial `M[0]==(0,0)` restriction from the harness's
`gen()`, the yaBMS `is_std` oracle STILL only ever accepted `M[0]==(0,0)`
hosts (51/51) -- i.e. yaBMS's notion of "standard" is narrower than what the
harness's filter alone would suggest.  Traced this to the ARTICLE ITSELF:
`tmp/content.md:1346` explicitly states `ST_PS` in the article's formal sense
is BROADER than the "usual" standard-form notion -- the usual notion
corresponds to `u = 0` in the `diagSeq u v` base case, and the article
deliberately generalizes to arbitrary `u`.  So yaBMS validates only the
"usual" (narrow) sub-case; testing through it was Round 5's blind spot, now
identified precisely.  Independently confirmed at the `red_model.py` level
(bypassing yaBMS, using `reduced()` -- the actual `RT_PS`-relevant check):
REDUCED `M` with `entry M 0 0 != 0` genuinely exist (198 found by direct
search over small tuples), and in ALL 198, `entry M 0 0 = entry M 1 0`
exactly (0 mismatches) -- i.e. such `M` opens like `diagSeq u ...`, matching
the article's own generalization.

ATTEMPT 2 (construct a genuine `u>0` regime-satisfying counterexample).
`python/_r6_u_nonzero_search.py`: generated REDUCED (via `reduced()`, NOT
yaBMS) seeds starting `(u,u)` for `u in {1,2,3}`, applied the SAME named
regime filter as Round 4/5 (`transCondV(Mq)`, `hasParent`, `parR`, `coin`,
`jm1pos`, trunk-stuck).  RESULT: `entry N 0 0 < fst col` FAILED in 95/245
trunk-stuck instances (39%) -- e.g. `M=(1,1)(0,0)(1,0)(1,1)(1,0)`, `q=1`,
`m=1`: `entry N 0 0 = 1 = fst col = 1` (equality, not strict).  This is a
GENUINE counterexample to Round 5's hypothesis under the article's own
(broader) domain, not a "ran out of time" gap.  REFUTED ROUTE #16: "the
trunk-stuck anchor witness's existence argument can use index 0 as the row-0
parent-existence witness" -- do not re-attempt; index 0 is too far from the
appended column once `entry _ 0 0` is allowed to be the article's general
`u > 0`.

ATTEMPT 3 (hand-trace a counterexample to find a working witness).  For
`M=(1,1)(0,0)(1,0)(1,1)(1,0)`, `q=1`: `Mq=(1,1)(0,0)(1,0)(1,1)`, appended
block `B=(0,0)(1,0)(1,1)`.  At `m=1` (`Nprev = Mq@[B!0] =
(1,1)(0,0)(1,0)(1,1)(0,0)`, `col=(1,0)`): `Pcut(Nprev)=4` (the JUST-OPENED
branch, since `B!0=(0,0)` is itself a fresh reset within the SAME appended
block -- a multi-branch-opening period, the Round-3 phenomenon recurring one
level up).  `entry(Nprev,0,Pcut(Nprev)) = entry(Nprev,0,4) = 0 < fst(col) =
1` -- WORKS, even though `entry(Nprev,0,0) = 1 NOT< 1` fails.  At `m=2`
(`col=(1,1)`, `fst(col)=1`): `entry(Nprev,0,Lng(Nprev)-1)` (the OLD last
entry, an alternative "adjacent" witness also tried) `= 1`, ALSO not `< 1` --
so the "use the immediately preceding entry" idea (a natural-seeming
alternative) is REFUTED too (route #17: adjacent-predecessor witness).  But
`entry(Nprev,0,Pcut(Nprev)) = entry(Nprev,0,4) = 0` STILL works (`0 < 1`),
via a SKIP-edge in `nextrel0` (index 4 reaches index 6 directly, jumping over
index 5, since `nextrel0`'s "between" condition only requires `>=`, not a
literal adjacent chain) -- i.e. `Pcut N` (the start of `N`'s CURRENTLY OPEN
last `P`-component) is the robust witness, not "the nearest" anything.

ATTEMPT 4 (validate `entry N 0 (Pcut N) < fst col` broadly, apples-to-apples
against the SAME sample that refuted Round 5's hypothesis).
`python/_r6_pcutwitness_search.py`, identical regime/generation parameters to
Attempt 2 (`u in {1,2,3}`, `q in {1,2,3,4}`, trunk-stuck, `fst col > 0`
excluding the unrelated trivial-reset case): `entry N 0 (Pcut N) < fst col`
held **245/245** (ZERO exceptions) on the EXACT 245 rows where `entry N 0 0 <
fst col` only held 150/245.  Re-confirmed on a SEPARATE, broader/longer sweep
(`maxlen<=7`, `u in {0..5}`, `q in {1..5}`, 380s budget): **289/289** (a
DIFFERENT, larger set of trunk-stuck instances than the apples-to-apples
245 -- 744 reduced seeds scanned, 567 regime-checked, 289 trunk-stuck rows
with `fst col>0`), again ZERO exceptions.

FORMALIZED (green, layerC/pss_scratch.thy, this round):
  m_8_5_hasParent0_of_pcut_entry_lt: N \\in RT_PS, multiT N, entry N 0
    (Pcut N) < fst col ==> hasParent (N@[col]) 0 (Lng(N@[col])-1).
    UNCONDITIONAL.  Same existence+uniqueness pattern as Round 5's
    m_8_5_hasParent0_of_entry0_lt (`m_5_1_parent_exists_1` +
    `idxsum_parent0_unique`), with `Pcut N` (not `0`) as the witness index;
    `Pcut N < Lng N` comes from `Pcut_le` (UNCONDITIONAL, just needs
    `1 < Lng N`, itself from `multiT_imp_Lng_gt1`) -- no NEW base facts
    needed, just a different witness plugged into the SAME existing engine.
  m_8_5_anchor_col_trunkstuck_regime2: N \\in RT_PS, multiT N, n0 < Pcut N,
    entry N 0 (Pcut N) < fst col ==> \\exists sx bx. scb_decomp (Mark N n0)
    sx (flatBT (transC1 (N@[col]))) bx.  Same assembly as Round 5's
    m_8_5_anchor_col_trunkstuck_regime (now superseded -- this is the
    article-domain-robust version), via the unchanged
    m_8_5_trunkstuck_hyps_of_hasParent0 + m_8_5_anchor_col_trunkstuck.
  (Round 5's m_8_5_hasParent0_of_entry0_lt / m_8_5_anchor_col_trunkstuck_
  regime are NOT deleted -- they remain valid implications, just with an
  unprovable-in-general hypothesis; kept for the record / in case a future
  caller genuinely has `u=0` pinned down some other way.)

NET this round: the article's own stated generality (`ST_PS` `u>0` broader
than "usual") is now CONFIRMED to bite at the level of the keystone's own
hypothesis set, not just an abstract worry -- Round 5's witness was
fragile, the Pcut(N) witness is robust to it.  The genuinely OPEN residual
content has NOT shrunk in COUNT (still one named hypothesis,
`entry N 0 (Pcut N) < fst col`, not yet derived from `transCondV` et al.)
but has gotten STRICTLY MORE TRUSTWORTHY (245/245 on the harder sample, vs.
the old one's demonstrated 39% failure rate there).  NOT attempted this
round: (a) deriving `entry N 0 (Pcut N) < fst col` itself from the regime
(needs the not-yet-built end-to-end `m_8_5_basepoint`/`m_8_5_deepen_block_
explicit`/`m_8_5_anchor_fold` driver -- see Round 5's note, still applies
verbatim); (b) wiring `m_8_5_anchor_col_trunkstuck_regime2` into
`m_8_5_anchor_fold` via case-split (still only calls `m_8_5_anchor_col`,
confirmed by grep again this round); (c) the non-trunk-stuck `leR` case of
R2a (still fully open, `adm` only is closed); (d) R1 (still open, shares R2's
bottleneck per Round 3).

Re-run instructions for Round 6: python/_r5_entry00_varied.py (yaBMS-vs-
reduced() M[0] distribution check), python/_r6_u_nonzero_search.py (the
refuting u>0 search, 245 trunk-stuck rows), python/_r6_pcutwitness_search.py
(the Pcut(N)-witness confirmation, apples-to-apples against the same rows).

Re-run instructions for Round 5: python/_r4_pcutle_r2bprime.py (the new
targeted pcutle/R2b' harness, 51 trunk-stuck instances); cross-check via
python/_marked_last_component_probe.py's R2b/R2c columns (28 more,
independently coded).

=====================================================================
ROUND 6b (2026-07-01, same day as Round 6 above; layerC/pss_scratch.thy,
Shift/oper_Shift/entry00_lt_fstcol_Shift): a SEPARATE pass on the SAME task
brief (this campaign apparently spans a context-compaction boundary -- this
pass started without memory of Round 6 above, re-investigated the same
question, and only discovered Round 6's counterexample/regime2 fix AFTER
already formalizing a Shift-invariance argument).  Net effect: a genuine,
narrower-scope, INDEPENDENTLY TRUE side result, now correctly scoped against
Round 6's findings; does NOT change Round 6's conclusions or supersede
`m_8_5_anchor_col_trunkstuck_regime2` in any way.
=====================================================================

WHAT WAS DONE (before discovering Round 6's counterexample): formalized,
green, that `oper` COMMUTES with `Shift u M = map (lambda p: (fst p+u,snd p+u)) M`
(uniform translation of BOTH rows by u, distinct from the row-0-only
`IncrFirst`) PROVIDED `entry M 1 (Lng M - 1) > 0` holds for the OPER
ARGUMENT `M` ITSELF (not merely some downstream iterate `M[q]`) -- i.e.
exactly `m_8_5_basepoint`'s literal `cv: transCondV M` hypothesis on the
keystone's base `M`.  Confirmed empirically with ZERO exceptions (200/200
direct + 58968/58968 brute-force-filtered, python/_r6_shift_invariance.py;
an UNRESTRICTED version without the e1pos-on-M restriction found 9828/66339
genuine commutation failures, root-caused to `idx1` flipping under a
positive shift when `entry M 1 (Lng M-1) = 0`).  Formalized: `Shift`,
`Lng_Shift`, `entry_Shift`, `nextrel0_Shift`, `le0_Shift`, `nextrel1_Shift`,
`le1_Shift`, `nextR_Shift`, `leR_Shift`, `hasParent_Shift`, `parent_Shift`,
`Pred_Shift`, `idx1_Shift` (foundational relational layer, ALL
unconditional), then `nextR_parent_witness` + `oper_Shift` (the main
`(Shift u M)[n] = Shift u (M[n])` fact, reusing the ALREADY-PROVEN
`m_8_4_oper_genform` for the substantive case rather than hand-unfolding
`oper_def`), then `seg_Shift`/`append_Shift`/`take_Shift`/
`entry00_lt_fstcol_Shift` (closing arithmetic corollaries).  All green,
0 sorry/oops, no circular citation (only external cite: the already-proven
`m_8_4_oper_genform`).

THE CAVEAT (discovered only after writing the above, by reading task.md and
re-reading `_keystone_residual_summary.py` itself more carefully -- a
process/workflow lesson, not a math one): Round 6's counterexample search
(`_r6_u_nonzero_search.py`) used the SAME regime filter as every other
python harness in this campaign, `transCondV (M[q])` -- condition (V)
checked on the ITERATE `M[q]`, NOT on the base `M` directly.  `oper_Shift`'s
hypothesis is about `M` directly.  These are DIFFERENT conditions (`oper`'s
branch choice depends only on the FIXED base `M`'s own last-column row-1
entry -- once `oper(M, q)` is evaluated for varying `q`, `M` itself is the
literal first argument every time, so `entry M 1 (Lng M - 1)` is the SAME
value for every `q`; it can be `0` even when `M[q]` happens to satisfy
condV).  So `oper_Shift`'s 0/58968 clean result and Round 6's 95/245
counterexample rate are NOT in tension -- they characterize DIFFERENT
(overlapping but distinct) subsets of the keystone's candidate hosts.  This
DOES, however, surface a genuine OPEN QUESTION not previously flagged: is
`m_8_5_basepoint`'s `M` (required to satisfy `transCondV M` directly, by
the literal hypothesis list of `m_8_5_basepoint` / `m_8_5_TransCondV_
descend_kernel`) actually how the keystone is invoked in the real
termination argument, or does the real usage only ever have `transCondV`
available on some ITERATE `M[q]` (in which case `m_8_5_basepoint`'s own
domain may need re-examination, separately from the entry-N-0-0-vs-Pcut-N
question)?  NOT investigated this round; flagged for whoever next touches
`m_8_5_basepoint`'s call sites.

PROCESS LESSON (for future rounds, important): this session evidently spans
a context-compaction boundary within a SINGLE longer-running task attempt --
the task prompt this pass received described "Round 5" as the most recent
completed state, but the actual `layerC/pss_scratch.thy` / task.md / this
file on disk already contained a FULLY-WORKED "Round 6" (the regime2 fix)
that the prompt's context did not mention.  ALWAYS re-read this entire
residual-summary file (not just skim for the highest round number expected
from the task prompt) AND `git status`/`git diff` for uncommitted changes
in the target worktree BEFORE concluding what the "current frontier" is --
the task prompt itself can be stale relative to the worktree's actual disk
state when a session has been long-running or compacted.

Re-run instructions for Round 6b: python/_r6_shift_invariance.py (the
e1pos-restricted oper-commute confirmation, 200+58968 cases, 0 failures).

=====================================================================
ROUND 6b, part (B) (same pass; layerC/pss_scratch.thy,
m_8_5_Mark_netfold_condV): the end-to-end driver architecture investigation
the task brief asked for.  NOT a closure -- a genuine, concrete, missing
PIECE found and formalized.
=====================================================================

QUESTION (per the task brief): is there a lemma anywhere that actually
chains m_8_5_basepoint / m_8_5_deepen_block_explicit / m_8_5_anchor_fold /
m_8_5_fold_C_commute / m_8_5_keystone_allq together, instantiating F/C/
Inv/z concretely with the real Trans/Mark/BT objects?  Re-confirmed by grep
(zero hits for any of these used as `OF`-arguments to each other): still
NO -- this remains true even after Round 6's regime2 advances.

WHAT WAS FOUND: a pre-existing, GENERIC abstract lemma
`m_8_5_fold_of_colstep` (per-column fold telescoping, `f` an arbitrary
"column functor": `f(Y@take(Suc m)B) = op m (f(Y@take m B))` for all
`m<Lng B` implies `f(Y@B) = fold op [0..<Lng B] (f Y)`) ALREADY HAD A
COMMENT explicitly saying it "instantiates BOTH to the Trans netfold
(f = Trans) and to the MARK netfold (f = lambda M. Mark M jm1)" -- but
grepping for any concrete Mark-level instantiation found ZERO hits: only
the Trans-level one (m_8_5_Trans_netfold_surgery / m_8_5_Trans_netfold_
condV) had actually been written.  This is exactly the missing bridge: the
anchor chain (m_8_5_anchor_col / _fold / _trunkstuck_regime2) establishes
`scb_decomp`/`MarkedB` facts about `Mark (host) n0` -- a fact ABOUT one
fold step's substitution being well-positioned -- but nothing connected
that to a genuine `fold`-level identity for `Mark (Y@B) n0` itself.

FORMALIZED (green, layerC/pss_scratch.thy, this round):
  m_8_5_Mark_netfold_condV: given the SAME per-column membership facts
    m_8_5_Trans_netfold_condV already needs (hostR/hostP/hostJ1/hostT1:
    RT_PS/PT_PS/transJ1>0/transT1!=0_B for each host_m = (Y@take m B)@
    [B!m]), PLUS two new per-column facts (hostN0: n0 stays interior,
    n0 < Lng host_m - 1; hostMk: (Mark (Y@take m B) n0, transC1 host_m)
    \\in MarkedB -- EXACTLY what the anchor chain supplies, via MarkedB_def
    unfolding against m_8_5_anchor_col's scb_decomp conclusion):
      Mark (Y@B) n0 = fold (lambda m acc. scbSubst (transC1 host_m)
                                                     (transC2 host_m) acc)
                            [0..<Lng B] (Mark Y n0)
    Proof: instantiates m_8_5_fold_of_colstep at f := (lambda M. Mark M n0),
    discharging its `step` hypothesis via the per-column Mark recursion
    m_8_5_Mark_scbSubst_step (ALREADY proven, frozen earlier in the file --
    this is literally the SAME engine m_8_5_Mark_spine_deepen's comment
    describes as "the master-key self-similar bridge's inductive step",
    just not previously folded over a whole period).  Needed an explicit
    `op` instantiation in the final `rule ... [where f=... and op=..., OF
    step]` to avoid a "multiple unifiers" higher-order-unification failure
    (f alone under-determines op from step's shape).

WHY THIS MATTERS for the driver: `m_8_5_fold_C_commute`'s abstract `op`/
`acc0`/`anchor` hypothesis now has a CONCRETE REALIZATION matching this
lemma's `op`/`Mark Y n0`/`hostMk` exactly (same `scbSubst (transC1 host_m)
(transC2 host_m)` shape).  So instantiating `m_8_5_fold_C_commute` at
`acc0 := Mark Y n0` and feeding it THIS lemma's conclusion (rather than an
abstract `fold`) is now mechanical -- PROVIDED `hostMk` is itself supplied
by the anchor chain, which is the genuinely remaining wiring (NOT attempted
this round): `m_8_5_anchor_fold`'s conclusion is stated as raw
`scb_decomp (Mark (host_m) n0) sx (flatBT (transC1 host_{m+1})) bx`
existence, which IS `(Mark host_m n0, transC1 host_{m+1}) \\in MarkedB` by
`MarkedB_def` (an `\\exists`-unfold, mechanical) -- but `m_8_5_anchor_fold`'s
OWN hypotheses (colMarked0/colMarkedJ/colMono/colRT) are themselves NOT
yet discharged for genuine fold hosts (that's the still-open R2a/R2b/R2c
question this and prior rounds have been chipping at).  So the chain is
NOW: anchor_fold's named hyps (open) => anchor_fold (proven) => MarkedB
(mechanical unfold) => hostMk => m_8_5_Mark_netfold_condV (this round) =>
feed into m_8_5_fold_C_commute (needs matching acc0:=Mark Y n0, NOT yet
wired) => m_8_5_keystone_allq's `commute` hyp (still needs the OUTER
q-level z/F too, R1, entirely separate and still open).

NOT attempted this round (honest accounting of what remains, in order):
  (1) wire m_8_5_anchor_fold's conclusion into m_8_5_Mark_netfold_condV's
      hostMk argument (mechanical MarkedB_def unfold, NOT done -- the two
      lemmas have never been used together);
  (2) discharge m_8_5_anchor_fold's OWN per-column hypotheses for a
      genuine fold (still the open R2a leR / R2b / R2c question, now with
      the Round-6 Pcut(N)-witness available for the trunk-stuck sub-case
      but NOT the non-trunk-stuck case, and NOT derived from transCondV
      itself rather than carried as a hypothesis);
  (3) connect m_8_5_Mark_netfold_condV's `Mark Y n0`-based fold to
      m_8_5_fold_C_commute's `acc0` (needs acc0 := Mark Y n0 specifically,
      and Cinv/commute's `Inv` predicate concretely instantiated -- not
      even SKETCHED yet, since Inv must characterize whatever invariant
      lets `m_8_5_scbSubst_addBT_commute`'s own preconditions transfer
      across the WHOLE fold, not just one step);
  (4) the OUTER q-level layer of m_8_5_keystone_allq (R1: the q=2 base
      instance, confirmed in Round 3 to share R2's bottleneck, not
      separately attackable) is a COMPLETELY SEPARATE, still fully open,
      outer wrapper around everything above -- this round's progress is
      entirely at the WITHIN-PERIOD column-fold level, not the q-tower
      level.
So "the end-to-end driver" is now ONE concrete lemma closer (the netfold
SHAPE is no longer missing/unwritten), but still requires (1)-(4) above,
of which (2) and (4) are the genuinely hard, still-unsolved mathematical
content; (1) and (3) are real but more mechanical wiring work for a
future round.
"""
