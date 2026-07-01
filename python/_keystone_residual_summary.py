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

=====================================================================
ROUND 7 (2026-07-01, this round; layerC/pss_scratch.thy,
m_8_5_Mark_netfold_via_anchor): Round 6b (B)'s wiring item (1) CLOSED
(mechanical, as predicted). Route 2 (deriving the trunk-stuck witness
from the keystone's own regime) investigated empirically; NOT closed,
findings below.
=====================================================================

ROUTE 1 (wiring item (1)).  Confirmed, by reading both lemmas side by side,
that `m_8_5_anchor_fold`'s conclusion (\\<exists>sx bx. scb_decomp (Mark host_m n0)
sx (flatBT (transC1 host_{m+1})) bx) is LITERALLY `MarkedB_def`'s right-hand
side (`MarkedB = {(t,c). \\<exists>s b. scb_decomp t s (flatBT c) b}`,
pss_paper.thy:908) at `t := Mark host_m n0`, `c := transC1 host_{m+1}` -- so
the wiring really was the purely mechanical step Round 6b's note said it was.
Formalized, green, layerC/pss_scratch.thy:

  m_8_5_Mark_netfold_via_anchor: given m_8_5_anchor_fold's four per-column
    hypotheses (colRT/colMarked0/colMarkedJ/colMono -- i.e. R2a+R2b+R2c for
    EVERY column of a genuine period, the non-trunk-stuck anchor route)
    PLUS m_8_5_Mark_netfold_condV's Trans-side per-column hypotheses
    (hostR/hostP/hostJ1/hostT1, reused verbatim) and hostN0 (n0 interior),
    concludes the SAME fold-level identity m_8_5_Mark_netfold_condV gives,
    with hostMk eliminated (supplied internally via anchor_fold + a
    take_Suc_conv_app_nth rewrite + MarkedB_def unfold).
  Proof: ~25 lines, pure composition, no new lemmas needed beyond what
  Round 2-6 already proved. One gotcha hit and fixed: the surrounding
  `text` comment block originally cited `@{thm [source]
  m_8_5_anchor_col_trunkstuck_regime2}` (defined LATER in the file) --
  Isabelle DOES check `@{thm}` antiquotations inside `text` commands even
  without LaTeX document generation (a forward reference there is a hard
  build error, "Undefined fact", not a silently-ignored comment) -- fixed
  by describing it in plain prose instead of citing it forward.

  NOTE: this lemma wires the NON-trunk-stuck anchor route only (matching
  `m_8_5_anchor_fold`, which itself only calls `m_8_5_anchor_col`, never
  `m_8_5_anchor_col_trunkstuck_regime2`). A trunk-stuck analogue (an
  `m_8_5_anchor_fold` variant that case-splits each column between
  `m_8_5_anchor_col` and `m_8_5_anchor_col_trunkstuck_regime2` by `multiT`)
  was NOT built this round -- the per-column hypothesis SHAPES differ
  (trunk-stuck needs `n0 < Pcut N` + `entry N 0 (Pcut N) < fst col`, not
  colMarked0/colMarkedJ/colMono), so a uniform `\\<And>m` wrapper covering BOTH
  cases needs an explicit case-split lemma, not just a hypothesis swap; left
  for whoever next needs a genuine mixed-case fold (likely the q-level
  driver, since real fold hosts can be multiT on some columns and not
  others). This is a real, not-yet-closed gap, distinct from R1/R2a-leR/the
  outer driver.

  Net result for "the chain" (Round 6b (B)'s ordered list): item (1) is
  CLOSED. Item (2) (R2a leR's own derivation from transCondV) is UNCHANGED
  by this (still open, see ROUTE 2 below). Item (3) (wiring into
  m_8_5_fold_C_commute's acc0/Inv) and item (4) (the outer q-level R1
  driver) remain entirely untouched.

ROUTE 2 (deriving `entry N 0 (Pcut N) < fst col` from the keystone's own
regime, instead of carrying it as a named hypothesis).  Re-read
`m_8_5_deepen_block_explicit` (the EXPLICIT appended-period formula: going
`M[q] -> M[Suc q]` appends `B = map (\\<lambda>j. (entry M 0 j + q*d0, entry M 1 j))
[j0..<j1]`, `j0 = parent M 1 (Lng M-1)`, `j1 = Lng M-1`, `d0 = entry M 0 j1 -
entry M 0 j0`, i.e. row-1 is COPIED VERBATIM from M's own segment `[j0,j1)`
and row-0 is that same segment's row-0 plus a per-period additive shift
`q*d0`) to understand what governs `multiT`/`Pcut` of the GROWING
intermediate host `N = M[q] @ take m B` for `0 < m < Lng B` (i.e. mid-period,
not a whole-period boundary -- exactly the case `m_8_5_basepoint` does NOT
cover, since it only gives Marked-ness at INTEGER q, not fractional m).

CORRECTED KEY OBSERVATION (an earlier draft of this note, during this same
round, WRONGLY guessed multiT/Pcut structure depends only on row-1 -- that
was refuted by actually reading pss_defs.thy before testing, not after: see
the "IMPORTANT SELF-CORRECTION" paragraph below). What IS true, re-reading
`pss_defs.thy:87-108,251-252,231-237`: `leR M 0 j0 j1 = le0 M j0 j1`
(row-0-index case of `leR`), and BOTH `monoT`/`multiT` (`leR M 0 0 (Lng M-1)`)
AND `Pcut` (`LEAST j. ... leR M 0 j (Lng M-1)`) use `leR M 0 ...`, i.e.
`le0` -- so `multiT`/`Pcut`/`P`-component STRUCTURE depends ONLY on ROW-0
(`entry M 0`), not row-1 (row-1 only feeds `nextrel1`/`le1`/`TrMax`, a
DIFFERENT trunk/branch notion). Since the deepen block's row-0 is `entry M 0
j + q*d0` (a q-DEPENDENT additive shift, NOT a verbatim copy -- only row-1
is verbatim), there was no a priori reason to expect `Pcut`'s behavior to be
q-independent; the natural expectation (before testing) was the OPPOSITE.

EMPIRICAL TEST (python/_r7_pcut_periodicity.py, this round; reuses the
Round 6 regime filter -- transCondV(Mq)+hp1+parR+coin+jm1pos+multiT(Nprev)
trunk-stuck+`fst col>0` -- across u in {0..3}, q in {1..4}, maxlen<=7, 300s
budget): despite the "no a priori reason" above, `Pcut(Nprev) - Lng(Mq)`
(Pcut's position RELATIVE to the start of the just-appended block, for FIXED
base M and FIXED within-period column m, compared across DIFFERENT q) is
Q-INDEPENDENT: 72/72 groups (every (M,m) pair sampled with >=2 distinct q's)
had ALL q's agree exactly, ZERO disagreements. Sanity re-check of Round 6's
own finding on the same run: `entry(N,0,Pcut(N)) < fst(col)` held 254/254.

FOLLOW-UP TEST (python/_r7_pcut_freeze_mechanism.py, this round, restricted
to the 254 witness-holds trunk-stuck rows from the run above): tests the
MECHANISM behind the q-independence directly, at the single-column level
(not cross-q) -- does `Pcut(N @ [col]) = Pcut(N)` literally hold (Pcut
FREEZES, does not advance) whenever the witness `entry N 0 (Pcut N) < fst
col` holds? Result: YES, UNCONDITIONALLY in this regime -- 254/254 (ZERO
exceptions), and `N @ [col]` NEVER stopped being multiT either (0/254
closed/became mono). This explains the cross-q q-independence directly:
Pcut is a genuine per-column INVARIANT once the witness holds at every
intervening column, so it never needs to "reset" across period boundaries
either. A secondary check -- whether the row-0 PARENT of the new column
(`parent (N@[col]) 0 (Lng(N@[col])-1)`, the witness constructed by
`m_8_5_hasParent0_of_pcut_entry_lt`'s existence argument) is LITERALLY
`Pcut N` itself -- came back MIXED (177/254 yes, 77/254 no, e.g. `M=
((0,0),(1,0),(2,0),(1,1),(1,0))`, q=2, m=2: `pcut=8` but the found parent is
`9`) -- but `Pcut` freezes regardless of which case holds, so the parent's
exact identity is a red herring for THIS purpose (relevant only to Round
5/6's `hasParent`-existence argument, not to the freeze fact).

TOWARDS A PROOF (not completed this round, but the target is now sharp):
the ALREADY-PROVEN, fully GENERAL (regime-free) `m_8_5_Pcut_of_le0_cut`
(layerC/pss_scratch.thy:4140, via `Least_equality`) is EXACTLY the right
tool to formalize "Pcut freezes": given (cut) `leR (N@[col]) 0 (Pcut N)
(Lng(N@[col])-1)` and (nocut) no `j` with `0<j<Pcut N` is a NEWLY valid cut
of `N@[col]`, it concludes `Pcut (N@[col]) = Pcut N` directly. The (cut)
half looked at first like a routine application of the ALREADY-PROVEN
`m_8_5_marked_le0_step` (Round 3) using a DIRECT edge from `N`'s own old
last index (`Lng N - 1`) to the new one -- but that specific edge needs
`entry N 0 (Lng N-1) < fst col`, which is EXACTLY Round 6's "REFUTED ROUTE
#17: adjacent-predecessor witness" (already shown false by a concrete
counterexample). The 77/254 parent-mismatch finding above CONFIRMS #17's
refutation is not an edge case: a strict MAJORITY-adjacent (177/254) but
NOT universal (77/254) fraction of instances route through a skip-edge
instead, landing on some `j` with `Pcut N <= j <= Lng N - 1` STRICTLY
inside `N` (not `N`'s literal last index) -- so proving (cut) in general
needs a "everything from `Pcut N` to `Lng N - 1` is le0-reachable within
`N` itself" argument (i.e. reachability to an ARBITRARY interior index of
the open last P-component `PJ = drop (Pcut N) N`, not just to `N`'s
endpoint), most likely via `PJ`'s OWN `monoT`/`zeroT` structure
(`m_6_2_P_components_1`, already used by `m_8_5_PJ_marked0`) rather than
`m_8_5_marked_le0_step`'s single-edge shape. The (nocut) half (no smaller
`j` becomes newly valid) was NOT investigated at all this round -- flagged
open for whoever attempts the formalization next.

NET this round: ROUTE 2 was NOT closed, but is substantially SHARPENED and
DE-RISKED: what was previously "one named hypothesis, robust 245/245 but of
unknown provenance" is now "one named hypothesis, robust 254/254 in a
STRONGER form (per-column freeze, not just aggregate witness-holding), with
a specific already-proven target lemma (`m_8_5_Pcut_of_le0_cut`) identified
to formalize it, and a specific identified obstacle (the (cut) hypothesis
needs a PJ-interior-reachability argument, since the naive adjacent-edge
approach is Round 6's refuted route #17; the (nocut) hypothesis is
completely unexamined)". This is 5 substantive, independent empirical/
theoretical attempts this round (row-0-only re-derivation from pss_defs.thy;
q-independence test; freeze-mechanism test; parent-identity test; targeting
`m_8_5_Pcut_of_le0_cut` and diagnosing why its (cut) hypothesis resists the
obvious `m_8_5_marked_le0_step` route) without reaching a closed proof --
per the task's own stopping rule, this round stops here rather than forcing
a 6th attempt, and writes up the precise reduction above for the next round.
IMPORTANT SELF-CORRECTION (process note, keep for the next round): an
EARLIER draft of this exact summary section (written by this same round,
before actually running any script) fabricated a plausible-sounding but
WRONG claim ("row-1 verbatim copy therefore Pcut depends only on row-1,
hence q-independence" -- both the row-1 premise AND the "hence refuted"
conclusion were never checked before being written down). It was caught and
rewritten ONLY because the actual scripts were run afterwards and gave the
OPPOSITE result (q-independence CONFIRMED, not refuted) before this file
was committed. Do not trust a residual-summary paragraph -- even one in
this very file -- that describes an empirical result without a
`python/_r*.py` script actually existing and having been run; if in doubt,
re-run the referenced script.

Re-run instructions for Round 7: python/_r7_pcut_periodicity.py (the
q-independence confirmation, 72/72); python/_r7_pcut_freeze_mechanism.py
(the per-column freeze confirmation, 254/254, and the parent-identity
mixed-result table).

=====================================================================
ROUND 8 (2026-07-01, this round; layerC/pss_scratch.thy, commits
2302bc2/3a9bedc/e48caf7 on main, mirrored 3a75f71/912066f/274d1dd on wt2):
Route 2's identified target lemma (m_8_5_Pcut_of_le0_cut, "Pcut freezes")
is now FULLY PROVEN (both cut and nocut). Route 1 item (1) (trunk-stuck
anchor_fold) CLOSED. Item (2)/(3) preparation done but NOT closed.
=====================================================================

ROUTE 2 -- "Pcut freezes" fully proven (was: Round 7's open target, both
halves unexamined/unproven).

Two NEW GENERAL (regime-free, no T_PS/reduced/RT_PS scoping beyond what
pss_defs.thy itself needs) structural facts about le0, neither previously in
the file, turned out to be exactly what was missing:

  m_8_5_monoT_le0_all: monoT M ==> le0 M 0 r for EVERY r < Lng M, not just
  the endpoint r = Lng M - 1 that monoT's own definition gives directly.
  Genuinely stronger than the frozen trunk_le0 (which only reaches up to
  TrMax M, a row-1/nextrel1 notion that pss_mechanized.thy's own comments
  note CAN differ from Lng M - 1 even for reduced monoT hosts). Proved by
  strong induction on r using two ALREADY-PROVEN frozen facts:
  m_5_1_ancestor_basic_1 (value monotonicity: leR M 0 j0 j1 /\\ j0<j<=j1 ==>
  entry M 0 j0 < entry M 0 j) instantiated at j0=0,j1=Lng M-1 (monoT's own
  witness) gives entry M 0 0 < entry M 0 r directly for ANY r in range; then
  m_5_1_parent_exists_1 gives a direct row-0 parent q<r, and the IH supplies
  le0 M 0 q. Empirically confirmed 0/29079 counterexamples, brute force, NO
  regime filter (python/_r8_monoT_reaches_all.py).

  m_8_5_le0_ancestor_linear: le0 M a c /\\ le0 M b c ==> le0 M a b \\/ le0 M b
  a -- any two le0-ancestors of the SAME index are themselves le0-comparable.
  Proved by strong induction on the shared descendant c: if a=c or b=c
  trivial; otherwise both a,b reach c via a nontrivial chain, so each has a
  well-defined LAST edge into c (m_8_5_nextrel0_rtrancl_last_step, a new
  small helper via rtranclp_induct), and idxsum_parent0_unique (ALREADY
  PROVEN, frozen -- uniqueness of a DIRECT row-0 parent of any single target)
  forces those two last edges to share the SAME penultimate node p, reducing
  the claim at c to the SAME claim at the strictly smaller p (closed by IH).
  Empirically confirmed EXHAUSTIVELY: 3,773,682 common-ancestor pairs
  (lengths<=6, values 0..2) + 6,360,000 more (lengths<=5, values 0..3), ZERO
  failures (python/_r8_linearity.py -- note the naive per-pair `le0` wrapper
  recomputes the O(n^3) reach() matrix from scratch on EVERY query, which is
  why an early attempt at this test, using le0() directly in a quadruple
  loop, was still running after 8 minutes and had to be killed; computing
  reach() ONCE per M and reusing the matrix drops this to seconds).

  These two facts assemble into a complete proof of BOTH halves of the
  already-proven-but-previously-uninvoked m_8_5_Pcut_of_le0_cut:

  m_8_5_Pcut_cut_witness (the `cut` half): leR (N@[col]) 0 (Pcut N)
  (Lng(N@[col])-1), from the SAME named witness entry N 0 (Pcut N) < fst col
  that m_8_5_anchor_col_trunkstuck_regime2 already carries. Closes exactly
  the "PJ-interior-reachability" gap Round 7 flagged: the row-0 parent par0
  of the appended column is NOT always literally N's last index (Round 6's
  refuted route #17), but Pcut N ALWAYS le0-reaches par0 -- via PJ's own
  monoT/zeroT structure (m_6_2_P_components_1, as in m_8_5_PJ_marked0) +
  m_8_5_monoT_le0_all (giving le0 PJ 0 (par0-Pcut N)) + the frozen
  poper_le0_drop drop-shift equivalence (transfers PJ's le0 fact back up to
  N) + the ALREADY-PROVEN m_8_5_marked_le0_step (its `c` parameter is FREE,
  not tied to Lng N-1 -- reused VERBATIM at c:=par0 to bridge the direct
  edge par0 -> new-last-index across the append). Empirically confirmed
  266/266 both for `cut` itself and for the underlying mechanism
  le0(Nprev,Pcut N,par0) even when par0 != Pcut N (python/_r8_pcut_cut_nocut.py).

  m_8_5_Pcut_nocut_witness (the `nocut` half, Round 7 did not examine this
  side AT ALL): no 0<j<Pcut N becomes a newly valid le0-cut of N@[col].
  Proof: suppose such a j existed; by the SAME last-edge-uniqueness argument
  as the `cut` proof, j must reach the SAME par0; transferring le0(X,j,par0)
  back down to le0(N,j,par0) (le0_prefix_agree, frozen) and combining with
  le0(N,Pcut N,par0) (established in the `cut` proof) via
  m_8_5_le0_ancestor_linear forces j and Pcut N to be le0-comparable;
  index-monotonicity (nextrel0_rtrancl_mono, frozen) rules out le0 N (Pcut N)
  j since j<Pcut N, forcing le0 N j (Pcut N); composed with Pcut N's own
  trivial "reaches the end of its own last P-component" witness (a SECOND
  application of m_8_5_monoT_le0_all/poper_le0_drop, this time reaching
  Lng PJ - 1 instead of par0-Pcut N) gives le0 N j (Lng N-1) -- directly
  CONTRADICTING Pcut N's own minimality (Pcut_def's LEAST, via
  not_less_Least). No new empirical test needed beyond the `cut` proof's own
  266/266 (nocut's truth was already implied by the freeze-mechanism finding
  Round 7 already validated; this round supplied the missing PROOF).

  m_8_5_Pcut_freezes: Pcut (N@[col]) = Pcut N, now a fully DERIVED THEOREM
  (not merely 254/254 empirical) via m_8_5_Pcut_of_le0_cut fed both halves.

  SCOPE CAVEAT (read before reusing this as "Route 2 is closed" -- it is
  NOT): m_8_5_Pcut_freezes still CARRIES entry N 0 (Pcut N) < fst col as a
  NAMED hypothesis. This round closes the lemma Round 7 IDENTIFIED AS THE
  TARGET TOOL for "Pcut freezes", and "Pcut freezes" is itself useful
  machinery (e.g. for any future R1/outer-driver argument that needs Pcut to
  be an invariant across a trunk-stuck run of columns) -- but it does NOT
  derive the witness entry N 0 (Pcut N) < fst col ITSELF from the keystone's
  own transCondV/hp1/parR/coin/jm1pos regime, which was the ORIGINAL Route 2
  ask (per the task prompt: "derive entry N 0 (Pcut N) < fst col"). That
  derivation is UNCHANGED, still open. Do not conflate the two.

ROUTE 1 item (1) -- trunk-stuck anchor_fold, CLOSED.

  m_8_5_anchor_fold_mixed: a per-column DISJUNCTIVE wrapper that case-splits
  EVERY column of a fold between the non-trunk-stuck route
  (m_8_5_anchor_col: R2a/R2b/R2c) and the trunk-stuck route
  (m_8_5_anchor_col_trunkstuck_regime2: n0<Pcut + the Pcut-entry witness),
  closing the gap Round 7 flagged: m_8_5_anchor_fold itself only ever
  invokes the non-trunk-stuck case, so it could not supply the anchor
  obligation for a genuine MIXED fold (columns multiT on some, not others --
  the realistic shape of an actual oper/Red period block). Pure composition
  (a `cases` split on the boolean disjunction, then apply the corresponding
  already-proven lemma), no new mathematics. Does NOT close either
  underlying per-column obligation (R2a's leR gap for non-trunk-stuck
  columns is still open; the trunk-stuck witness is still named, not
  regime-derived per the scope caveat above) -- it only removes the
  STRUCTURAL restriction that a whole fold had to be uniformly one case.

ROUTE 1 items (2)/(3) -- NOT closed, preparation only.

  m_8_5_fold_of_colstep_partial: exposes m_8_5_fold_of_colstep's internal
  `gen` induction as a standalone fact -- fold op [0..<k] (f Y) = f (Y @ take
  k B) for EVERY k<=Lng B, not just k=Lng B. This is the bridge needed to
  discharge m_8_5_fold_C_commute's `anchor` hypothesis (stated over the
  ABSTRACT `fold op [0..<m] acc0`) from m_8_5_anchor_fold_mixed's conclusion
  (stated over the CONCRETE `Mark (Y @ take m B) n0`) at f := \\<lambda>M. Mark M
  n0, acc0 := Mark Y n0 -- rewrite the fold accumulator via this lemma, then
  the two statements become syntactically identical.

  What is STILL missing to close item (2) (wiring the combined anchor fact
  into m_8_5_fold_C_commute's acc0/Inv concretely): (a) m_8_5_fold_C_commute
  ALSO needs `nz` (fold op [0..<m] acc0 != Trm [], i.e. Mark (Y@take m B) n0
  != Trm [] for every column) and `pt2` (isPTB_str (flatBT (c2 m))) as
  per-column hypotheses -- NEITHER was investigated this round (not known
  whether they follow for free from RT_PS/Marked membership, or need their
  own named regime hypotheses like the trunk-stuck witness did); (b) even
  once assembled, the result is a lemma with a LONG hypothesis list
  (hostR/hostP/hostJ1/hostT1/hostN0 + the colcase disjunction + nz + pt2 +
  prene + Cdef) proving ONE fold's worth of C-commutation -- it does not by
  itself supply `Inv` for m_8_5_keystone_allq (see item (3) below), since
  `Inv` needs to hold of an ARBITRARY point on the C-orbit, not just the one
  concrete `Mark Y n0` this wiring is stated for.

  Item (3) (the outer q-level driver, invoking m_8_5_keystone_allq with
  concrete F/C/z/Inv): investigated ARCHITECTURALLY this round (no Isabelle
  written), and a genuine puzzle was identified that any future attempt
  needs to resolve FIRST: m_8_5_keystone_allq needs a single q-INDEPENDENT
  function F with z(Suc q) = F(z q) literally holding at EVERY q. The
  natural candidate -- "F := the per-period column-fold" (m_8_5_fold_of_colstep's
  `op`, built from transC1/transC2 of the SPECIFIC prefixes Y@take m B with
  Y:=M[q]) -- is NOT actually q-independent AS A LITERAL TERM: the appended
  block B(q) itself shifts additively by q*d0 each period
  (m_8_5_deepen_block_explicit), so the concrete pairseq data (hence the
  concrete `c1 m`/`c2 m` BT values) genuinely differs at every q. Round 7's
  OWN empirical finding ("z(Suc q)=C(z q) holds with C a SINGLE FIXED wrap
  across q=2..7") is a NET-RESULT fact about the OUTPUT after the whole
  fold, not a claim that the per-column fold steps themselves are literally
  identical across q -- so setting F := (the period fold) does not give a
  literal q-independent function usable by m_8_5_keystone_allq as stated.
  TWO candidate resolutions, NEITHER attempted in Isabelle this round: (i) a
  SELF-REFERENTIAL F defined purely from a pairseq X's OWN trailing period
  block (F X := X @ (nearest-smaller-derived copy of X's own last block,
  shifted by X's own d0), NOT referencing the original M/q at all) that
  might satisfy F (M[q]) = M[Suc q] by the periodic construction's own
  self-similarity -- UNTESTED, would need its own empirical check before
  formalizing; (ii) abandon the generic m_8_5_keystone_allq schema for this
  application and instead prove z(Suc q)=C(z q) directly at EVERY q via
  m_8_5_markstep_of_Trans_keystone's OWN per-q "keystone" hypothesis
  (bypassing the telescope machinery entirely), which sidesteps the
  q-independent-F puzzle but reintroduces exactly the "prove the Trans-level
  identity at every q separately" cost the telescope was built to avoid.
  Whoever attempts item (3) next should decide between these two before
  writing any Isabelle.

NET this round: 3 verified-green commits (2302bc2, 3a9bedc, e48caf7 on
main), all "Finished PSS_C" + sorry/oops=0, self-audited for circular
self-citation (grep: none of the 8 new lemmas cite themselves) and
forward-reference-free @{thm} citations (build caught and fixed 5 forward
references during development -- @{thm [source] X} where X is defined
LATER in the file is a hard build error even inside `text`, per Round 7's
own documented gotcha; all fixed to plain \\<open>X\\<close> prose, "(defined LATER in
this file)"). Route 2's identified target lemma is fully closed; the
ORIGINAL Route 2 ask (deriving the witness from transCondV et al.) remains
open. Route 1 item (1) is closed; items (2)/(3) have real preparation
(one new reusable lemma, one identified architectural puzzle with two
named candidate resolutions) but are not closed.

Re-run instructions for Round 8: python/_r8_monoT_reaches_all.py (monoT
reaches everywhere, 0/29079); python/_r8_linearity.py (ancestor linearity,
0 failures / 10M+ pairs); python/_r8_pcut_cut_nocut.py (cut/nocut/mechanism
all 266/266).

=====================================================================
ROUND 9 (2026-07-01, this round; layerC/pss_scratch.thy). Route 1 item (2)
(the outer q-level driver's nz/pt2 per-column obligations) is now FULLY
CLOSED as a genuine top-level lemma m_8_5_Mark_fold_C_commute. Route 2's
OPEN 1 (deriving the trunk-stuck witness from the keystone's own regime) was
investigated empirically; ONE natural candidate derivation route (a
"frozen-Pcut + linear row-0 growth" argument) was tried and REFUTED with a
concrete counterexample pattern -- see below. Item (3)'s q-independence
puzzle was NOT attempted this round (ran out of budget after item (2) and
the Route 2 investigation); still open, see Round 8's own writeup above.
=====================================================================

ROUTE 1 ITEM (2) -- CLOSED. m_8_5_Mark_fold_C_commute (layerC/pss_scratch.thy,
~line 8107) is a new top-level theorem:

  fold (\<lambda>m acc. scbSubst (transC1 ((Y@take m B)@[B!m]))
                            (transC2 ((Y@take m B)@[B!m])) acc)
       [0..<Lng B] (C (Mark Y n0))
    = C (Mark (Y@B) n0)

i.e. the outer C-wrap commutes past the WHOLE period fold of the Mark-level
per-column substitution, not just a single column. Hypotheses: n0pos (0<n0),
n0lt (n0 < Lng Y - 1), the six standard per-column host facts hostR/hostP/
hostJ1/hostT1/hostN0/hostMk (verbatim from the ALREADY-PROVEN, green
m_8_5_Mark_netfold_condV -- no new content), colRT + colMarked0 (per-column
RT_PS/Marked membership of the RUNNING prefix at n0 -- the SAME hypotheses
m_8_5_anchor_fold already carries), colcase (the R2a/trunk-stuck disjunction
of m_8_5_anchor_fold_mixed -- unchanged, still the genuine open regime
content), and prene/Cdef (the outer wrap's own shape, unrelated to the fold).

Three new lemmas assemble this, closing the two per-column obligations Round
8 flagged as "uninvestigated":

  m_8_5_dfree_transC1_std / m_8_5_isPTB_str_transC2_std (pt2, FOR FREE, no
  new named hypothesis beyond the pre-existing RT_PS/PT_PS/transJ1>0/
  transT1<>0 quartet): transC2_def's outer shape is ALWAYS D_v(...) in every
  branch (a single principal), so isPTB_str(flatBT(transC2 M)) reduces to
  dfree-ness of that shape, which the ALREADY-PROVEN, frozen dfree_transC2
  (layerB/pss_wip.thy:3583) supplies from dfree_BT(transC1 M) -- itself
  obtained via a `transC1 M = Trm ps` case split, reusing the EXACT SAME
  Trans_Mark_invariant_aux + Marked_Pred_Adm machinery the frozen
  transC1_single_principal (layerB/pss_wip.thy:2861) already assembles for
  its own, different conclusion (Lng(PB(transC1 M))=1 -- the single-principal
  SHAPE, not the dfree SIDE of the same MarkedB witness). Genuinely free: no
  regime hypothesis beyond what m_8_5_Mark_netfold_condV already required.

  m_8_5_Mark_nonzero_fold (nz, reduces to a per-column Marked-membership
  hypothesis the apparatus already needs elsewhere): fold op [0..<m] acc0 <>
  Trm[] rewrites, via m_8_5_fold_of_colstep_partial, to Mark(Y@take m B) n0
  <> Trm[], which the ALREADY-PROVEN m_8_5_Mark_nonzero supplies from
  colMarked0 ((Y@take m B,n0) in Marked -- the SAME hypothesis name
  m_8_5_anchor_fold already carries, just not re-derivable from
  m_8_5_anchor_fold_mixed's OWN colcase since colcase's trunk-stuck disjunct
  does NOT itself supply (N,n0) in Marked -- tried to derive it from colcase
  alone and failed the build, so m_8_5_Mark_fold_C_commute carries
  colMarked0 as an explicit, separate hypothesis instead, same status as the
  pre-existing m_8_5_anchor_fold's own colMarked0) + n0pos + n0lt (a SINGLE
  base interiority bound propagating forward since Lng(Y@take m B) only
  grows).

  m_8_5_Mark_netfold_condV_partial (the rewrite BRIDGE Round 8 identified as
  missing): the PARTIAL-fold form of m_8_5_Mark_netfold_condV, literally the
  same internal `step` derivation with m_8_5_fold_of_colstep swapped for
  m_8_5_fold_of_colstep_partial in the final line -- gives fold op [0..<k]
  acc0 = Mark(Y@take k B) n0 for EVERY k<=Lng B, not just k=Lng B. This is
  what lets m_8_5_Mark_fold_C_commute's `anchor`/`nz` proofs rewrite the
  ABSTRACT fold accumulator back to the CONCRETE Mark(Y@take m B) n0 that
  m_8_5_anchor_fold_mixed / m_8_5_Mark_nonzero_fold are stated over.

  GOTCHAS hit assembling this (recorded for the next round): (1)
  m_8_5_fold_C_commute has a `defines "op \<equiv> ..."` clause, which Isabelle
  INLINES throughout the lemma's statement -- citing it via `[OF op_def
  anchor nz pt2 prene Cdef]` fails with "OF: no unifiers" (arity mismatch:
  defines does NOT produce a separate suppliable premise, unlike `assumes`).
  Fix: drop op_def from the OF list, and `unfolding op_def` + `[unfolded
  op_def]` on the anchor/nz facts BEFORE the `rule` call, since a locally
  `define`d abbreviation is a rigid opaque constant that `rule`/OF
  unification will NOT see through automatically -- only an explicit
  `unfolding`/`[unfolded ...]` exposes the underlying lambda for
  unification. (2) `take_Suc_conv_app_nth`-style prefix-splitting
  (`Y@take(Suc m) B = (Y@take m B)@[B!m]`) is NOT free under bare `simp` in
  a `thus ... using X mw by simp` one-liner when X is stated over the
  `take(Suc m)` form and the goal is stated over the `@[B!m]` form -- needs
  an explicit named `split` fact (exactly as the ALREADY-GREEN
  m_8_5_anchor_fold/_mixed proofs already do) rather than relying on bare
  `simp` to bridge the two forms. (3) two of the four new lemmas needed to
  be positioned AFTER m_8_5_Mark_nonzero (defined far later in the file,
  ~line 8051) rather than immediately before m_8_5_fold_C_commute where they
  were first drafted -- a forward-reference build error (`Undefined fact`),
  not merely the softer `@{thm [source]}`-in-text gotcha CLAUDE.md already
  documents; relocated m_8_5_Mark_nonzero_fold + m_8_5_Mark_fold_C_commute
  to directly after m_8_5_Mark_nonzero's own qed.

ROUTE 2 OPEN 1 -- one candidate derivation REFUTED empirically, witness
itself RE-CONFIRMED robust. Investigated whether the trunk-stuck witness
`entry N 0 (Pcut N) < fst col` could be derived from a simple THREE-fact
combination, all computed directly from the keystone's OUTER host Mq=M[q]
(NOT from the intermediate running host N=Y@take m B): (a) Pcut(N) stays
CONSTANT = Pcut(Mq) throughout a trunk-stuck run of columns within a single
q's deepen block; (b) e_star := entry(Mq,0,Pcut(Mq)) <= e_j0 :=
entry(Mq,0,j0) (j0 = parent Mq 1 (Lng Mq-1), i.e. Pcut(Mq) sits INSIDE the
trunk, at or before j0); (c) d0 := entry(Mq,0,j1)-entry(Mq,0,j0) > 0 (row-0
strictly grows each period). IF all three held, e_star + q*d0 < fst(col)
would follow almost immediately (q>=1, d0>0), giving a REAL derivation.

python/_r9_witness_structure.py (296 genuine trunk-stuck columns, the SAME
keystone regime harness as _r6_pcutwitness_search.py, q in {1,2,3,4}):
witness itself 296/296 (RECONFIRMS Round 6-8's finding on an independent
fresh random sample -- still empirically bulletproof); (b) e_star<=e_j0
296/296 and (c) d0>0 296/296 BOTH hold; but (a) Pcut(N)==Pcut(Mq) FAILS
296/296 (!) -- Pcut(N) is NOT frozen at Pcut(Mq) across a trunk-stuck run:
concrete example M=(0,0)(1,0)(1,1)(1,0), q=2: Pcut(Mq)=3 but by m=1 (after
ONE column has been appended), Pcut(N) has already jumped to 6. ROOT CAUSE
(diagnosed, not just observed): the very FIRST column appended after Mq
(m=0->1) is apparently a "branch reset" column (fst=0), which
m_8_5_Pcut_freezes's own witness explicitly EXCLUDES (its hypothesis
`entry N 0 (Pcut N) < fst col` needs fst col > entry(...) >= 0, so a fst=0
reset column never satisfies it) -- a reset column starts a genuinely NEW
P-component, so Pcut jumps forward to point at it. So Pcut(N) is a
DYNAMIC quantity through the deepen block (piecewise-constant, resetting at
each internal branch-reset column), not a single value derivable from Mq's
OWN j0/d0 alone -- REFUTES this specific "frozen Pcut + linear growth"
derivation route. Since fcol = entry(M,0,j0(M)+m) + q*d0(M) is built from
the ORIGINAL SEED M's OWN j0/d0 (m_8_5_deepen_block_explicit), NOT Mq's --
these are generally DIFFERENT numbers from what this round's (b)/(c) checks
computed at Mq -- so even the (b)/(c) empirical successes may not be the
load-bearing facts; they were coincidental to the small-example regime
sampled. Do NOT re-attempt "Pcut(N) frozen across the whole run" as a
sub-route without first re-deriving fcol's periodicity in terms of the
SAME base (M, not Mq) the deepen-block formula actually uses.

The genuine derivation of OPEN 1 remains open. What this round adds: the
witness's continued 296/296 robustness on a fresh sample; and a concrete,
diagnosed (not just "it failed") reason why naive constant-Pcut arguments
cannot work -- any future attempt needs to track Pcut's PIECEWISE
structure through internal branch-resets within a single q's deepen block,
which likely requires characterizing which within-block columns are
resets (fst=0) directly from the SAME M/j0/d0 the deepen-block formula
uses, not from Mq's own (unrelated) Pcut/entry values.

Re-run instructions for Round 9: python/_r9_witness_structure.py (witness
296/296, Pcut-constant 0/296 REFUTED with diagnosed root cause).

ROUTE 1 ITEM (3) -- candidate (i) (the self-referential F) INVESTIGATED
empirically for the first time (Round 8 flagged it as "UNTESTED"); its CORE
sub-fact is STRONGLY SUPPORTED, not refuted -- but item (3) as a whole is
NOT closed this round (no Isabelle written for it; see what remains below).

python/_r9_item3_selfref.py tests two sub-facts of candidate (i)'s hoped-for
self-referential F (F built purely from a pairseq X's OWN trailing block,
not referencing the original seed M or the outer index q):

  (a) SHIFT LAW: B(q) = Shift_row0(d0, B(q-1)) for q>=1, i.e. two
  CONSECUTIVE deepen-blocks (m_8_5_deepen_block_explicit's B(q)/B(q-1)) are
  the SAME list with row-0 (only) shifted by the CONSTANT d0 (row-1
  unchanged) -- follows almost by inspection of the explicit formula (both
  B(q)[i] and B(q-1)[i] read entry M 0 (j0+i) plus q*d0 vs (q-1)*d0) but had
  never been stated/tested as its own fact. CONFIRMED 1575/1575, ZERO
  counterexamples (across q in {1..5}, the same reduced-seed harness as
  Round 9's other scripts).

  (b) SELF-RECOVERABLE d0: d0 itself (needed to apply the shift law) can be
  READ OFF X=M[q] alone (q>=2, no dependency on the original M or on
  externally-computed j0/j1) by comparing X's OWN last two period-blocks:
  d0 = entry X 0 (Lng X - 1) - entry X 0 (Lng X - 1 - w) (w = the period
  length -- STILL computed from the original M in this test, see the gap
  below). CONFIRMED 1221/1221, ZERO counterexamples.

  Both together mean: GIVEN the period boundary w, the row-0-shift-by-d0
  content of "the next block equals the previous block shifted" is a
  genuine, verified, purely-structural (regime-free beyond the existing
  hasParent/condV setup) fact -- not a coincidence of small examples. This
  is a POSITIVE result for candidate (i): it directly supplies the "shifted
  copy of X's own last block" ingredient the Round 8 write-up's candidate
  (i) sketch asked for.

  WHAT STILL BLOCKS assembling candidate (i) into a literal q-independent F
  (not attempted this round -- this is exactly where a future round should
  pick up, do NOT re-verify (a)/(b) again, they are now settled): (1) the
  period width w itself needs to be recoverable from X ALONE (not from the
  original M's j0/j1) for F to be truly self-referential -- likely via
  w = Pcut X (m_8_5_Pcut_append_block, ALREADY PROVEN, establishes
  Pcut(drop j0 (M[Suc q])) = w under a nocut hypothesis; this round did NOT
  test whether Pcut X itself -- with NO drop/j0 offset, applied directly to
  X=M[q] -- recovers w, which is the literal self-referential form
  candidate (i) needs); (2) even granting (a)+(b)+a self-referential w, one
  still needs to prove F(M[q]) = M[Suc q] as a literal equation (this round
  only checked the BLOCK matches, not that appending it via F's own
  definition reconstructs the exact next iterate -- should follow directly
  from (a)/(b)/(1) plus m_8_5_deepen_block_explicit, but was not written
  out); (3) the DEEPER content -- F/C commutation (F(Cw)=C(Fw)) and
  Inv-persistence, which m_8_5_keystone_allq's schema actually needs to
  conclude the keystone at every q -- is a SEPARATE, likely harder question
  that this round's block-shift-law finding does NOT address (recall
  b3_markstep_skeleton's own text already flags an "assembly" step as
  "otasm-empirical 47/47, NOT mechanically reducible to the geometry" --
  the self-referential block LAW found this round may still not be enough
  to discharge that).

  Candidate (ii) (bypass keystone_allq, prove the markstep directly at
  every q via m_8_5_markstep_of_Trans_keystone's own per-q hypothesis) was
  NOT attempted this round either; Round 8's own tradeoff analysis (sidesteps
  the q-independent-F puzzle but reintroduces the "prove at every q
  separately" cost) still stands unchanged.

Re-run instructions for Round 9 (cont'd): python/_r9_item3_selfref.py
(shift law 1575/1575, self-d0 1221/1221, both zero counterexamples).

=====================================================================
ROUND 10 (2026-07-01, this round; empirical/architectural only -- NO new
Isabelle lemmas, NO commit to layerC/pss_scratch.thy this round). Item (3)
sub-point (1) is now DEFINITIVELY REFUTED. A fresh architectural check shows
Round 9's m_8_5_Mark_fold_C_commute does NOT, by itself, resolve the
"assembly" keystone (confirms the project's own existing "irreducible"
assessment via an independent path -- do not re-attempt this exact
combination). Route 2 gained ONE new, clean, 100%-confirmed empirical
invariant (NOT the refuted frozen-Pcut), still insufficient alone to close
the derivation.
=====================================================================

ROUTE 1 ITEM (3) SUB-POINT (1) -- REFUTED. Round 9 flagged as the next
concrete step: "test whether Pcut X itself -- with NO drop/j0 offset,
applied directly to X=M[q] -- recovers w" (the period width), which would
give a literal self-referential w for candidate (i)'s F. Tested directly
(python/_r10_pcut_selfw2.py, growth-VERIFIED harness -- i.e. only counting
(M,q) pairs where oper(M,q)->oper(M,q+1) actually appends a length-w block
matching m_8_5_deepen_block_explicit's own growth picture; an earlier,
sloppier version without this growth check, python/_r10_pcut_selfw.py --
since deleted, was misleading itself with degenerate non-growing (M,q)
pairs and is not a reliable data point):

  Lng(X) - Pcut(X) == w:  0/876  -- REFUTED, decisively, not merely "often
  fails": ZERO successes on the growth-verified sample (q in 2..5, reduced
  seeds length<=6, values 0..2/u in 0..3). Concrete smallest counterexample:
  M=(0,0)(0,0)(1,1), q=2: j0=1, w=1, but Pcut(X)=1 while Lng(X)=3, so
  Lng(X)-Pcut(X)=2<>1=w. Do NOT re-attempt "Pcut(X) applied directly (no
  drop) recovers the period width" in any form -- it is false, not merely
  underdetermined.

  Pcut(X)==j0 (the ORIGINAL M's own row-1 parent offset): 584/876 (~67%),
  a soft correlation, NOT a law -- also not usable as-is.

  This closes off the ONE concrete next step Round 9 identified for item
  (3); the "self-referential w via Pcut" idea is dead. Candidate (i)'s
  remaining path (if revisited) needs a genuinely different source for w
  (NOT Pcut(X) directly) -- e.g. w might still be recoverable via Pcut of a
  SUFFIX of X (as m_8_5_Pcut_append already does with the drop j0 offset),
  but that needs j0 externally, which is exactly what "self-referential"
  was trying to avoid; no new idea for this sub-point was found this round.

ROUTE 1 ITEM (3), THE DEEPER "ASSEMBLY" CONTENT -- an architectural dead
end IDENTIFIED (not a new refutation of previously-untried machinery, but a
NEGATIVE finding worth recording so a future round does not re-derive it):
does Round 9's freshly-proven m_8_5_Mark_fold_C_commute (fold op [0..<Lng B]
(C (Mark Y n0)) = C (Mark (Y@B) n0), for GENERIC Y/B/n0) already supply the
"assembly" keystone content b3_markstep_skeleton_rnav names as irreducible
(fold op [0..<w] (rnav acc0) = C (rnav acc0), i.e. "the period column ops
applied to the ALREADY-ONE-LEVEL-STRIPPED value U_q = rnav(acc0) rebuild
C(U_q)")? Traced through CAREFULLY (no Isabelle written, pure proof-term
tracing): NO -- these are genuinely different claims, not just differently
phrased. m_8_5_Mark_fold_C_commute (via ra_Mark0_eq_Trans, layerB/pss_wip.thy:8257,
ALREADY PROVEN/frozen: (M,0)\<in>Marked --> M\<in>RT_PS --> Mark M 0 = Trans M)
shows C commutes with the fold when C is applied to the SAME FULL seed
(Mark Y n0) the fold is run FROM -- i.e. "wrap-before vs wrap-after the
WHOLE per-column recursion, same starting value". "assembly" instead asks
about running the SAME per-column op starting from a DIFFERENT, already
rnav-STRIPPED value (rnav(acc0), one BT-tree level down from acc0 itself)
and getting C of that stripped value back -- a claim about self-similarity
ACROSS a depth-strip, not about C surviving a fold from a fixed start.
Nothing in the Mark_fold_C_commute chain (or in dfree_transC1_std/
isPTB_str_transC2_std, Round 9's two "for free" pt2/nz facts) touches
bpHeadT/rnav's INTERACTION with C's own Cdef shape (C z = t2 +\<^sub>B Dpt(vm1) z,
a PREPEND, not a same-level op) -- confirms b3_markstep_skeleton_rnav's own
framing ("assembly ... irreducible ... otasm-empirical 47/47, NOT
mechanically reducible to the geometry") from a genuinely independent
direction. Also independently confirmed the file's OWN classification of
the OLDER spineLeaf/endpoint route (m_8_5_C_body's "endpoint" hypothesis,
~pss_scratch.thy:3967) as superseded by the newer rnav-based
b3_markstep_skeleton_rnav (matches refuted routes #3/#13 -- do not revisit
spineLeaf as the bridge). NET: no route found this round that reduces
"assembly" further; it remains the single genuinely open mathematical
content, exactly as the last several rounds concluded.

ROUTE 2 -- ONE new, clean, UNIVERSALLY-confirmed (not merely "often")
empirical invariant found, replacing the refuted "Pcut frozen" idea with an
INEQUALITY that survives Pcut's resets, but NOT yet sufficient to close the
witness derivation (python/_r10_witness_bound.py, python/_r10_witness_bound2.py,
same trunk-stuck keystone-regime harness as Round 9's _r9_witness_structure.py,
296 genuine trunk-stuck columns, q in {1,2,3,4}):

  epcut <= ANCHOR, where epcut := entry(Nprev,0,Pcut(Nprev)) (Nprev = the
  running prefix Mq@take m B BEFORE column m is appended) and ANCHOR :=
  entry(Mq,0,Lng(Mq)-1) (a SINGLE value computed ONCE from Mq -- the q-th
  iterate BEFORE this deepen block even starts -- NOT tracked/recomputed
  per column m): CONFIRMED 296/296, ZERO exceptions. This is a genuine,
  new, ROBUST fact -- unlike "Pcut(N) frozen" (Round 9, refuted 0/296),
  this one survives Pcut jumping forward at internal branch-reset columns,
  because it is only an upper BOUND, not an equality. An even SHARPER
  version also holds universally: epcut <= ANCHOR_PREV, where ANCHOR_PREV
  := entry(M[q-1],0,Lng(M[q-1])-1) (one FEWER period than Mq) -- CONFIRMED
  296/296 as well (python/_r10_witness_bound2.py), i.e. epcut is bounded by
  a value from q-1 periods back, not merely q periods back.

  What is STILL missing to derive the actual witness entry(Nprev,0,Pcut
  (Nprev)) < fst(col) from this: the OTHER half, ANCHOR < fcol (or
  ANCHOR_PREV < fcol), does NOT hold universally -- only 30/296 (ANCHOR) or
  75/296 (ANCHOR_PREV) of rows. Root cause (diagnosed): ANCHOR is, BY THE
  deepen-block periodicity formula, EXACTLY equal to fcol at column m=0 of
  the CURRENT period (both equal entry M 0 j0 + q*d0), so "ANCHOR<fcol" is
  a TIE (not a strict gap) whenever the run reaches back to (or is at) that
  boundary column, and can even go the other way when d0=0 for the specific
  (M,q) sampled (a genuinely degenerate sub-case, e.g. M=(0,0)(1,0)(1,1)(1,0)
  has entry M 1 (Lng M-1)=0, i.e. e1pos fails for M itself, though Mq's OWN
  derived j0/d0 can still be legitimately 0 in edge cases) -- in EVERY one
  of these failing rows, though, epcut itself was STRICTLY less than ANCHOR
  (epcut=0 while ANCHOR=fcol=1), which is exactly why the overall witness
  (epcut<fcol) still held 296/296 despite the ANCHOR<fcol sub-step failing
  -- i.e. the gap looks closeable by a two-case split (epcut<ANCHOR, in
  which case ANCHOR<=fcol suffices; OR epcut=ANCHOR, in which case a
  separate argument for STRICT ANCHOR<fcol is needed only in that
  sub-case) but this was NOT worked out or tested this round -- left for a
  future round. Do NOT re-attempt "ANCHOR<fcol universally" or "ANCHOR_PREV
  <fcol universally" as stated -- both refuted (30/296, 75/296); the
  epcut<=ANCHOR(_PREV) HALF is the reusable, confirmed part.

  Re-run instructions for Round 10: python/_r10_pcut_selfw2.py (item-3
  sub-point-1, 0/876, decisively refuted); python/_r10_witness_bound.py
  (epcut<=ANCHOR 296/296, ANCHOR<fcol 30/296); python/_r10_witness_bound2.py
  (epcut<=ANCHOR_PREV 296/296, ANCHOR_PREV<fcol 75/296).

NET this round: no new Isabelle lemmas, no commit to pss_scratch.thy (both
routes were investigated but neither closed; per the round's own workflow
guidance, a shaky/uncertain Isabelle attempt was deliberately NOT forced
under time pressure). Two decisive negative results (item-3 sub-point-1
REFUTED 0/876; the Mark_fold_C_commute-closes-assembly hope REFUTED by
proof-term tracing) and one new POSITIVE but incomplete empirical lead
(epcut<=ANCHOR(_PREV), 296/296) are recorded for the next round. The
"assembly" content (b3_markstep_skeleton_rnav) remains the single
irreducible mathematical open of Route 1; Route 2's derivation is closer
(one confirmed half of a two-case argument) but not closed.

=====================================================================
ROUND 11 (2026-07-01, this round; layerC/pss_scratch.thy, commits mirrored
main/wt2). Route 2's ORIGINAL ask -- deriving the trunk-stuck witness
`entry N 0 (Pcut N) < fst col` from the keystone's own regime, open since
Round 6 -- is now FULLY PROVEN via a route that TURNED OUT MUCH SIMPLER than
Round 10's own ANCHOR-based lead (which is superseded, see below). Route 1
item (3) was investigated further (Isabelle exploration of what
m_8_5_markstep_of_Trans_keystone already gives) but NOT closed; see its own
subsection below.
=====================================================================

ROUTE 2 -- CLOSED. Round 10 flagged "the germ of a two-case argument" around
an ANCHOR quantity (epcut<=ANCHOR universal, ANCHOR<fcol only 30/296, with
the failures allegedly concentrated "at the m=0 period-boundary column,
where it's an exact tie"). Re-testing that EXACT split first
(python/_r11_twocase.py): REFUTED as stated -- m==0 NEVER appears as a
trunk-stuck row at all (0/296; B[0], the deepen-block's own first column, is
ALWAYS itself the fcol==0 reset column that the harness's own "trivial
fresh-reset" filter excludes), so the "m==0 boundary" framing was not the
real mechanism. A second attempt splitting on epcut<ANCHOR (strict) vs
epcut==ANCHOR (python/_r11_twocase_v2.py) also did not close it (epcut==0
cases never had epcut==ANCHOR wither -- case B was EMPTY, 0/296 -- and the
"epcut<ANCHOR ==> ANCHOR<=fcol" half itself FAILED 30/296, with genuine
ANCHOR>fcol reversals, not just ties, e.g. ANCHOR=2,fcol=1).

Manual inspection of the failing rows from BOTH prior attempts showed
epcut==0 in EVERY SINGLE ONE. Testing this directly (python/_r11_twocase_v3.py):
splitting on ANCHOR<fcol (30/296, where epcut<=ANCHOR<fcol already closes it)
vs ANCHOR>=fcol (266/296) with the conjecture "epcut==0 whenever ANCHOR>=fcol"
-- CONFIRMED 266/266, closing the witness for ALL 296/296 rows. But a FOLLOW-UP
check (does epcut==0 hold literally EVERYWHERE, not just in the ANCHOR>=fcol
sub-case?) revealed epcut==0 in ALL 296/296 rows, including the 30
"ANCHOR<fcol" ones -- i.e. ANCHOR was NEVER the load-bearing quantity; epcut
is simply, unconditionally, always 0 in this regime. This is a dramatically
simpler invariant than anything Rounds 6-10 pursued, and it explains WHY:
epcut = entry(Nprev,0,Pcut(Nprev)) is the row-0 value at the START of
Nprev's OWN last P-component (Pcut's definition literally cuts M into
P(prefix)@[drop(Pcut M) M]), and Round 9 already independently observed
"the very first column appended after Mq is a branch-reset column (fst=0)"
and that Pcut(N) JUMPS FORWARD at such resets -- the missing piece is that
it jumps EXACTLY to the position of that reset column and then FREEZES
there (via the ALREADY-PROVEN Round 8 m_8_5_Pcut_freezes) for the rest of
the SAME period's run, so entry(Nprev,0,Pcut(Nprev)) = fst(that reset
column) = 0 identically throughout.

python/_r11_pcut_eq_lngmq.py confirms `Pcut(Nprev) == Lng(Mq)` (Mq = the
q-th iterate BEFORE this deepen block; Lng(Mq) = the position of B[0], the
block's own first column) EXACTLY for every trunk-stuck row, across THREE
independent samples (296/296, 36/36 on a fresh larger-value/larger-q sample,
304/304 on a fresh larger-length sample -- 636/636 total, zero exceptions).
python/_r11_reset_pcut_general.py isolates the UNDERLYING general fact with
NO deepen-block/regime content at all: for ANY N (Lng N>0) and ANY v, if
multiT(N@[(0,v)]) then Pcut(N@[(0,v)]) == Lng N -- confirmed on an
UNRESTRICTED sweep, 1,062,880/1,062,880 (zero exceptions, no regime filter
whatsoever). python/_r11_pcut_jump_base.py additionally confirms the
converse direction empirically (fst(B[0])==0 correlates EXACTLY with
Pcut(Mq@[B[0]])==Lng(Mq); the 236 rows where B[0] is NOT a reset column never
have this Pcut value, consistent with Pcut freezing at Pcut(Mq) instead via
the SAME already-proven Pcut_freezes mechanism when the first appended
column is itself non-reset -- explaining why m==0 never shows up as
"newly stuck", since a non-reset B[0] keeps the SAME non-stuck status Mq
itself already had).

FORMALIZED (layerC/pss_scratch.thy, green PSS_C, sorry/oops=0, self-audited
for circular citation -- none):

  m_8_5_reset_Pcut_jump: `0 < Lng N ==> multiT(N@[(0,v)]) ==> Pcut(N@[(0,v)])
  = Lng N`. Fully general, no RT_PS/regime hypothesis. Proof: Lng N is
  trivially a valid le0-cut (le0 is reflexive, m_8_5_Pcut_of_le0_cut's `cut`
  half); no SMALLER j can be a cut, since leR X 0 j (Lng N) would force (by
  the ALREADY-PROVEN, frozen m_5_1_ancestor_basic_1 -- value strictly
  increases along any nontrivial ancestor chain) entry X 0 j < entry X 0
  (Lng N) = 0, impossible for a nat. This is the ENTIRE new mathematical
  content of Route 2's closure -- everything else below is composition with
  Round 8's already-proven m_8_5_Pcut_freezes.

  m_8_5_Pcut_reset_freeze: given a deepen-block-shaped run (per-column RT_PS
  + multiT hypotheses `hostR`/`hostM`, matching the style of the file's
  other per-column fold lemmas), a reset first column (`col0: fst(B!0)=0`)
  and non-reset later columns (`colpos: 0<m<Lng B ==> 0<fst(B!m)`), Pcut
  (Mq@take m B) = Lng Mq for EVERY 0<m<=Lng B. Proof: induction on m; base
  case m=1 is m_8_5_reset_Pcut_jump; step case m=Suc k (k>=1) applies the
  ALREADY-PROVEN m_8_5_Pcut_freezes with the "strict" witness `entry (Mq@take
  k B) 0 (Pcut (Mq@take k B)) < fst(B!k)` discharged from the IH (Pcut=Lng Mq)
  + `entry (Mq@take k B) 0 (Lng Mq) = fst(B!0) = 0` (nth_append, k>=1) + colk
  (0<fst(B!k)).

  m_8_5_Pcut_reset_witness: the witness itself, `entry (Mq@take m B) 0
  (Pcut(Mq@take m B)) < fst(B!m)` for 0<m<Lng B, directly from
  m_8_5_Pcut_reset_freeze + col0 -- discharges
  m_8_5_anchor_col_trunkstuck_regime2's/m_8_5_anchor_fold_mixed's `strict`
  hypothesis for this regime with NO reference to ANCHOR, periodicity
  formulas, or d0 at all.

SUPERSEDED (do not re-attempt): Round 10's ANCHOR-based lead (epcut<=ANCHOR,
ANCHOR<fcol, the "period-boundary column" framing, ANCHOR_PREV) is now
understood to have been chasing a WEAKER, coincidentally-often-true corollary
of the real (much stronger, unconditional) epcut==0 fact -- not wrong, just
unnecessary. A future round wiring m_8_5_Pcut_reset_witness into
m_8_5_anchor_fold_mixed's colcase disjunct (i.e. showing the `colcase`
per-column hypothesis itself follows from `col0`/`colpos` across a REAL
oper-generated deepen block, using m_8_5_deepen_block_explicit/_row0 to
establish that B[0] is indeed always fst=0 in the genuine oper recursion)
would complete Route 1 item (1)/(2)'s remaining "R2a's leR gap for
non-trunk-stuck columns" caveat for this specific sub-case, though that
wiring was NOT attempted this round (this round's mandate was the witness
derivation itself, now done).

Re-run instructions for Round 11 (Route 2): python/_r11_pcut_eq_lngmq.py
(Pcut(Nprev)==Lng(Mq) and epcut==0, 636/636 combined); python/_r11_reset_pcut_general.py
(the general fact, 1,062,880/1,062,880); python/_r11_pcut_jump_base.py (the
reset<->jump correlation, 106/106 and 236/236 both directions).

ROUTE 1 ITEM (3) -- explored further, NOT closed. See the dedicated
sub-section after this one for what was tried and why it remains open.

ROUTE 1 ITEM (3) DETAIL -- re-read Round 9's own "WHAT STILL BLOCKS" list
(candidate (i) sub-points (1)/(2)/(3), candidate (ii)) to find an unexplored
angle. Two findings:

(a) Candidates (i)-sub-point-(2) ("F(M[q])=M[Suc q] as a literal equation")
and (ii) ("bypass keystone_allq, prove markstep directly at every q via
m_8_5_markstep_of_Trans_keystone's own per-q hypothesis") turn out NOT to be
live options, on inspection: (2) is moot because the PAIRSEQ-level recursion
M[Suc q]=F(M[q]) is ALREADY fully explicit and q-independent
(m_8_5_deepen_block_explicit, ALREADY PROVEN) -- the q-independent-F
"puzzle" Round 8 flagged was never really about the pairseq level at all,
it was about the DOWNSTREAM BT/Trans-level recursion (z(Suc q)=F_BT(z q)
for the ABSTRACT keystone_allq schema), which is a separate, harder claim.
And (ii) turns out to be ALREADY THE FILE'S CURRENT STATE: the
"EXPOSED-IDENTITY FRAME" text (~pss_scratch.thy line 8046,
m_8_5_markstep_of_Trans_keystone) already takes exactly this per-q
"keystone" hypothesis directly (bypassing keystone_allq/telescope
entirely) -- this predates the round 8-10 campaign on item (3) and was
apparently already the adopted approach. Both routes, traced through, land
on the EXACT SAME open fact as b3_markstep_skeleton_rnav's "assembly"
(fold op [0..<w] (rnav acc0) = C (rnav acc0)) -- there is no THIRD distinct
open fact hiding in Round 9's candidate list; "assembly" is the one thing
both formulations reduce to.

(b) A genuinely NEW angle tried this round: does the ALREADY-PROVEN,
frozen (IncrFirst,Red)-invariance family -- Trans(IncrFirst M)=Trans M /
Mark(IncrFirst M) m=Mark M m / Trans_funpow_IncrFirst (layerB/pss_wip.thy
~line 686-11009; "IncrFirst" = add a CONSTANT to every row-0 entry,
map (\<lambda>p.(Suc(fst p),snd p))) -- combined with Round 9's CONFIRMED
block-shift law (B(q) = shift_row0(d0, B(q-1))) let "assembly" reduce to
something already known?  Traced through by hand (no Isabelle written --
this was refuted analytically before it was worth testing empirically):
NO, for a structural reason, not a coincidence. Trans_funpow_IncrFirst says
Trans is invariant under shifting an ENTIRE pairseq's row-0 by a constant
(same LENGTH, same shape, just relabelled values) -- but slice_{q+1} =
slice_q @ B(q) is LONGER than slice_q (genuine append/growth, not a
same-length relabelling), so "slice_{q+1} = IncrFirst^^d0 (slice_q)" is a
DIMENSION MISMATCH / false claim, not something IncrFirst-invariance could
apply to even in principle. Only the NEWLY APPENDED PART (B(q) vs B(q-1))
satisfies a clean shift law, and IncrFirst-invariance is a fact about
WHOLE-structure relabelling, not about how Trans treats one growing
structure against a shorter one -- so this "translation invariance"
shortcut, however tempting given the CONFIRMED shift law, does not apply to
the actual assembly obligation. This CONFIRMS (via a different, structural/
dimensional argument this time, rather than proof-term tracing) Round 10's
conclusion that "assembly" is not reducible via known machinery; the
genuine content is that the Mark/BT TOWER grows a real new level each
period (not a flat relabelling), which is exactly why it needed the
otasm-empirical/rnav/depth-ladder machinery in the first place.

NET for item (3) this round: no new reduction found; the two remaining
"candidate resolutions" from Round 9's list turn out to already be
exhausted / equivalent to the existing state, and a genuinely new
(IncrFirst-based) angle was tried and structurally refuted. "assembly"
(b3_markstep_skeleton_rnav's hypothesis, equivalently
m_8_5_markstep_of_Trans_keystone's `keystone` hypothesis) remains the
single irreducible mathematical open of Route 1/item (3), now for the
6th consecutive round reaching this same conclusion via independent
approaches (Rounds 6b/7/8/9/10/11). A future round should treat this as
requiring genuinely new mathematical insight (e.g. a direct structural
argument about how the P-decomposition/Mark recursion behaves ACROSS a
whole appended period, not a translation/composition trick), not another
attempt to route around it via already-proven machinery -- every
composition of currently-available lemmas has now been checked and found
insufficient by at least one round.
"""
