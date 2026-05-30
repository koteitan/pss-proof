# §6.8 命題1 `slice_Br_descending` — 設計と補題分解

The §6.8 proposition `p_6_8_standard_slice_Br_descending` (pss_paper):

```
assumes "M ∈ ST_PS" "j0' < j1'" "j1' ≤ Lng M - 1" "leR M 0 j0' j1'"
shows   "monoT (seg M j0' j1') ∧ descending (Br (seg M j0' j1'))"
```

This is the hardest proposition in the development (article proof: content.md
1424–1615, a ~190-line `k_0` induction with `N_{1,j1}=0/>0` split, quotient/
remainder, `FirstNodes`/`TrMax`/`Joints`/`IncrFirst`, and `Br(M'[n])`
decomposition). Empirically true: `python/sk_68_prop1_audit.py` (0 violations).

## Reduction (what is FREE vs HARD)

Write `M' = seg M j0' j1'`. The goal splits cleanly:

1. **`monoT M'`** — FREE. `m_6_2_mono_ancestor_slice[OF (M∈T_PS) (j0'<j1') (leR M 0 j0' j1')]`
   gives `monoT (seg M j0' j1')` directly. (`M ∈ ST_PS ⊆ T_PS` via `ST_PS_T_PS`.)

2. **`descending (Br M')`** — `Br M' = (if TrMax M' = Lng M' - 1 then [] else
   P (seg M' (TrMax M' + 1) (Lng M' - 1)))`.
   - If `TrMax M' = Lng M' - 1`: `Br M' = []`, `descending [] ` trivial.
   - Else `Br M' = P Y`, `Y = seg M' (TrMax M' + 1) (Lng M' - 1)`. Since the
     guard fails, `Y` is non-empty, so `Y ∈ T_PS` (recall `T_PS = {M. M ≠ []}`).
     `descending (P Y)` unfolds to two parts:
     - **row-0 (weakly decreasing left ends)** — FREE. `m_6_4_P_leftend_mono[OF
       (Y∈T_PS) J0≤J1 J1≤Lng(P Y)-1]`.
     - **row-1 tie-break** (equal row-0 ⟹ row-1 weakly decreasing) — **HARD.**
       This is the genuine content of the §6.8 induction.

So the whole proposition reduces to the **row-1 tie-break of the branch
components `Br M'`**.

## Why there is no ST_PS shortcut (empirical, `python` ad-hoc)

- (A) `descending (P X)` holds for **all** `X ∈ ST_PS` (0 violations) — derivable
  from `m_6_8_standard_P_descending` (prop2, ✅) + `m_6_4_P_leftend_mono`. This is
  the article's note "(1) P(M) は降順である" for `M ∈ ST_PS`. Worth recording as a
  reusable lemma `descending_P_of_ST`.
- (B) the branch segment `Y = seg M' (TrMax M'+1)(Lng M'-1)` is **never** in
  ST_PS (106/106 in the bounded enumeration) — a branch starts at `TrMax+1`, so
  its row-1 structure is not that of a `diagSeq`-oper image. **⟹ cannot get the
  tie-break for `Br M'` from (A): `P Y` with `Y ∉ ST_PS`.**
- (C) even the ancestor slice `M' = seg M j0' j1'` is not always in ST_PS
  (42/207, **including for mono `M`**, e.g. `M = (0,0)(1,1)(2,0)`, slice
  `(1,1)(2,0)`). So the tie-break needs the article's structural induction, not
  a membership shortcut. **This refutes content.md 1434** ("M' が標準形となること
  を…示す") — the proven (and provable) statement is "Br(M') is descending", not
  "M' is standard". Recorded as **correction A7**.

## The hard part: row-1 tie-break of `Br M'` (article k_0 induction)

The article inducts on `k_0 = min{k : M ∈ S_k T_PS}` (we will use plain `k` with
`M ∈ SkT_PS k` + `SkT_PS_mono`, as in prop2). The slice `M'` is threaded through
`M = (built by oper)`. The core is **how `Br` behaves under `oper`**: for the
mono parent `N` with `M`-structure `N[n]`, `Br(N[n])` decomposes in terms of
`Br(N')` (where `N'` is the corresponding sub-slice), plus `IncrFirst`-shifted
copies of the trunk-to-`j1` block, governed by `FirstNodes`/`TrMax`/`Joints`.

### Br-under-oper lemma inventory (TODO — to be built)

These are the new helpers the induction needs (none exist yet; no `Br`-under-
oper lemma in `pss_mechanized.thy`):

- `branch_seg_T_PS`: `Br M ≠ [] ⟹ seg M (TrMax M + 1)(Lng M - 1) ∈ T_PS`
  (immediate: non-empty when the `Br` guard fails). **easy**
- `Br_eq_P_branchseg`: `Br M ≠ [] ⟹ Br M = P (seg M (TrMax M+1)(Lng M-1))`
  (unfold `Br_def`). **easy**
- `descending_unfold` / `descending_P`: `descending (P Y)` ⟺ row-0-mono ∧
  tie-break; row-0-mono is `m_6_4_P_leftend_mono`. **easy**
- `descending_P_of_ST`: `X ∈ ST_PS ⟹ descending (P X)` (= prop2 + leftend_mono).
  **easy, reusable** — but NOT directly applicable to `Br M'` since the branch
  seg ∉ ST_PS.
- **`Br_oper_decomp`** (the crux, HARD): express `Br (N[n])` from `Br N'` +
  `IncrFirst`-blocks. Needs `TrMax`/`FirstNodes`/`Joints` behaviour under oper,
  the `(1,j1)=0` vs `>0` split, and the quotient/remainder slicing of the
  expanded block. This mirrors content.md 1450–1615.
- row-1 values of `Br` components in terms of joints / `M_{1,FirstNodes}`
  (`entry (Br M ! J) 1 0` characterization), to drive the tie-break.

## CLEAN final reduction (confirmed) — prop1 reduces to ONE lemma

The whole proposition reduces to a single lemma about **any slice** of a
standard form:

> **`slice_P_descending`**: `M ∈ ST_PS ⟹ a ≤ b ⟹ b ≤ Lng M - 1 ⟹
>   descending (P (seg M a b))`.

Given `slice_P_descending`, `m_6_8_standard_slice_Br_descending` follows:
- `monoT (seg M j0' j1')` — `m_6_2_mono_ancestor_slice` (FREE).
- `descending (Br M')`: if `Br M' = []`, trivial; else `Br M' = P Y`,
  `Y = seg M' (TrMax M'+1)(Lng M'-1)`. By `seg_of_seg` (green; `j0' ≤ j1'`,
  `Lng M'-1 ≤ j1'-j0'`), `Y = seg M (j0'+TrMax M'+1) (j0'+Lng M'-1)`, a slice of
  `M` with right end `= j1' ≤ Lng M-1`. So `slice_P_descending` gives
  `descending (P Y) = descending (Br M')`. ∎

Empirically (G1) `descending (P (seg M a b))` holds for every slice (0/353).
(The earlier `descending_Br_of_FN_tiebreak` is an alternative FirstNodes-based
reduction; `slice_P_descending` + `seg_of_seg` is the cleaner route and makes it
unnecessary.)

## DECISION (2026-05-27): faithful conditional `Br` induction (supersedes the unconditional route)

The unconditional `slice_P_descending` (`descending (P (seg N a b))` for ALL
slices) is empirically true but **diverges from the article** and forces a hard
multi-period sub-case in `d0zero` that the article avoids via its `leR`
hypothesis. Per the faithfulness policy we **re-architect to the article's
conditional statement** (= exactly `p_6_8_standard_slice_Br_descending`):

> `M ∈ ST_PS ⟹ j0' < j1' ⟹ j1' ≤ Lng M - 1 ⟹ leR M 0 j0' j1' ⟹
>  monoT (seg M j0' j1') ∧ descending (Br (seg M j0' j1'))`

proved by induction on the rank `k` (`M ∈ SkT_PS k`), transcribing content.md
1422–1615. The `monoT` part stays `m_6_2_mono_ancestor_slice`.

### PROGRESS (worktree `../pss-slice`, green; `m_6_8_slice_Br_descending_monoT`)
The whole rank-induction skeleton is GREEN except **two** `sorry`s, both inside
the `n>1` block region. Done:
- **base `k=0`**: `seg_diagSeq` → `Br_diagSeq` (new helper, `TrMax(diagSeq)=Lng-1`)
  → `descending []`.
- **`Suc k`, `multiT N`** (article 1442): `M = P(N)₀ ∈ SkT_PS k` (via
  `m_6_2_P_oper_1/2` + `P M = [M]` from `monoT M`), IH applies to `M`.
- **`Suc k`, `Lng N = 1`**: `M = N`, `Lng M = 1` contradicts `j0' < j1'`.
- **`Suc k`, `monoT N`, `j1' < Lng N - 1`** (article 1446): slice agrees with `N`
  (`oper_nth_lt`), `leR` transferred `M→N` via `adm_le0_seg`, IH on `N`.
- **`Suc k`, `monoT N`, `j1' ≥ Lng N - 1` groundwork**: the oper is generic
  (`notzeroN`/`hasparN`; degenerate ⟹ `Lng M = Lng N - 1` < `j1'`), split on
  `entry N 1 (Lng N - 1)`.

Remaining (the genuine core, multi-session):
- **`d0zero`** (`entry N 1 (Lng N-1) = 0`, i1=0, unshifted blocks): article 1460–1514.
- **`d0pos`** (`> 0`, i1=1, `δ`-shifted blocks): article 1516–1589.

Both need a **`Br`-under-oper decomposition** lemma (`Br(M') = (Br(N')_J) ⊕
blocks` via `FirstNodes(N')`), the principal missing machinery. Available:
`m_6_4_FirstNodes_TrMax_Joints` (prop 769), `FirstNodes_nth`, `Joints_nth`,
`entry_FirstNodes_eq_component(_gen)`, `TrMax_*`, `IncrFirst` equivariance
(`m_6_2_P_IncrFirst`, `TrMax_funpow_IncrFirst`).

**Key simplification (no minimal rank needed).** The article uses minimal-rank
`k₀` induction only to get «`N` is monoT» (via `M ≠ P(N)₀`). But a plain `k`
induction suffices: in the `Suc k` step `M = N[n]`, `N ∈ SkT_PS k`,
- if `N` is **multi**: `M = N[n]` monoT forces (via the `P`/fundamental-sequence
  relation: a multi `N` would make `N[n]` multi unless it collapses to the first
  component) `M = P(N)₀`, which is standard of rank `k` (`m_6_7_standard_P_components`),
  so `M ∈ SkT_PS k` and **IH applies to `M` directly**;
- if `N` is **monoT**: run the article's argument, applying IH to the ambient
  `N ∈ SkT_PS k` with the slices `[j'_0,j'_1]` / `[j'_0, j1^N]` (= `N'`).

So `IH` is always keyed on the **ambient** sequence's rank (`N`, or `M` itself in
the multi case) — never on a slice being standard.

The committed `_of_drop` reduction lemmas (which depend on the abandoned
unconditional core) become dead; remove them from `main` when the article-based
proof integrates. Helpers `take_seg`/`drop_seg`/`seg_diagSeq`/
`not_multiT_seg_diagSeq`/`oper_nth_lt` (all green) are reused.

The article case structure (content.md): WLOG `M` monoT (1432; multi `M` ⟹ slice
within one standard component); `k₀=0` ⟹ `M'` diagonal, `Br(M')=()` (1436);
`k₀>0`, `M=N[n]`, `N` monoT (1442); reductions `M'=slice of N` / `M=Pred N` /
`n=1` ⟹ IH (1446–1450); `n>1` splits on `N_{1,j1^N}` (= our `d0zero`/`d0pos`):
1460–1514 / 1516–1586, the bulk (uses `N'`, `FirstNodes`/`TrMax`/`Joints`, the
quotient/remainder block bookkeeping).

## (superseded) FURTHER reduction — slice ⟶ single-index «suffix/drop» form

`slice_P_descending` (two free indices `a ≤ b`) reduces to a **single-index**
statement by the prefix lemma. Set `N = seg M 0 b`; then `N ∈ ST_PS`
(`m_6_7_standard_prefix`), `Lng N = Suc b`, and by `seg_of_seg`
`seg M a b = seg N a b = seg N a (Lng N - 1) = drop a N`
(`seg_to_last_eq_drop`). So:

> **core** (the only remaining obligation): `N ∈ ST_PS ⟹ descending (P (drop j N))`.

Two green conditional lemmas now lock the whole reduction chain in
`pss_mechanized.thy` (verified, no sorry):
- `slice_P_descending_of_drop`: `core ⟹ M∈ST_PS ⟹ a≤b ⟹ b≤Lng M-1 ⟹
  descending (P (seg M a b))`.
- `m_6_8_standard_slice_Br_descending_of_drop`: `core ⟹ [p_6_8 hyps] ⟹
  monoT (seg M j0' j1') ∧ descending (Br (seg M j0' j1'))` — the full prop1
  conclusion, modulo `core`.

So `p_6_8_standard_slice_Br_descending` is discharged the moment `core` is
proven. The induction below is now stated for `core` (suffix `drop j N` of a
standard `N`), which is cleaner than the two-index slice: `drop j N` for
`N ∈ SkT_PS k`.

## `core` / `slice_P_descending` proof strategy (the remaining hard core)

Row-0 part is FREE (`m_6_4_P_leftend_mono` on `seg M a b ∈ T_PS`). The row-1
tie-break is the irreducible content (= the article's §6.8 induction, content.md
1450–1615). Plan: induct on the level `k` with `M ∈ SkT_PS k` (as in prop2,
using `SkT_PS_mono`):
- **base `k=0`**: `M = diagSeq u v`; `seg M a b = diagSeq (u+a)(u+b)` (diagonal
  slice, cf. `seg_0_diagSeq`), which is non-multi (`not_multiT_diagSeq`), so
  `P (seg M a b) = [seg M a b]` — a singleton, trivially descending.
- **step `M = M''[n]`**, `M'' ∈ SkT_PS k`: the oper expands as
  `M''[n] = take j0 M'' @ concat_{k'<n} (IncrFirst^{k'·d0}) (seg M'' j0 (j1-1))`
  where `j1 = Lng M''-1`, `d1 = 0` always, so each block shifts ONLY row-0 (by
  `k'·d0`) and keeps row-1. Key tools:
  - `m_6_2_P_IncrFirst`: `P (IncrFirst N) = map IncrFirst (P N)` (equivariance).
  - `entry_IncrFirst` / `entry_funpow_IncrFirst0`: `IncrFirst` raises row-0 by 1,
    fixes row-1 ⟹ the tie-break predicate is **`IncrFirst`-invariant**.
  - A slice within the prefix `take j0 M''` or within a single block reduces to a
    slice of `M''` (IH), possibly after stripping an `IncrFirst^{k'd0}`.
  - **crux**: a slice spanning ≥2 blocks. If `d0 > 0` (`i1 = 1`), components in
    different blocks have row-0 ends differing by a positive multiple of `d0`, so
    the tie-break across blocks is vacuous (only within-block pairs matter ⟹ IH
    via `IncrFirst`-invariance). If `d0 = 0` (`i1 = 0`, identical block copies),
    needs separate care. (This is where the formalisation effort concentrates.)

## Two further reductions of `slice_P_descending` (green tools in place)

The row-0 part of `slice_P_descending` is free (`m_6_4_P_leftend_mono`); the
row-1 tie-break is the core, which can be peeled two ways:

- **slice-length induction (via `descending_snoc`, green).**
  `P (seg M a b) = P (seg M a (a+Pcut-1)) @ [seg M (a+Pcut) b]` when `seg M a b`
  is multi (else `P` is a singleton, trivial). The prefix is a shorter slice ⟹
  IH; `descending_snoc` then reduces the goal to: the new last component
  `seg M (a+Pcut) b` is `≤` (in the descending order) the previous last
  component `last (P (seg M a (a+Pcut-1)))`. I.e. the obligation collapses to the
  **adjacent-cut tie-break**: for two *consecutive* `P`-cut points `p < q` of the
  slice with `entry M 0 p = entry M 0 q`, one has `entry M 1 p ≥ entry M 1 q`.
- **prefix reduction (via `m_6_7_standard_prefix`, green).**
  `seg M 0 b ∈ ST_PS`, and `seg M a b = seg (seg M 0 b) a b` (`seg_of_seg`). So
  WLOG the slice is a **suffix** `drop a N` of a standard `N := seg M 0 b`.

Either way the irreducible core is a rank-induction over the standard form's
`oper` structure (the article's content.md 1450–1615), still TODO.

## SKELETONS in worktree `../pss-slice` (green except the step `sorry`)

Two prototypes were built (worktree `../pss-slice/pss_mechanized.thy`, kept off
`main` while a `sorry` remains). Green helpers from both, all reusable:
**`take_seg`** (`take c (seg M a b) = seg M a (a+c-1)`, `1≤c`, `c ≤ Suc b - a`),
**`drop_seg`** (`drop c (seg M a b) = seg M (a+c) b`), **`seg_diagSeq`**
(`u≤v, a≤b, b≤v-u ⟹ seg (diagSeq u v) a b = diagSeq (u+a)(u+b)`),
**`not_multiT_seg_diagSeq`**.

### (A) slice-length induction — reduces to adjacent-cut tie-break
`induction "b-a" … less_induct`; multi case
`P (seg N a b) = P (seg N a (a+c-1)) @ [seg N (a+c) b]` (`take_seg`/`drop_seg`/
`poper_P_multi`), prefix shorter ⟹ IH, `descending_snoc` closes with row-0 free
(`m_6_4_P_leftend_mono`). The single `sorry` is the **adjacent-cut row-1
tie-break**: `c = Pcut (seg N a b)`, `c2 = Pcut (seg N a (a+c-1))`,
`entry N 0 (a+c2) = entry N 0 (a+c) ⟹ entry N 1 (a+c) ≤ entry N 1 (a+c2)`.
This is local but still needs the rank/oper structure, so route (B) is preferred.

### (B) rank induction (CURRENT, matches the article) — base done
`slice_P_descending`: `N ∈ SkT_PS k ⟹ a ≤ b ⟹ b ≤ Lng N - 1 ⟹
descending (P (seg N a b))`, `proof (induction k)` over the rank, slice carried.
- **base `k=0`** — DONE: `N = diagSeq u v`; `seg N a b` is a `diagSeq`
  (`seg_diagSeq`), hence non-multi (`not_multiT_seg_diagSeq`), so `P` is a
  singleton ⟹ `descending` trivial.
- **step `N = M'[n]`** (`M' ∈ SkT_PS k`, `n ≥ 1`). Key foundation DONE:
  **`oper_nth_lt`** (green) — `(M[n]) ! i = M ! i` for `i < Lng M - 1`, in all
  `oper` cases (degenerate `M[n] = Pred M = butlast M`; generic
  `M[n] = take j0 M @ B₀ @ …` with the `k=0` block `B₀` carrying the unshifted
  `M`-entries on `[j0..<j1]`, so `take j0 M @ B₀ = take j1 M`). Step sub-cases:
  - `Lng M' = 1`: `N = M'[n] = M'`, slice of rank-`k` `M'` ⟹ **IHk**. DONE.
  - `b < Lng M' - 1` (slice within the `butlast` prefix): `seg N a b = seg M' a b`
    by `oper_nth_lt`, lower rank ⟹ **IHk**. DONE.
  - `b ≥ Lng M' - 1` (slice reaches the expanded block region) — the remaining
    work, now with the layout exposed and split on `d0`. Here the `oper` is
    necessarily generic (the degenerate case has `Lng N = Lng M' - 1`, forcing
    `b < Lng M' - 1`); `notzero`, `haspar`, `j0 < j1` and
    `layout : N = take j0 M' @ concat (map ?f [0..<n])` are GREEN, then
    `cases "0 < idx1 M' (Lng M'-1)"` splits into two `sorry`s:
    - **`d0pos`** (`i1=1`, row 1 of `M'` at `j1` positive): cross-block row-0
      ties impossible (row-0 ends differ by positive multiples of `d0`).
    - **`d0zero`** (`i1=0`): `d0=d1=0`, all blocks `= B₀ = map (M'!) [j0..<j1]`
      identical, so `N = take j1 M' @ B₀^{n-1}` is periodic past `take j1 M'`;
      tie-break reduces to within-`B₀` (a slice of `M'`).

  These two are exactly the article's block-spanning cases (content.md
  **1478–1586**), proved there by a rank (`k₀`) induction that constructs a
  derived standard form `N'` and uses the `FirstNodes`/`TrMax`/`Joints` relation
  and `(0,j0^N) ≤ (0,j1^N)` (the `d0>0` strict row-0 increase). NB the article
  inducts on `Br(M')` directly via `FirstNodes`; our `P`-of-slice framing is
  equivalent on content but the transcription of `N'` + the `FirstNodes`
  bookkeeping is the bulk of the remaining effort.

## Status / Plan

1. ✅ design + empirical reduction; ✅ `seg_nth_eq`, `seg_of_seg` (green);
   ✅ `descending_P_of_ST`, `entry_FirstNodes_eq_component_gen`,
   `descending_Br_of_FN_tiebreak`, `descendingD`, `descending_snoc` (green);
   ✅ correction A7.
2. **TODO (hard core)**: `slice_P_descending` — the row-1 tie-break, now isolated
   to the adjacent-cut tie-break (or, after prefix reduction, descending of `P`
   of a suffix of a standard form). Needs the `k`-induction over `oper` with the
   `IncrFirst`-invariance of the tie-break (`m_6_2_P_IncrFirst` / `entry_IncrFirst`);
   multi-block-spanning / `d0 = 0` is the crux. Largest remaining piece.
3. Assemble `m_6_8_standard_slice_Br_descending` from `slice_P_descending` +
   `seg_of_seg` + `m_6_2_mono_ancestor_slice`.

## Conditional Br induction — validated foundation (2026-05-27)

Re-architected to the article's **faithful conditional Br induction**
(`m_6_8_slice_Br_descending_monoT`, content.md 1422–1614), proved by plain
rank induction on `k`. Base (`k=0`, diagSeq slice has empty `Br`), `multiT N`
(M = P(N)₀ ∈ SkT_PS k, IHk), `Lng N = 1` (vacuous) and the `jsmall`
(`j1' < Lng N - 1`, slice within `butlast` prefix) cases are GREEN. The `jlarge`
groundwork (oper is generic; `notzeroN`, `hasparN`) is GREEN. Remaining: the two
block-spanning `sorry`s `d0zero` (i1=0, 1460–1514) and `d0pos` (i1=1, 1516–1589).

Two reusable pillars now GREEN (in `pss_mechanized.thy`, just before the main
lemma):

- **Descending algebra** (head-pair lexicographic order `cdom`):
  `cdom`, `cdom_refl`, `cdom_trans`, `descending_via_cdom` (descending ⟺
  cdom-monotone along the index), `descendingI_cdom`, `descending_cdomD`,
  `descending_append` (`A@B` descending ⟸ both descending + junction
  `cdom (last A) (B!0)`), `descending_take` (prefix of descending). These reduce
  every sub-case's `Br(M') = take J₁ (Br N') @ blocks` goal to cdom transitivity
  + one junction inequality.
- **d0zero block periodicity** (i1=0 ⟹ d0=d1=0, blocks k-independent):
  `nth_concat_replicate`, `oper_d0zero_expand`
  (`M[n] = take j₀ M @ concat (replicate n (map (M!) [j₀..<j₁]))`),
  `oper_d0zero_nth` (`(M[n])!(j₀+q·w+s) = M!(j₀+s)` for `q<n`, `s<w=j₁-j₀`).

Isabelle note: `Lng M - 1` is rewritten to `Lng M - Suc 0` by `One_nat_def`
(a default simp rule), which de-syncs any rule stated with literal `1`. Build the
oper expansion by `poper_oper_expand[..., unfolded Let_def]` (pure rewriting, no
normalisation), collapse `i1=0` shifts by `subst i1z`, and add `del: One_nat_def`
when a `Lng M - 1` rule must fire under simp.

CORRECTION CANDIDATE: content.md 1462 writes `j_1 = j0^N+(n+1)(j1^N-j0^N)-1`,
but the M-decomposition on the **same line** has `n` blocks (`k=0..n-1`), giving
`j_1 = j0^N + n(j1^N-j0^N) - 1`. The `(n+1)` is an off-by-one typo (should be `n`),
consistent with our (yaBMS-validated) `oper`. To be logged in corrections.md.

### Next (d0zero, 1460–1514)
- 1464 `j1' ≤ j0^N`: cannot arise under `jlarge` (`j1' ≥ Lng N-1 > j0^N`).
- 1502 `j0^N ≤ j1'`... actually `j0^N ≤ j'0`: slice lands in one block; by
  `oper_d0zero_nth`, `seg M j'0 j'1 = seg N (j0^N+r) (j0^N+r')`, then IHk.
- 1466 `j'0 < j0^N < j'1`: the hard `Br(M')` decomposition via
  `FirstNodes(N')`/`TrMax(N')`; uses `descending_append` + the junction
  `N_{0,j0^N} < N_{0,j1^N} = (Br(N')_{J₁})_{0,0}`.

## d0zero: confinement + case 1502 done (2026-05-27)

More GREEN machinery in the worktree (`../pss-slice`), all validated:

- **Row-0 value characterisation**: `oper_d0zero_entry0`
  (`entry (M[n]) 0 x = entry M 0 (j₀ + (x-j₀) mod w)` for `x ≥ j₀`),
  `parent_block_entry0_min` (`j₀` is the row-0 minimum of its block, strict at
  interior offsets — from `nextrel0 M j₀ (Lng M-1)`).
- **Confinement (article 1510)**: `oper_d0zero_le0_confined` — in the `i₁=0`
  periodic layout, `(nextrel0 (M[n]))** a b` with `a ≥ j₀` forces
  `b < j₀ + ((a-j₀) div w + 1)*w` (b stays in a's block). Proof: `rtranclp_induct`
  with invariant `j₀ ≤ · < j₀+(q+1)w`; each block-start carries the row-0 minimum
  `M_{0,j₀}`, which no `nextrel0` step (strictly increasing row-0) can reach from
  within the block — the barrier argument.
- **Case 1502** (`j₀^N ≤ j'₀`) of d0zero is now **fully proven**: confinement +
  periodicity give `seg M j'₀ j'₁ = seg N (j₀^N+r) (j₀^N+r')` (one block), `leR`
  transfers through the equal slices via `adm_le0_seg`, then IHk on `N`. (Used
  `define` for the div/mod offsets to keep them opaque to simp.)

Remaining d0zero `sorry`: **1466** (`j'₀ < j₀^N < j'₁`, slice straddles the
trunk/branch junction) — needs the **Br-under-oper decomposition** via
`FirstNodes(N')`. d0pos (1516–1589) likewise. That decomposition is the central
remaining piece for both.

Isabelle notes: `(M[n])` must be annotated `((M::pairseq)[n])` whenever a head
combinator (`Lng`, `nextrel0`, `entry`) is applied directly to it (parse
ambiguity vs list application). For block-offset arithmetic, prove identities by
`linarith` (treating `q*w` as an atom) rather than `simp`, which expands
`(q+1)*w` / unfolds `let`-bound div/mod terms and thrashes; `mult_less_mono1` /
`mult_less_cancel2` for the strict-product steps.

## Br-under-oper decomposition: the mechanisation route (2026-05-27)

GREEN prerequisites added: `oper_d0zero_nth_prefix` (`(M[n])!x = M!x` for `x<j₀`)
and `oper_d0zero_seg_period_reduce` (`seg (M[n]) a b = seg (M[q+1]) a b` when `b`
is in block `q`, `q+1≤n` — the article's WLOG `q=n-1`, 1472).

**Key tool for the decomposition: `m_6_2_P_additive`** —
`P M = P(seg M 0 (j₀-1)) @ P(seg M j₀ (Lng M-1))` whenever `j₀` is a *left-minimal*
cut (`∀j<j₀. entry M 0 j ≥ entry M 0 j₀`). In d0zero every block-start carries the
row-0 minimum `N_{0,j₀^N}` (`parent_block_entry0_min`), so it is left-minimal
within the branch region `S = seg M' (TrMax M'+1)(Lng M'-1)`. Applying P-additivity
at the block boundaries decomposes `Br M' = P S` into `P(prefix) @ (P block)*`,
i.e. the article's `take J₁ (Br N') @ blocks`. Combined with `descending_append`
and the junction `N_{0,j₀^N} < N_{0,j1^N} = (Br N'_{J₁})_{0,0} ≤ (Br N'_{J₁-1})_{0,0}`
(latter = descending Br N', from IHk), this yields `descending (Br M')`.

Remaining concrete obligations for 1466 (and analogously d0pos):
1. compute/bound `TrMax M'` so the branch region `S` is pinned down;
2. identify the block-boundary cuts inside `S` and discharge their left-minimality
   (via `parent_block_entry0_min` + `oper_d0zero_entry0`);
3. fold the repeated `P block` via `m_6_2_P_additive` + `descending_append`;
4. establish `leR N 0 j'₀ j1^N` (so IHk gives `descending (Br N')`) — needs the
   periodic le0 transfer (one direction is `oper_d0zero_le0_confined`; the other
   is the within-block le0 lift already used in 1502).

## 1466 leR-N groundwork done; Br decomposition plan (2026-05-27)

GREEN now in the worktree: the 1466 case (`j'₀ < j₀^N < j'₁`) establishes
`descN' : descending (Br (seg N j'₀ (Lng N-1)))` (article 1476→IHk), via
- row-0 convexity `m_5_1_ancestor_tree_1` (木構造(1)) : `le0 M j'₀ j₀^N`;
- `[0,j₀^N]` agreement `oper_d0zero_nth_le_parent` + `le0_prefix_agree` : `le0 N j'₀ j₀^N`;
- `le0_trans` with `le0 N j₀^N (Lng N-1)` (from `parR0N`) : `le0 N j'₀ (Lng N-1)` ⟹ leRN.
New green helpers: `nextrel0_prefix_imp`, `le0_prefix_agree`, `oper_d0zero_nth_le_parent`.

Both remaining `sorry`s (1466, d0pos) reduce to the SAME final obligation:
**`descending (Br M')` from `descN'` + block structure**, via this concrete plan
(N' = seg N j'₀ (Lng N-1), J₁ = Lng(Br N')-1):

1. WLOG `j'₁` in the last block (`oper_d0zero_seg_period_reduce`, q=n-1).
2. **`Br M' = take J₁ (Br N') @ B`** where `B` is a list of branch components each
   equal to the block `seg N j₀^N (j1^N-1)` (head `N!j₀^N`), possibly with a partial
   final component — article 1486/1492/1498 (3 sub-cases on `FirstNodes(N')_{J₁}`
   position vs `TrMax(N')`). Mechanise by **`m_6_2_P_additive` at the block-boundary
   cuts** (left-minimal by `parent_block_entry0_min`) inside the branch region
   `S = seg M' (TrMax M'+1)(Lng M'-1)`. Needs: relate `TrMax M'` to `TrMax N'`
   (the trunk does not reach the repeated blocks), and the `FirstNodes(N')` position
   lemmas (`m_6_4_FirstNodes_TrMax_Joints`, `FirstNodes_nth`, `Joints_nth`).
3. **junction**: `(Br N'_{J₁})_{0,0} = N_{0,j1^N}` (article 1486) and
   `N_{0,j₀^N} < N_{0,j1^N}` (from `parR0N` = `nextrel0 N j₀^N (Lng N-1)`,
   `parent_block_entry0_min`). So `cdom (last (take J₁ (Br N'))) (B!0)` holds
   (strict row-0), and `descending_append` + `descending_take[OF descN']` +
   constant-`B` descending give `descending (Br M')`.

This step (computing `TrMax M'`, the P-additivity cut sequence, the 3 FirstNodes
sub-cases, and the d0pos `IncrFirst`-shift analog) is the last and largest piece.

## 1466 (d0zero) / d0pos sub-case map (article 1478–1596) — formalization targets

Notation: `N' = seg N j'₀ (j1^N)` (article writes `(N_j)_{j'₀..j1^N}`; in our worktree
`descN' = descending(Br(seg N j'₀ (Lng N-1)))` since `j1^N = Lng N-1` here),
`J₁ = Lng(Br N')-1`, `w = j1^N - j0^N` (block width, d0zero), `r = (j'₀-j0^N) mod w`.
Key fact (1480): `N_{0,j1^N}=0 ∧ j1^N-j'₀ > j0^N-j'₀ > 0 ⟹ TrMax(N') < j1^N-j'₀`, so `J₁≥0`.
`j_{-1}` = unique row-0 next-parent of `j0^N-j'₀` in `N'` (1482).

### d0zero, case `j'₀ < j0^N < j'₁` (the open sorry @9115). Trichotomy on FirstNodes(N')_{J₁}:
- **A. `j0^N-j'₀ ≤ TrMax(N')`** (1484-1488): `FirstNodes(N')_{J₁} = j1^N-j'₀`, `Br(N')_{J₁}=(N_{j1^N})`.
  `Br M' = take J₁ (Br N') @ replicate (n-2) blk @ [partial]`, `blk = seg N j0^N (j1^N-1)`,
  `partial = seg N j0^N (j0^N+r)`. `Lng(Br M')-1 = J₁+n-2`. Head sequence =
  `(Br N')_0..(J₁-1)` heads then `N_{j0^N}` ×(n-1). Junction: `N_{0,j0^N} < N_{0,j1^N} = (Br N'_{J₁})_{0,0}`.
- **B. `j_{-1} ≤ TrMax(N') < j0^N-j'₀`** (1490-1494): `FirstNodes(N')_{J₁}=j0^N-j'₀`,
  `Br(N')_{J₁}=seg N j0^N j1^N`. `Br M' = take J₁(Br N') @ replicate(n-1) blk @ [partial]`,
  `Lng-1=J₁+n-1`. Junction: `N_{j0^N} = (Br N'_{J₁})_0`.
- **C. `TrMax(N') < j_{-1}`** (1496-1500): `FirstNodes(N')_{J₁} ≤ j_{-1}`.
  `Br M' = take J₁(Br N') @ [seg M (FirstNodes(N')_{J₁}+j'₀) j'₁]`, `Lng-1=J₁`.
  Junction: `M_{FirstNodes(N')_{J₁}+j'₀} = N_{...} = (Br N'_{J₁})_0` (index `< j1^N` so M=N there).
- (case `j0^N ≤ j'₀` @1502 = already proven in worktree.)

### d0pos `N_{1,j1^N} > 0` (the open sorry @9120, article 1516–1596):
- no row-1 next-parent `j_{-2}^N` ⟹ `M = N[n] = Pred N` ⟹ reduces to an already-shown case (1518).
- else `δ = N_{0,j1^N}-N_{0,j_{-2}^N} > 0`, `M = take j_{-2}^N N @ ⨁_{k=0}^{n-1} IncrFirst^{kδ}(seg N j_{-2}^N j1^N)` (1524).
  Establish `(0,j_{-2}^N) ≤_M (0,j1)` by the per-block row-0 monotonicity (1526-1538, uses `entry_IncrFirst`/`m_6_2_P_IncrFirst`).
  - `j'₁ ≤ j_{-2}^N` (1540): prefix agrees with N ⟹ `M' = seg N j'₀ j'₁` ⟹ reduces to shown case.
  - `j'₀ < j_{-2}^N < j'₁` (1542-1576): get `(0,j'₀) ≤_N (0,j1^N)` ⟹ `descN'`; then trichotomy
    on `J₁` (=-1 @1546 trivial single component; ≥0 @1552 mirrors A/B/C with `j_{-3}` = next-parent of `j_{-2}^N-j'₀`).
  - `j_{-2}^N ≤ j'₀` (1578-…): quotient `q,r` of `j'₀-j_{-2}^N` by `j1^N-j_{-2}^N`; WLOG q=0 (1584);
    `j'₁<j1^N` ⟹ prefix=Pred N case; `j'₁≥j1^N` ⟹ `(0,j'₀)≤_N(0,j1^N)` ⟹ `descN'` ⟹ A/B/C again.

### Shared machinery still to build (the bottleneck, both sorries):
- **TrMax-under-oper**: `TrMax M'` vs `TrMax N'` — the trunk of `M'` does not reach the repeated
  blocks, so `TrMax M' = TrMax N'` (d0zero) and the branch region `S = seg M' (TrMax M'+1)(Lng M'-1)`
  is the periodic part. No `TrMax(seg …)`/`TrMax(…[n])` lemma exists yet.
- **Br-as-take-@-blocks**: fold the repeated `P`-components via `m_6_2_P_additive` at the
  block-boundary cuts (left-minimal by `parent_block_entry0_min`); the `take J₁ (Br N')` prefix
  is `descending` by `descending_take[OF descN']`; the block tail is `descending` by the new
  `descending_replicate`/`descending_const_head`; glue by `descending_append` + the single junction
  `cdom`. **Recommended first target: case A** (cleanest: single junction `N_{0,j0^N}<N_{0,j1^N}`).

## Progress 2026-05-27 (continued): case-A TrMax half done; blocker isolated to one row-1 inequality

Two green bricks added in `../pss-slice` (uncommitted, lines ~8832–8911):
- `nextrel1_prefix_imp` — row-1 next-relation transfers across a shared prefix `[0,c]`
  (the `nextrel1` minimality quantifier is confined to `[0,c]` since `le0` is
  index-monotone; transfer via `le0_prefix_agree` + pointwise row-1 agreement).
- `TrMax_eqI` — `M∈T_PS ⟹ (∀j'<j. nextR M 1 j' (j'+1)) ⟹ ¬nextR M 1 j (j+1) ⟹ TrMax M = j`
  (use `TrMax` directly without re-deriving from `Max`).

Empirically (`python/red_model.py`, UB5/NMAX4/KMAX4): `TrMax M' = TrMax N'` holds
universally (6129/6129). The **below-trunk half** (`j' < TrMax N'`) is DONE: `TrMax_trunk_step`
on `N'` transfers to `M'` via `nextrel1_prefix_imp`. The remaining gap is the **stop condition
at the trunk/branch boundary** (the 72/6129 hard cases, all block-width `w=1`).

**UPDATE 2026-05-27 (continued 2): TrMax-equality reduced to one named residual; doc's earlier
inequality was FALSE.** Five more green bricks added in `../pss-slice` (uncommitted, ~8924–9118):
`TrMax_eq_of_prefix_agree`, `TrMax_stop`, `TrMax_lt_last_of_row1_zero` (= article 1480,
`Br N' ≠ []`), `nextR1_boundary_stop_of_prefix` (discharges the EASY 6057/6129 boundary-stop
cases), and `TrMax_seg_oper_d0zero_eq` (the d0zero case-A `TrMax (seg (N[n]) j0' j1') =
TrMax (seg N j0' (Lng N-1))`, modulo the boundary stop). 

⚠️ **CORRECTION**: the inequality stated here previously, `entry N 1 j0^N ≤ entry N 1 (Lng N-2)`,
is **FALSE** (9 counterexamples, e.g. `N=(0,0)(1,1)(2,0)(2,0)(2,0)`). The **real residual**
(the hard 72-case boundary stop, after trunk confinement `TrMax N' ≤ j0^N - j0'`, empirically
6129/6129) is the standard-form structural fact **`entry N 1 j0^N ≥ entry N 1 (j0^N + 1)`**
(row-1 does not increase right after the row-0 parent of the last index; empirically 141/141
for d0zero standard `N`; false for non-standard `N`, so it needs `SkT_PS`/standard-form theory,
not the generic §5.1 parent lemmas). **Next-session target: this inequality** (`entry N 1 j0^N
≥ entry N 1 (j0^N+1)`) + the trunk-confinement `TrMax N' ≤ j0^N - j0'`; then
`TrMax_seg_oper_d0zero_eq` closes unconditionally and the `Br M' = take J1 (Br N') @ blocks`
decomposition (m_6_2_P_additive + descending_append) finishes case A. Audit scripts:
`python/slice_trmaxeq_audit*.py`.

## UPDATE 2026-05-27 (continued 3): the boundary residual reduces to ONE clean rank-induction lemma

The boundary stop, trunk confinement, AND the row-1 inequality all collapse to a single
self-contained standard-form lemma (empirically **1632/1632**; FALSE for non-standard N):

> **`N in SkT_PS k ==> nextrel0 N a b ==> entry N 1 b = 0 ==> a < c ==> c <= b ==> entry N 1 c = 0`**

("along a row-0 descent `a -> b` ending at a row-1-zero node, row-1 is zero throughout `(a,b]`").
**Wiring (short, only existing green bricks):** this lemma => F1 `not nextrel1 N' (j0^N-j0')(j0^N-j0'+1)`
(= `entry N 1 j0^N >= entry N 1 (j0^N+1)`, since adjacent-index nextrel1 is just row-1 strict
increase) => trunk confinement `TrMax N' <= j0^N-j0'` (969/969) => in TrMax_seg_oper_d0zero_eq's
residual `TrMax N' = Lng N'-2` forces `j0^N = j1^N-1` i.e. block width **w=1** (72/72), making the
boundary stop reflexive => TrMax_seg_oper_d0zero_eq unconditional. (Explains why the retracted
`entry N 1 j0^N <= entry N 1 (Lng N-2)` only held on the residual domain: there `Lng N-2 = j0^N`.)

**Proof = rank induction on k.** Base k=0 (diagSeq) vacuous (`entry · 1 b = 0 ==> b=0` contradicts
`nextrel0 ==> a<b`). Suc k (`N = M'[n]`): periodic d0zero/d0pos index bookkeeping through oper
(oper_d0zero_nth/_expand) + the multiT-M' case via `N <-> P M'` components (m_6_2_P_oper_1/2,
m_6_7_standard_P_components). ~200-line multi-build proof = its own session. **THE irreducible core
of §6.8 case A.** NB: `seg N j0^N (Lng N-1)` is monoT but NOT always standard (1236/1632), so the
recursion must go through the last P-component, not that segment.

## UPDATE 2026-05-27 (continued 4): RETRACTION — the "continued 2/3" reduction rests on a FALSE lemma

⚠️⚠️ **The (continued 3) interval lemma is FALSE**, clean counterexample (yaBMS-STANDARD):
`N = (0,0)(1,1)(1,0)`, `a,b,c = 0,2,1`: `nextrel0 N 0 2`, `entry N 1 2 = 0`, but `entry N 1 1 = 1 ≠ 0`.
The "1632/1632" (and the continued-2 "141/141" for `entry N 1 j0^N ≥ entry N 1 (j0^N+1)`, which
this same `N` also breaks: `entry N 1 0 = 0 ≥ entry N 1 1 = 1` is `0≥1`, false) were **bounded-
enumeration artifacts**: counterexamples first appear at KMAX=6 (not KMAX=4), and the "false for
non-standard N" probe did NOT filter standardness so it mislabeled this STANDARD counterexample
as non-standard. **Both `F1` and the interval lemma are RETRACTED.** All failures are in the
**d0pos** branch (`idx1 N (Lng N-1) = 1`): the IncrFirst block carries row-1 values rising from 0
at `j0` to positive at `j1`, so an interior offset can be row-1-positive while the block start reads 0.

**Still solid (Isabelle-proven, green, unconditional truth):** the 7 bricks
`nextrel1_prefix_imp`, `TrMax_eqI`, `TrMax_eq_of_prefix_agree`, `TrMax_stop`,
`TrMax_lt_last_of_row1_zero`, `nextR1_boundary_stop_of_prefix`, `TrMax_seg_oper_d0zero_eq`.
The last proves the case-A TrMax-equality **modulo the boundary-stop hypothesis** — that part is
sound. ONLY the *discharge route* for that hypothesis (via F1 / the interval lemma) was wrong.

**Methodology fix (mandatory before any further empirical claim here):** re-run `red_model.py` /
`slice_trmaxeq_audit*.py` with (a) a **yaBMS `is_standard` filter** on N, and (b) **KMAX ≥ 6**.
The earlier audits used neither and are unreliable.

**Open re-derivation:** the boundary-stop discharge for case A needs a NEW argument. The d0zero
sub-branch may still be true *restricted*, but a naive rank induction recurses into d0pos
(where it is false), so that route is blocked. The d0pos boundary likely needs the explicit
`IncrFirst^{kδ}` row-1 structure (article 1516-1589), not a generic interval/row-1 lemma.
**Next step is empirical re-derivation (with the methodology fix), not another proof attempt.**

## UPDATE 2026-05-27 (continued 5): TrMax route is SOUND for case A (methodology-corrected)

Methodology-corrected re-audit (yaBMS `is_standard` filter + enumeration to length 5,
`python/slice_caseA_trmax_recheck.py`-style) of the **faithful** case-A domain
(standard `N`, d0zero `entry N 1 (Lng N-1)=0`, `j0' < j0^N = parent N 0 (Lng N-1)`,
`leR M 0 j0' j1'`, **and the brick precondition `Lng N - 2 ≤ j1'`**):

> **`TrMax (seg (N[n]) j0' j1') = TrMax (seg N j0' (Lng N-1))` holds 738/738 (0 mismatches).**

So the green brick `TrMax_seg_oper_d0zero_eq`'s **conclusion is correct on case A**, and its
boundary-stop hypothesis **is a theorem on this domain** (dischargeable). The (continued 4)
retraction was right that the *F1/interval lemma route* is false, but that does NOT doom the
TrMax approach — only that one discharge route was wrong. ⚠️ (Earlier audits that omitted
`Lng N - 2 ≤ j1'` reported spurious mismatches: with `j1'=1` the slice `seg M 0 1` is a tiny
prefix unrelated to `N'`, so `TrMax` trivially differs; that guard is essential.)

**Revised next step:** find a CORRECT argument for the boundary stop
`¬ nextrel1 (seg M j0' j1') (TrMax N') (TrMax N' + 1)` on this (now confirmed-true) domain —
NOT via the retracted F1. Candidate: characterize the hard (block-boundary) cases empirically
(with is_standard + depth ≥ 5) to find a TRUE sufficient condition, then prove it. The
`TrMax_seg_oper_d0zero_eq` brick already reduces case A's TrMax-equality to exactly this stop.

## UPDATE 2026-05-27 (continued 6): the CORRECT boundary-stop condition (replaces false F1)

Methodology-corrected characterization (is_standard + depth 5) of the case-A boundary stop
`¬ nextrel1 M' (TrMax N') (TrMax N' + 1)` (M' = seg M j0' j1', N' = seg N j0' (Lng N-1)):
- **The stop holds 738/738** on the faithful case-A domain (it IS a theorem).
- Easy cases (`TrMax N' + 1` inside the M'/N' prefix-agreement region): already discharged by the
  green `nextR1_boundary_stop_of_prefix` (transfer `TrMax_stop` on N' via `nextrel1_prefix_imp`).
- **Hard cases** (`TrMax N'+1` reaches the block boundary, 576 instances): the stop follows from
  > **`entry M' 1 (TrMax N') ≥ entry M' 1 (TrMax N' + 1)`  (576/576 — row-1 does NOT strictly
  > increase at the block boundary)**,
  which kills `nextrel1` (it needs a strict row-1 increase). This is the **correct replacement for
  the retracted F1**. Note: the prior agent's "w=1" claim was a KMAX=4 artifact — here w ∈ {1,2,3};
  and "row-1 equal" is NOT universal (270/576), only the **≥** is (576/576). The clean N-coordinate
  form is NOT simple (`entry N 1 (j0^N-1) ≥ entry N 1 j0^N` matches only 300/576), so the proof
  should stay in **M'-coordinates** and use the d0zero periodic block layout
  (`oper_d0zero_entry0`/`oper_d0zero_nth` etc.): at the boundary, `M' ! (TrMax N')` is the last
  interior of block 0 and `M' ! (TrMax N'+1)` is the block-1 start, whose row-1 values satisfy ≥
  by the periodic structure.

**Concrete remaining proof target (confirmed TRUE):** `entry M' 1 (TrMax N') ≥ entry M' 1 (TrMax N'+1)`
on the case-A hard domain, in M'-coordinates via the periodic block layout. Then
`nextR1_boundary_stop_of_prefix` (easy) + this (hard) discharge the boundary stop, making
`TrMax_seg_oper_d0zero_eq` unconditional, after which the `Br M' = take J1 (Br N') @ blocks`
decomposition finishes case A. Audit: extend `python/slice_caseA_trmax_recheck.py`.

## Validation (2026-05-27): §6.8 prop1 target is empirically SOUND (methodology-corrected)

Rigorous re-validation of the WHOLE prop1 goal with the methodology fix (yaBMS `is_standard`
filter over ALL pairseqs to length 5, not the incomplete diag→oper generation; vs the older
`sk_68_prop1_audit.py` which used KMAX=3 generation without is_standard):
**250 standard N, 1420 ancestor slices checked, 0 monoT violations, 0 Br-descending violations.**
So unlike the (retracted) F1 inequality, the prop1 target itself has no false edges — the worktree
is proving a genuinely true statement. Combined with the case-A audits (TrMax route 738/738,
boundary stop 738/738, hard-case row-1 ≥ 576/576), the §6.8 case-A empirical foundation is solid.

## UPDATE 2026-05-27 (continued 7): case-A boundary stop PROVEN — TrMax equality now UNCONDITIONAL

The case-A boundary stop is now a GREEN theorem in `../pss-slice` (uncommitted), via the
trunk-routing that the methodology-corrected analysis pointed to (NOT the retracted F1):
- `le1_imp_entry1_le` — row-1 weakly increases along a row-1 ancestor chain (`nextrel1` rtrancl).
- `nextR1_boundary_stop_d0zero_caseA` — discharges `¬ nextR M' 1 (TrMax N')(TrMax N'+1)` on the
  case-A domain. HARD case: `oper_d0zero_nth` gives `M'!(TrMax N') = N!(Lng N-2)` (block-0 last
  interior) and `M'!(TrMax N'+1) = N!j0^N` (block-1 start); `j0^N` is on the N'-trunk
  (`j0^N - j0' ≤ TrMax N'`, arithmetic from `j0^N < Lng N-1`), so row-1 weakly increases to it
  (`trunk_le1` + `le1_imp_entry1_le`): `N₁,j0^N ≤ N₁,(Lng N-2)`, killing the strict `nextrel1`.
- `TrMax_seg_oper_d0zero_eq_caseA` — the UNCONDITIONAL `TrMax(seg (N[n]) j0' j1') =
  TrMax(seg N j0' (Lng N-1))` on the case-A domain (`j0' < j0^N`, article-1466).

Why this works where F1 didn't: the standalone N-form `entry N 1 (Lng N-2) ≥ entry N 1 j0^N` is
generically FALSE (47 fails), but TRUE under the hard-case condition `TrMax N' = Lng N'-2` (0 fails),
which the proof uses via `j0^N` on the N'-trunk — not as an N-coordinate inequality. Empirical
recheck (is_standard + depth 5, `python/slice_caseA_boundary_stop_recheck.py`): boundary stop
fails 0, hard M'-inequality fails 0, index identities 0 mismatches.

**Remaining for case A (9648 sorry):** only the `Br M' = take J1 (Br N') @ blocks` decomposition
(m_6_2_P_additive + descending_append + the junction); the TrMax half is fully done. **Next brick.**

## UPDATE 2026-05-27 (continued 8): case-A reduced to the Br = take@blocks decomposition (the hard passage)

Groundwork now GREEN in `../pss-slice` inside `m_6_8_slice_Br_descending_monoT` (~9648): `TrEq`
(`TrMax M' = TrMax N'` via `TrMax_seg_oper_d0zero_eq_caseA`) and `junc0`
(`entry N 0 j0^N < entry N 0 (Lng N-1)`, the row-0 strict junction, from `parR0N`/`nextrel0_def`).

**The sole remaining obligation for case A (9648 sorry)** is the article's central identity
`Br M' = take J1 (Br N') @ blocks` (1486-1500), then `descending_append` +
`descending_take[OF descN']` + `descending_replicate`/`descending_const_head` close
`descending (Br M')`. Mechanising the identity needs, per FirstNodes(N')_{J1} sub-case (A/B/C):
P-additivity folding of the branch region `S = seg M' (TrMax N'+1)(Lng M'-1)` via `m_6_2_P_additive`
at each block boundary (left-minimal by `parent_block_entry0_min`+`oper_d0zero_entry0`), and
`FirstNodes(N')_{J1}` identification via `m_6_4_FirstNodes_TrMax_Joints`/`FirstNodes_nth`/`Joints_nth`.
This is the hardest passage (~several hundred lines, multi-session). Empirically sound:
`python/slice_caseA_brdecomp_recheck.py` (is_standard + depth 5, 453 instances) — `descending(Br M')`
0 fails, `TrMax M'=TrMax N'` 0 fails, junction 0 fails, `descN'` 0 fails; sub-cases A=213/B=198/C=42.
**Next concrete brick: sub-case A's P-additivity fold (cleanest, single junction).**

## UPDATE 2026-05-27 (continued 9): sub-case A reduced to one precise block-fold identity

More GREEN groundwork in `../pss-slice` inside `m_6_8_slice_Br_descending_monoT` (~9670-9746):
`monoM'`/`M'PT` (M' ∈ PT_PS), `NpL`/`Npz`/`TrNplt` (= article 1480), `BrNpne`, and the two
co-anchored framings **`BrM'P : Br M' = P (seg M a j1')`** and **`BrNpP : Br N' = P (seg N a (Lng N-1))`**
with `a = j0' + TrMax N' + 1`, `j0^N < a ≤ j1^N`. The case-A `sorry` is split A(~9765)/B-C(~9770);
d0pos at ~9776 (sorry count now 3).

**Sub-case A's SOLE residual (9765)** is the block-fold identity, empirically confirmed 0/213
(`python/slice_caseA_subA_decomp.py`, is_standard + depth 5):
> `Br M' = take J1 (Br N') @ replicate (neff-2) blk @ [partial]`, `blk = seg N j0^N (j1^N-1)`,
> with **`neff = (j1' - j0^N) div w + 1`** (NB: the article's "n-2" is per-block-of-`j1'`, i.e.
> `neff`, NOT the raw `n`).
Proof = `m_6_2_P_additive` fold of `seg M a j1'` at block boundary `j0^N + w` (left-minimal via
`parent_block_entry0_min`) + induction over the `neff-1` repeated blocks (heads all `N!j0^N`);
then `descending_append` + `descending_take[OF descN']` + `descending_replicate` + junction `junc0`
(trunk/trunk by descN', block/block equal heads, trunk/block vacuous). This is the ~several-hundred-
line multi-session core; all surrounding groundwork is green and the identity is empirically sound.
Also `descending_Br_of_FN_tiebreak` reduces the goal to this FN tie-break (0/213). **Next: the
block-fold induction (dedicated session).**

## UPDATE 2026-05-28 (continued 10): block-fold machinery GREEN; formula corrected; two-regime bridge

The block-fold machinery is now GREEN in `../pss-slice` (worktree builds `Finished PSS`):
- `oper_d0zero_entry0_min` (~9363) — `entry M 0 j0 ≤ entry (M[n]) 0 x` for in-range `x ≥ j0`.
- `oper_d0zero_seg_P_split` (~9397) — single P-additivity step
  `P(seg (M[n]) a (B+s)) = P(seg (M[n]) a (B-1)) @ [seg M j0 (j0+s)]` at block boundary `B = j0+k·w`
  (left-minimal via `oper_d0zero_entry0_min`; trailing fragment non-multi by `poper_P_nonmulti`).
- `oper_d0zero_seg_P_hfold` (~9541) — whole-block fold by induction:
  `P(seg (M[n]) a (j0+m·w-1)) = P(seg (M[n]) a (Lng M-2)) @ replicate (m-1) blk`.
  (NB: the `by` at ~9481 is slow ~30s but green; candidate for later optimisation.)

⚠️ **FORMULA CORRECTION (supersedes continued-9's `neff`):** under the in-scope `bge` (`Lng N-1 ≤ j1'`),
let `qb = (j1'-j0^N) div w` (≥1, since `bge` ⟹ `j1'-j0^N ≥ w`), `r2 = (j1'-j0^N) mod w`. Then
**`Br M' = take J1 (Br N') @ replicate (qb-1) blk @ [partial]`**, `blk = seg N j0^N (Lng N-2)`,
`partial = seg N j0^N (j0^N+r2)` — empirically 0 fails at maxlen 4 AND 5. (continued-9's `neff` was
wrong for the `qb=0` cases, which violate `bge`.)

**Two-regime bridge (next-session care):** `a = j0'+TrMax N'+1 ∈ (j0^N, Lng N-1]`. The intermediate
`P(seg M' a (Lng N-2)) = take J1 (Br N')` holds **only when `a < Lng N-1`** (block-0 fragment
nonempty, J1≥1; ~24/54). For `a = Lng N-1` (J1=0, `take J1 = []`), block-0 fragment empty
(`P [] = [[]] ≠ []`) — the bridge must case-split on `a < Lng N-1` vs `a = Lng N-1`.

**Remaining to close 9765 (sub-case A):** (1) final fold = one `oper_d0zero_seg_P_split` at boundary
`j0+qb·w`, `s=r2`, glued to `hfold qb`; (2) the `P(seg M' a (Lng N-2)) = take J1 (Br N')` bridge
with the two-regime split; (3) descending assembly: `descending_append [descending_take[OF descN'],
descending_replicate/const_head]` + junction from `junc0`. Audit: `python/slice_caseA_subA_decomp.py`
(corrected), `slice_caseA_explore.py`, `slice_caseA_formula.py`.

## UPDATE 2026-05-28 (continued 11): new green brick `parent_block_le0`; bridge route corrected; two genuine residuals isolated

New GREEN reusable brick (worktree `../pss-slice`, uncommitted, `pss_mechanized.thy` ~8527–8612,
just after `parent_block_entry0_min`; worktree builds `Finished PSS`):
- **`parent_block_le0`** — `nextrel0 M (parent M 0 (Lng M-1)) (Lng M-1) ⟹ s < w ⟹
  le0 M (parent M 0 (Lng M-1)) (parent M 0 (Lng M-1) + s)`. The block start `j0` is the row-0
  ancestor (`≤_0`) of every block-0 interior. Proof: strong induction on the offset `s`; for `s>0`
  take the maximal strict-row-0 predecessor `p` of `x=j0+s` (which is `≥ j0` since `j0` itself is a
  strict predecessor by `parent_block_entry0_min`), so `nextrel0 M p x`, `p=j0+s'` with `s'<s`, chain
  by IH + `le0_trans`. This is exactly the `blockmono` precondition demanded by BOTH
  `oper_d0zero_seg_P_hfold` and `oper_d0zero_seg_P_split`; verified empirically `le0(N,j0N,j0N+s)`
  162/162 (is_standard, depth 5). **Audit clean** (no `slice_P_descending`/`_of_drop`/`m_6_8`/`F1`).

The full sub-case-A assembly was DRAFTED on top of this brick (fold via `hfold`+`split`+`BrM'fold`
all type-checked through line ~10210, M/N block-0 agreement `MNblk0`/`segMNa` green) but hit ONE
genuine logic error and was reverted to the original FN-tiebreak `sorry` to keep the worktree green.

⚠️ **BRIDGE-PROOF CORRECTION (the blocker):** the two-regime bridge
`P(seg N a (Lng N-2)) = take J1 (Br N')` (`Br N' = P(seg N a (Lng N-1))`, identity 0/132 in regime
`a<Lng N-1`) **cannot** be proven by `m_6_2_P_additive` at the **endpoint** cut `c = Lng N-1-a`:
that index is the row-0 **maximum** of the block, NOT left-minimal, so `m_6_2_P_additive`'s
left-minimality premise is FALSE there (the residual `entry N 0 (Lng N-1) ≤ entry N 0 (a+j)` for
interior `j` is false — interior < endpoint). The CORRECT route: split `seg N a (Lng N-1)` at its
**last `Pcut`** (which IS left-minimal), giving `Br N' = P(seg N a (lastPcut-1)) @ [lastcomp]`; the
last P-component is generally NOT a singleton (so the earlier `seg N (Lng N-1)(Lng N-1)` framing was
also wrong). Empirically `P(seg N a (Lng N-2)) = (all-but-last of P(seg N a (Lng N-1)))` is 0/132,
so the bridge conclusion is sound — only the cut location in the proof was wrong. Likely tool: a
P-snoc / `poper_last_P_multi` / `Pcut`-based lemma relating `P(X)` and `P(butlast-by-one X)`.

**Two genuine residuals for sub-case A (both empirically TRUE):**
1. **Bridge via last-Pcut** (regime `a < Lng N-1`, 132/150): the corrected route above. Everything
   else in the `a<Lng N-1` branch (fold `BrM'fold`, `descending_append`, `descending_const_head`
   block tail, junction via `junc0`+descN', `lastfull`) was drafted and is correct MODULO the bridge.
2. **Degenerate `a = Lng N-1 = j0^N + w`** (18/150): here `J1=0`, `take J1 (Br N') = []`, and
   `Br M' = P(seg M a j1')` is purely the block tail (all components head `N!j0^N`, 18/18). Needs a
   **block-boundary-anchored fold** — `oper_d0zero_seg_P_hfold` requires `a ≤ Lng N-2`, which fails
   here; close via `descending_const_head` once the boundary-anchored fold gives the component heads.
Audit scripts added in worktree: `python/slice_caseA_bridge.py`, `slice_caseA_regime.py`.

## UPDATE 2026-05-28 (continued 12): bridge lemma `P_seg_butlast_bridge` GREEN; regime needs further split

GREEN standalone brick (worktree `../pss-slice` ~8124-8140, builds `Finished PSS`):
- **`P_seg_butlast_bridge`**: `a < b ⟹ multiT (seg X a b) ⟹ Pcut (seg X a b) = b - a ⟹
  P (seg X a (b-1)) = butlast (P (seg X a b))`. Essentially definitional via `poper_last_P_multi`
  (`butlast (P S) = P (take (Pcut S) S)`) + `take_seg`. Pure `P`/`Pcut` property, no N-coords.
  Empirically 0/228366 at depth 6; necessity of `Pcut = b-a` confirmed (fails 340416/340416 otherwise).

⚠️ **The bridge does NOT cover the whole case-A regime by itself.** Of the 234 case-A `a<Lng N-1`
windows (depth 5): **mono(89)** (P is a singleton, `butlast = []` ≠ `P(seg a (b-1))`), 
**multiT ∧ Pcut=b-a (97)** (covered by `P_seg_butlast_bridge`), **multiT ∧ Pcut≠b-a (48)** (last
component is not at the endpoint — dropped index lies inside a non-final component). So closing the
sub-case A bridge needs a 3-way split: the `P_seg_butlast_bridge` branch (97), the mono branch (89),
and the multiT-`Pcut≠b-a` branch (48) — each with its own `Br M' = …` shape. This is more structure
than continued-11 assumed.

**Honest status: §6.8 case-A sub-case A is a genuine multi-session core.** Extensive green machinery is
in place (`oper_d0zero_entry0_min`/`_seg_P_split`/`_seg_P_hfold`, `parent_block_le0`,
`P_seg_butlast_bridge`, the TrMax/boundary-stop bricks), the target is empirically sound (0/1420 prop1,
0/453 caseA), and the residuals are precisely characterized — but closure keeps revealing further
sub-case structure (mono/multiT/Pcut-position × two regimes) and is a dedicated sustained effort, not
"one spawn away". Audit scripts: `python/slice_bridge_butlast.py`, `slice_bridge_pure.py`.

## UPDATE 2026-05-28 (continued 13): ✅ sub-case A CLOSED (verified green)

The d0zero 1466 **sub-case A is fully proven** (no sorry) — parent-verified: `../pss-slice` builds
`Finished PSS` and the only remaining `sorry`s are B/C (~10644) and d0pos (~10650). The FN-tiebreak
sorry is replaced by the `descending_append` route on the now-complete machinery. Both regimes:
- `a < Lng N-1` (J1≥1): `Br M' = P(seg M a (Lng N-2)) @ replicate (qb-1) blk @ [partial]`; the prefix
  `P(seg M a (Lng N-2)) = P(seg N a (Lng N-2)) = butlast (Br N') = take J1 (Br N')` via
  `P_seg_butlast_bridge` (the `multiT` + `Pcut = endpoint` hypotheses hold here — empirically
  `Pcut(seg N a (Lng N-1)) = (Lng N-1)-a` 100%, because the leaf's row-0 parent `j0^N < a`; the
  earlier "Pcut≠endpoint" worry does NOT bite within sub-case A). Block tail by `hfold`/`split`;
  descending by `descending_append[descending_take[OF descN'], descending_const_head]` + junction `junc0`.
- `a = Lng N-1` (J1=0): pure block tail `replicate (qb-1) blk @ [partial]`, descending by `descending_const_head`.
New helpers (worktree): `nextrel0_above_parent_trivial` (~8650; no proper row-0 ancestor of the trunk
leaf above its parent), `oper_d0zero_seg_P_blk1fold` (~9694; block-1-anchored fold for the J1=0 regime).

**§6.8 case A now: only sub-cases B/C (article 1490/1496) remain** (+ the separate d0pos 1516-1589).
B/C are the other FirstNodes(N')_{J1} positions and are analogous to A — and now have ALL of A's
machinery (`P_seg_butlast_bridge`, `parent_block_le0`, `hfold`/`split`/`blk1fold`, the boundary-stop /
TrMax bricks, the descending algebra) available as a template. Next: B/C, then d0pos.

## UPDATE 2026-05-28 (continued 14): sub-cases B/C — B true but needs NEW development; C status ambiguous

The sub-case A template does NOT transfer to B/C. In A, the branch region starts at
`a = j0'+TrMax N'+1 > j0^N` (since `j0^N-j0' ≤ TrMax N'`), so the fold helpers
(`oper_d0zero_seg_P_hfold`/`_split`, precondition `j0^N < a`) apply. In B/C, `TrMax N' < j0^N-j0'`
gives `a ≤ j0^N`, so that precondition FAILS and the A-bridge `P(seg M a (Lng N-2)) = take J1 (Br N')`
is false (60/60 counterexamples for B; `take J1 = []` while LHS nonempty).

- **B (article 1490-1494): empirically TRUE** (237/237 at depth 6): `FirstNodes(N')_{J1} = j0^N-j0'`,
  `Br M' = take J1 (Br N') @ replicate qb blk @ [partial]` — **`qb` whole blocks, ONE MORE than A's
  `qb-1`** (matches the article). Junction `N_{j0^N} = (Br N'_{J1})_0`. Needs a NEW trunk-spanning
  fold + junction (the `descending_Br_of_FN_tiebreak` route, not A's `descending_append`); reusable
  piece: high-half `P(seg M j0^N j1') = replicate qb blk @ [partial]` (0 fail).
- **C (article 1496-1500): status AMBIGUOUS.** This agent found **0 witnesses** (depth≤6, maxval≤3,
  n≤4) for its C-discriminant (`TrMax N' < j_{-1}`), so it could not validate C's decomposition —
  BUT the earlier continued-3 `brdecomp_recheck` reported **C=42** at depth 5 (different discriminant).
  ⚠️ **The two C-encodings disagree; reconcile before any C proof attempt** — C may be vacuous in the
  case-A regime, or one encoding is wrong. Investigate first (do not "fly blind").

**§6.8 status:** sub-case A CLOSED (verified green); **B** = a dedicated new sub-development (true,
tractable, well-mapped); **C** = needs empirical reconciliation (possibly vacuous) before proof; **d0pos**
= separate (IncrFirst^{kδ}). Worktree artifact: `../pss-slice/python/slice_caseBC_decomp.py`.

## UPDATE 2026-05-28 (continued 15): C reconciled — NOT vacuous (A=285, B=270, C=21)

Re-computed the A/B/C partition with the CORRECT `j_{-1}` (the row-0 parent of `d = j0^N - j0'`
within `N'`): over the case-A d0zero regime (is_standard, len 5, maxval 3, n≤3, 576 windows):
**A = 285, B = 270, C = 21.** So **C is NOT vacuous** (21 witnesses, e.g. `N=(0,0)(1,0)(2,0)(3,0)`,
`j0'=0, j1'=2`: `TrMax N' = 0 < j_{-1} = 1 = d-1`, `d=2`); continued-14's "0 witnesses for C" was a
mis-encoding of `j_{-1}` by that agent, and matches the earlier continued-3 `C=42` (maxval diff).
**C must be proven** (article 1496-1500: `Br M' = take J1 (Br N') @ [seg M (FirstNodes(N')_{J1}+j0') j1']`,
`Lng(Br M')-1 = J1`, junction `M_{FirstNodes(N')_{J1}+j0'} = N_… = (Br N'_{J1})_0`, that index `< j1^N` so M=N).
C occurs when N''s trunk is short (`TrMax N'` small) and `j_{-1} > TrMax N'`.

**§6.8 remaining (accurate map):** sub-case A CLOSED; **B** (270 cases, true, new trunk-spanning fold +
junction `N_{j0^N}=(Br N'_{J1})_0`); **C** (21 cases, true, the single-extra-component decomposition
above); **d0pos** (separate, IncrFirst^{kδ}). All empirically sound; each B/C/d0pos a dedicated
sub-development on the now-complete machinery.

## UPDATE 2026-05-28 (continued 16): B agent over-claimed; blk0fold isolated; worktree now COMMITTED (green)

The sub-case B agent reported "B-J1=0 closed" but **never obtained a verified `Finished PSS`** — its
builds ran 25-40 min and timed out, so its `oper_d0zero_seg_P_blk0fold` was UNVERIFIED. Parent
verification found blk0fold has (a) a pathological `seg_of_seg`+`linarith` in its `leftseg` step
(>2400s on compound div/mod terms) and (b) a genuine index-bound proof error in `blkseg` (~10100).
⚠️ Reminder (agent-workflow rule 5): **the build is the only truth; never accept an agent's "green"
self-report — verify at integration.**

Resolution: blk0fold's proof body isolated as `sorry` (statement kept; empirically validated 0-fail,
and B-J1=0 uses it soundly). Worktree now builds `Finished PSS` (54s) with 4 real sorries:
**blk0fold (proof TODO), B-J1≥1, C, d0pos.**

🔑 **The whole §6.8 work is now COMMITTED to a worktree branch `slice-wip-68`** (it had been
uncommitted for the entire session — a real loss risk): `fbd9017` = the full blk0fold proof attempt
(for later repair), `efbd321` = the green checkpoint. **Lesson: commit worktree green states to a
branch; do not leave the §6.8 development uncommitted.**

**§6.8 remaining (accurate):** sub-case A CLOSED; **blk0fold** proof repair (fast `seg_of_seg` side
discharge for `leftseg` + fix the `blkseg` index bound — both trivially true, just slow/buggy tactics);
**B-J1≥1** (the documented N-side P-additive split at `j0^N`, `parent N 0 j0^N < a` route); **C** (21
cases, single-extra-component); **d0pos** (separate). All empirically sound; machinery green.

## UPDATE 2026-05-28 (continued 17): concrete blk0fold-leftseg fix recipe (from B agent handoff)

For repairing `oper_d0zero_seg_P_blk0fold` (currently `sorry` at ~9961 on branch slice-wip-68;
full attempt at fbd9017): the pathological `leftseg` step was `seg_of_seg[OF aleEnd] (use cle lenQ in
linarith)` — `seg_of_seg`'s 2nd premise is `d ≤ b-a` (here `?w-1 ≤ ?End-?j0`). Replace with an
EXPLICIT witness (avoids the slow `linarith` on `Lng ?Q`):
```
have db: "?w - 1 \<le> ?End - ?j0" using wle r2w by simp   \<comment> ?w-1 \<le> qb*w \<le> qb*w+r2; wle: ?w \<le> qb*?w in scope
... by (rule seg_of_seg[OF aleEnd db]) ...
```
NB: blk0fold ALSO had a separate `blkseg` index-bound proof error (~10100, goal
`parent M 0 (Lng M-1) + i < Lng M - 1`) found by the parent build — fix that too when un-sorrying.
The ~35-40min builds were partly two concurrent builds oversubscribing the 12-core box (use ONE build).

## UPDATE 2026-05-28 (continued 18): blk0fold PROVEN green (parent, not agent)

`oper_d0zero_seg_P_blk0fold` is now a **real proof** (no `sorry`); worktree `slice-wip-68`
commit `552dcd7`, `Finished PSS` in 49s with NO slow steps. The B agent's `db`-witness recipe
(continued 17) fixed the `leftseg` blow-up, but the lemma had FOUR more landmines, all from
decision procedures / `simp` choking on the `?w`-expanded `parent` terms — diagnosed and fixed
incrementally by the parent (each build ~50s green or ~40min loop, so build-after-every-fix):

1. **leftseg `thus`**: `?j0+(?c-1) = ?j0+?w-1` index mismatch (nat-sub assoc) → explicit `idxL`.
2. **segL/idxe/ej**: `?j0+(?w-1) < Lng M` etc. — **both `linarith` AND `presburger` loop >2400s**
   in preprocessing once `j0lt` is supplied (the `?w` abbreviation re-expands `parent` twice under
   nested subtraction). Fix: chain `assoc` (`w0`-only linarith, fast) + `j0w1` (`by simp` trans);
   keep `j0lt` out of every `?w`-laden arith. Recorded as a CLAUDE.md gotcha.
3. **eqv**: needs `ej` (`?j0+(Lng M-2-?j0)=Lng M-2`) to match `?blk`; reorder `j0le2`/`ej` BEFORE
   `eqv` and feed `ej` to its `simp`.
4. **rightseg**: `Lng_seg` simproc shifts `?j0+(Lng Q-1)` into an assoc-different form `simp` won't
   re-close → rewrite endpoint with `arg_cong[OF e, of "seg ?MN (?j0+?w)"]`, not `simp`.
5. **nz (`¬ zeroT ?blk`)**: `Lng ?blk = Suc(Lng M-2)-?j0` normalizes messily; `simp add: zeroT_def`
   evaluates the `entry` conjunct into garbage. Fix: extract only the `Lng=1` conjunct and
   contradict `True` (`1 < Lng ?blk`). (The base-case `?partial` nz worked because `Lng = Suc r2`
   is clean — the difference is the messy `Lng M-2-?j0` endpoint.)

The B agent's "blk0fold closed/green" self-report (its builds all timed out, never `Finished PSS`)
was indeed false — landmines 2–5 were never verified. Parent build-at-merge caught it (the rule held).

**§6.8 remaining real sorries (3):** B-J1≥1 (11051), C (11057), d0pos (11077). All else green.

## UPDATE 2026-05-28 (continued 19): §6.8 B-J1≥1 — leftmin + fold proven green

Two more verified `have` blocks inside the caseB branch (worktree `slice-wip-68`,
commits `8b9ea44` leftmin + `b89989d` fold). `show ?thesis sorry` still remains
for the descending closure (Xdesc + junc_cdom), but the genuinely-new content of
B-J1≥1 is now green.

### leftmin (8b9ea44): `entry N 0 j0N ≤ entry N 0 q` for all q ∈ [a, j0N)
Route: `m_5_1_ancestor_basic_1[OF NT j0'lt0N j0Nle1 leRN]` gives `entry N 0 j0' <
entry N 0 j0N` → `m_5_1_parent_exists_1` yields a row-0 parent `p` (j0'≤p<j0N) →
`adm_nextrel0_seg` transfers to `nextrel0 N' (p-j0') (j0N-j0')` → uniqueness
(`idxsum_ex1_parent0_iff` + `the1_equality[rotated]`) identifies it as
`parent N' 0 (j0N-j0')` → caseB gives `p-j0' ≤ TrMax(N')`, hence `p < a`. The
`nextrel0_def` valley clause then closes leftmin.

**New Isabelle gotcha** (added to CLAUDE.md): `unfolding parent_def` on
`parent ?Np 0 (?j0N - j0')` ALSO unfolds the inner `?j0N = parent N 0 (Lng N - 1)`,
breaking matching with folded facts. Stash the inner index in a fresh `b` via
`obtain b where bdef: "?j0N - j0' = b" by blast` so `unfolding parent_def` only
hits the outer `parent`.

### fold (b89989d): `Br M' = P(seg M a (j0N-1)) @ ?Y`
M-side `m_6_2_P_additive[OF XT c0 cle lminX]` on `?X = seg M a j1'` at cut
`c = j0N - a`; `lminX` derived from `leftmin` via period agreement (`agree`) +
`entry_def`; segment conversions by `seg_of_seg[OF less_imp_le[OF aj1] db]` +
`arg_cong` for endpoints; `P(seg M j0N j1') = ?Y` from `hival` (blk0fold).

**Three more tactic landmines fixed:**
1. `entry_seg`+`agree`+`entry_def` in one `simp` does not close `fst(M!x)=fst(N!x)`;
   establish nth-equality at list level first, then a single `simp add: entry_def`.
2. `using c0 ac by linarith` on `?a + (?c-1) = ?j0N - 1` loops (the `?c`-double-
   expansion gotcha); chain `c0`-only assoc + `ac` by `simp` via `also`/`finally`.
3. `thus ?thesis using <eq> by simp` to rewrite seg endpoints is unreliable in
   `?c`/`?a` contexts; use `arg_cong[OF eq, of "seg M ?a"]` (blk0fold's recipe).

**§6.8 remaining real sorries (3, unchanged in count):** B-J1≥1 closure (Xdesc +
junc_cdom), C, d0pos. B-J1≥1's hardest math is now green; closure mirrors
sub-case A's `descending_take[OF descN']` + `descending_append`.

## UPDATE 2026-05-28 (continued 20): §6.8 B-J1≥1 — Xdesc proven green (closure-only sorry left)

Third verified `have` block (worktree `slice-wip-68`, commit `466f77e`,
`Finished PSS` 53s). The descending of LOW = P(seg M a (j0N-1)) is now green:
N-side `m_6_2_P_additive` at the SAME cut j0N (leftmin direct on N, no agree
needed), segLOW_N/segHIGH_N via `seg_of_seg` + `arg_cong` (twice for segHIGH_N's
two endpoint rewrites), `segMN` via `nth_equalityI` + `agree` for the period
bridge, then `descending_take[OF descN']`.

**One refactor hit:** `idx` had to be hoisted out of segLOW (M-side)'s `proof -
... qed` so segLOW_N (N-side) can reuse it.

**§6.8 status:** B-J1≥1 has 4 verified haves stacked (leftmin/fold/Xdesc/segMN);
just `show ?thesis sorry` remains, needing one final brick:

### junc_cdom plan (the one remaining piece)
`cdom (last LOW) (?Y!0)` via the head-equality route (NOT A's leafval — A's
multiseg/Pcutend live in `caseBC:True` and aren't in scope for B):

1. `LOWN = P(seg N a (j0N-1))`, `HIGHN = P(seg N j0N (Lng N-1))`, `J1 = length LOWN`.
2. Both non-empty (`a < j0N`, `j0N ≤ Lng N - 2`).
3. `last LOWN = LOWN ! (J1-1) = (LOWN @ HIGHN) ! (J1-1) = Br N' ! (J1-1)` via `nth_append`.
4. `Br N' ! J1 = HIGHN ! 0` via `nth_append` + brEq.
5. `cdomBr: cdom (Br N' ! (J1-1)) (Br N' ! J1)` by `descending_cdomD[OF descN']`.
6. `entry (HIGHN!0) i 0 = entry N i j0N` for i∈{0,1} via first-P-component-head
   (look for an existing lemma like `entry_P_first` or derive via `IdxSum...!0 = 0`
   pattern from line 6817 — `P M ! 0 = seg M 0 k`, then `entry (seg M 0 k) i 0 = entry M i 0`).
7. `Y0hd0/Y0hd1: entry (?Y!0) i 0 = entry N i j0N` via `cases "?qb = 0"` + `blkhdi`/`parhdi`.
8. `cdom_def` depends only on heads, so cdomBr + same-heads(HIGHN!0, ?Y!0) gives `cdom (last LOW) (?Y!0)`.

Then `descending (fold) = descending (LOW @ ?Y)` by `descending_append[OF Xdesc Ydesc]` + `junc_cdom`. Close.

## UPDATE 2026-05-28 (continued 21): A案 agent fan-out 結果 — B-J1≥1 完全 close、C/d0pos は blocker 報告

Agent X/Y/Z を `slice-wip-68@466f77e` ベースの 3 worktree（`pss-junc`/`pss-c-wip`/`pss-d0pos`）で並列実行。
parent ルール5「自己申告を信じず必ずビルド」を遵守し、X の green 主張を parent build で検証してから統合。

### Agent X — junc_cdom + descending_append 緑（worktree `junc-wip-68` → `slice-wip-68` ff-merge `1323561`）
8-step plan 通りに 132 行の証明を書き、`Finished PSS` 検証済、`p_*` 引用なし。
**B-J1≥1 完全 close**。`m_6_8_slice_Br_descending_monoT` 内の sorry は 3→2（caseC, d0pos）。

### Agent Y — caseC 重要発見：empirically 真、`monoT (seg M ?a j1')` に reduce
truth-check 結果（`python/slice_caseBC_decomp.py` をコピー）:
- depth 4 maxval 4 n≤5 で **caseC は 10 witnesses あり**（以前の「empirically UNVALIDATED」は探索深度不足だった）
- 全 witness で `Br N'`/`Br M'` ともに singleton（`J1=0`、`take 0 _ = []`）
- 全 witness で article 分解 `Br M' = take J1 (Br N') @ [...]` が成立、`descending` も真

**戦略的洞察（agent Y）**: caseC では `seg M ?a j1'` が monoT（non-multi、`P = [seg ...]`）なので
`Br ?M' = [seg M ?a j1']` の singleton、`descending` は自明。**核心は `le0 M ?a j1'`**。
これは次のチェインで分解可能:
- `nextrel0 M p j0N`（`?a ≤ p < j0N`、N-side `nextrel0` を `agree` で M に転送）
- `le0 M j0N j1'`（**新 brick が要**: `le0_M_block_extension: le0 N j0N (Lng N - 1) ⟹ le0 M j0N j1'`、d0zero block-replication 構造の延長）
- `?a ≤ p` + 推移 + `adm_le0_seg` → `monoT (seg M ?a j1')`
- `P_non_multi_singleton` + `descending_via_cdom` + `cdom_refl` で close

**推定 60-100 行**（新 brick 含む）。BC:False が常に caseB/caseC で singleta J1=0 を生むなら、案外 asmall:True の caseB ≥ J1≥1 と caseC の両方をこの monoT route で再 close できる可能性もある（要確認）。

### Agent Z — d0pos 構造解析：単独 agent では out of scope、9 sub-task に decompose
truth-check 結果（`python/d0pos_truth_check.py` をコピー）: 5,950 instances 0 violations（深度 6 まで empirically 真）。

**構造的相違（d0zero vs d0pos）**:
- d0zero: `M = take j0N N @ concat (replicate n block)`（リテラル繰り返し）
- d0pos: `M = (N_j)[0..j-2N-1] ⊕ ⊕_{k=0..n-1} IncrFirst^{kδ}((N_j)[j-2N..j1N])`（各 block で row-0 を `δ > 0` 増分）

d0zero の周期性補題群（`oper_d0zero_nth`, `oper_d0zero_entry0`, `oper_d0zero_le0_confined`,
`oper_d0zero_seg_period_reduce`, …）は `M ! (j0+qw+s) = M ! (j0+s)` に依存しているため d0pos には使えない。
新 infrastructure ~1500 LOC が要。

**Z 推奨 fan-out 9 sub-task**:
- Phase 1（infrastructure、逐次）: Z1=`oper_d1pos_expand`+`LngM`、Z2=`_nth`+`_entry0`+`_entry1`、Z3=`_le0_confined`、Z4=`_seg_period_reduce`
- Phase 2（case analysis、並列、Phase 1 後）:
  - Z5: 1a/2a の N-slice 還元（小）
  - Z6: 1b inter-block monotonicity `(0, j-2N+kw) ≤_M (0, j-2N+(k+1)w)`（article 1530-1538）
  - Z7: 2b `(0, j0') ≤_M (0, j1N)` 推移チェイン（Z6 引用）
  - Z8: 2b 内 3 sub-cases on `TrMax(N')` vs `j-3`（article 1564-1586、Z7 引用）
  - Z9: 1b/2b finalization（article 1539-1545, 1572-1586）

**§6.8 prop1 残**: caseC (60-100 行、新 brick 1 つ)、d0pos (~1500 LOC、9-agent fan-out)。
caseC が小ければ次にやるべきは caseC、d0pos は別計画。

## UPDATE 2026-05-28 (continued 22): caseC monoT route — empirically supported at limited depth, structural ambiguity at the (?a, parent] interval

Followed up on Agent Y's monoT hypothesis with focused `python/slice_caseC_monoT_check.py`:
- depth 4 maxval 3 n≤4: 6 caseC witnesses, **all monoT** (zero counterexamples).
- All 6 witnesses have the same shape: N=[(0,0),(1,0),(2,0),(3,0)], j0N=2, j0'=0, TrMax(?Np)=0, **?a = parent N 0 j0N = 1** (a CRITICAL coincidence).
- The seg M ?a j1' is monoT because nextrel0 M ?a j1' holds DIRECTLY (single edge): the valley clause `∀q∈(?a,j1'). entry M 0 q ≥ entry M 0 j1'` is satisfied — every intermediate position is in the d0zero block-cycle at row-0 value `entry N 0 j0N` = `entry M 0 j1'` (the seg has shape `[(low,0),(cycle-val,0),(cycle-val,0),...]`).

**Structural concern**: caseC says `parent N 0 j0N ≥ ?a` (weak inequality). In the explored witnesses we found `parent = ?a` (strict equality), making the interval `(?a, parent]` empty and the valley analysis trivial. But for general caseC, parent could be `> ?a`, leaving the `(?a, parent]` interval non-empty with NO direct constraint on entries there. The monoT route would then need an additional argument to establish the valley over `(?a, parent]`.

Truth at deeper depth (parent > ?a witnesses) is **not yet checked**; the depth-4/maxval-3 search is too narrow to surface the general case. Recommended next step: enumerate caseC witnesses with `parent N 0 j0N > ?a` strictly, verify monoT still holds (or find a counterexample). If monoT survives generally, proceed with the monoT-via-direct-nextrel0 route; otherwise the full article decomposition `Br M' = take J1 (Br N') @ [tail]` is required.

**Status**: caseC not closed in this session. B-J1≥1 fully green (slice-wip-68 `1323561`); the §6.8 prop1 lemma still has 2 sorries (caseC, d0pos).

**Addendum (deeper Y-script search, late-arriving result)**: a follow-up run of Y's full-decomposition
script at depth 5 / maxval 5 / n≤3 (which completed in background after the above was written) found
**42 caseC witnesses, all article-decomposition clean** (`Cidfail=0`, `Cprefixfail=0`, `Cfnfail=0`;
also 198 case-B, all `B-shape(qb whole)`). This is much stronger than caseC's prior "UNVALIDATED"
reputation — the full article decomposition `Br M' = take J1 (Br N') @ [seg M (FN[J1]+j0') j1']`
holds at this depth.

**Recommendation for next session**: (a) widen the monoT check to detect `parent > ?a` witnesses
and decide monoT vs full route, OR (b) commit directly to the full article decomposition
(~200 lines, mirrors sub-case A structurally, empirically robust at 42/42).

## UPDATE 2026-05-29 (continued 23): Dynamic Workflow fan-out (Opus 4.8) — d0pos Z1 green, caseC groundwork green

First use of the Workflow primitive (`workflow` keyword) with `model: 'opus'` (4.8) agents,
2-way parallel on `slice-wip-68 @ 1323561`. Both verified by parent build, merged into
slice-wip-68 (`8912c95`, `Finished PSS` 52s). Sorry count unchanged at 2 (caseC, d0pos) — both
results are green groundwork that relocate/prepare, not yet discharge.

### d0pos Z1 — GREEN (merge `cfaadf6`, lemmas at 8475/8511)
`oper_d1pos_expand` + `oper_d1pos_LngM`, the i1=1 analogs of `oper_d0zero_expand`. Built via
`poper_oper_expand` with d0=δ (row-0 shift live since 0<i1), d1=0. **Faithfulness note**: the
agent matched the actual `oper` def (block bound `Lng M - 1`, NOT the task-prose `Lng N`), so
`w = Lng M - 1 - parent M 1 (Lng M-1)` and `Lng(M[n]) = parent M 1 (Lng M-1) + n*w`. First brick
of the 9-task d0pos plan (Z1). No sorry, no p_* cite. Phase-1 infra; Z2-Z4 (nth/entry0/entry1,
le0_confined, seg_period_reduce) still needed before the d0pos case-analysis (Z5-Z9).

### caseC — PARTIAL (merge `8912c95`, groundwork at 11398+, sorry relocated to 11535)
Green reusable geometry haves: `monoNp`/`NpPT`, `?J1 = Lng(Br Np)-1`, `?fn = FirstNodes Np!J1`,
`?fnM = j0'+?fn`, `a_le_fnM`, `e_lt`, `p`/`jm1eq` (fresh-b trick), `jm1lt`, `caseC'`,
`nleaf` (article 1482 via `adm_nextrel0_seg`).

**The remaining caseC obligation (BULK, ~360 lines like sub-case B), in order:**
1. `?fn ≤ ?jm1` (article 1498): show `entry Np 0 ?fn < entry Np 0 (Lng Np-1)` from the last branch
   component being non-multi, then `nextR0_largest_below` twice → `?fnM < ?j0N`. (~40-60 lines, tractable.)
2. **THE BLOCKER — HIGH non-multiplicity**: `P(seg M ?fnM j1') = [seg M ?fnM j1']`, i.e.
   `seg M (FN[J1]+j0') j1'` is non-multi (single P-component, article 1498). Requires
   `entry M 0 ?fnM < entry M 0 q` for all `q ∈ (?fnM, j1']` — `?fnM` strictly row-0-dominates the
   whole tail, **crossing the oper n-fold repetition boundary at ?j0N**. No existing helper gives
   this M-side cross-repetition row-0 domination; needs a NEW named lemma.
3. LOW = `take J1 (Br Np)` (`m_6_2_P_additive` cut at `?fnM-?a`, period agreement on `[?a,?fnM]`
   since `?fnM<?j0N`, left-min from `idxsum_leftend_lmin` NOT a nextrel0 valley), `descending_take`.
4. junction `cdom (last LOW) (HIGH!0)` via head-equality (heads agree since `?fnM<?j0N`,
   tail head = `(Br Np ! J1)_0` via `entry_FirstNodes_eq_component`), mirroring caseB's junc_cdom.
5. close via `descending_append` + fold.

**RECOMMENDATION (agent C2)**: split off step-2's HIGH non-multiplicity as its OWN named lemma
FIRST — it is the one missing brick with no existing analogue and is the true blocker; the
LOW/junction parts then transcribe from sub-case B. Decomposition empirically sound (42/42).

## UPDATE 2026-05-29 (continued 24): caseC CLOSED + d0pos Z2 — §6.8 prop1 now d0pos-only

Second Workflow run (Opus 4.8, 2-way parallel), both parent-verified green and merged into
slice-wip-68 (`4310f7f`, `Finished PSS` 132s). **m_6_8_slice_Br_descending_monoT now has exactly
ONE sorry left: d0pos.** (B-J1≥1 + caseB-J1=0 + caseA + caseC all closed; only the i1=1 branch remains.)

### caseC — CLOSED (merge `4310f7f`, proof at 11535-12069, ~534 lines)
Full article-1498/1500 decomposition `Br M' = take J1 (Br N') @ [seg M (FN[J1]+j0') j1']`, 5 steps:
- **Step 1 fnM_lt** (`?fnM < ?j0N`, article 1498): last branch component `Br Np!J1 = seg Np ?fn (Lng Np-1)`
  is non-multi (`m_6_2_P_components_1`), `?fn < Lng Np-1` (else its parent ≤ TrMax contradicts nleaf+caseC'
  via `idxsum_parent0_unique`), `compdom` via `m_6_2_multi_crit_12`, then `nextR0_largest_below` from
  nleaf + `fn_ne_d` (parent uniqueness) + from p → `?fn ≤ ?jm1` → `?fnM < ?j0N`.
- **Step 2 hitail** (THE key brick): `P(seg M ?fnM j1') = [seg M ?fnM j1']` — the tail is a single
  non-multi component CROSSING the oper boundary. `Mdom`: `?fnM` row-0-dominates `(?fnM,j1']`: for q≤?j0N
  via `agree` + `Ndom` (compdom→N by entry_seg); for q>?j0N via `oper_d0zero_entry0_min`
  (entry M 0 q ≥ entry N 0 ?j0N > entry N 0 ?fnM). Then `poper_P_nonmulti` + `m_6_2_multi_crit_12`.
- **Step 3 LOW_eq**: `P(seg M ?a (?fnM-1)) = take J1 (Br Np)` — N-side `m_6_2_P_additive` at ?fnM
  (left-min `lminLOW` from `idxsum_leftend_lmin`, NOT a nextrel0 valley), HIGH_N single, transferred by `segMN`.
- **Step 4 junction** `cdom (last LOW) ?TL`: `descending_cdomD[OF descN']` + head equality
  (?TL head = (Br Np!J1) head = N_{?fnM} via agree + entry_seg).
- **Step 5 fold**: M-side `m_6_2_P_additive` split → `Br M' = take J1 (Br N') @ [?TL]`;
  `descending_append[OF descending_take[OF descN'], descending [?TL]]` + junction; `cases ?J1=0`.

### d0pos Z2 — GREEN (merge `ce9b236`, lemmas at ~8542-8678)
`oper_d1pos_nth` + `oper_d1pos_entry0` + `oper_d1pos_entry1` (row-1 UNSHIFTED — the d0pos vs d0zero
difference) + helper `nth_concat_map_const_len` (nth of concat of distinct equal-length blocks;
d0zero's `nth_concat_replicate` needs identical blocks, d1pos blocks differ per k; induction
`arbitrary: q B`). Z2 of the 9-task d0pos plan; Z1 (expand/LngM) already in. Next: Z3 (le0_confined),
Z4 (seg_period_reduce), then the d0pos case-analysis Z5-Z9.

**§6.8 prop1 status**: ONE sorry left (d0pos). All other cases closed.

## UPDATE 2026-05-29 (continued 25): d0pos — block-fold is the WRONG brick; the fold collapses to ONE mono component (caseC-shaped)

The d1pos-shape + d1pos-split workflow (empirical-first) overturned the "build a
d1pos block-fold family `oper_d1pos_seg_P_*`" plan:

- **`oper_d1pos_seg_P_split` is FALSE for delta>0.** In d0zero every block starts
  at the same row-0 value, so the block boundary B=j0+k*w is a row-0 left-minimum
  and `m_6_2_P_additive` peels one block. In d1pos block k's start carries row-0
  `entry M 0 j0 + k*delta` which is INCREASING, so B is the row-0 MAXIMUM among
  block starts; left-minimality fails and **P does not split at block boundaries**.
  Counterexample: `M=[(0,0),(1,1),(2,1)], n=2` → `M[2]=[(0,0),(1,1),(2,0),(3,1)]`,
  `seg(M[2],1,2)=[(1,1),(2,0)]` is a SINGLE P-component. (left-min fails 504/708.)

- **H1 (the right brick, empirically 550/0):** for a block-start anchor
  `a = j_2 + q*w` (q<n) and any b with `a<b<Lng M ∧ le0 M a b`,
  `P (seg M a b) = [seg M a b]` — a SINGLE mono component. The delta-shifted fold
  absorbs into ONE mono component (its later, larger row-0 entries keep the span
  mono; the row-1 last-node chain stays mono).

- **Paradox resolved:** descending(Br) needs the branch P-component heads row-0
  weakly DECREASING; delta>0 makes BLOCK heads INCREASING — no conflict because
  the blocks do NOT each become a component. The multi-component structure of
  `Br(seg M j0' j1')` comes ONLY from N's own pre-existing branch components (left
  of the fold); the whole fold is the SINGLE LAST mono component.

**Consequence — d0pos closure mirrors caseC, not a block-fold:**
`Br M' = take J1 (Br N') @ [single mono tail]`. The needed brick is the d1pos
analogue of caseC's `hitail` (HIGH non-multiplicity): the fold tail is one mono
P-component (via le0 → leR → monoT → `poper_P_nonmulti`), NOT a block-fold.
Verified: H1 550/0, H2 (last component mono) 932/0, descending 932/0, J1=-1 fold
row form (w=1) 15/0 — `python/d1pos_fold_shape.py`.

**Next brick:** `oper_d1pos_seg_mono` (block-start-anchored le0 slice is monoT,
P = singleton), then assemble the d0pos closure exactly like caseC (LOW = take J1
(Br N') via N-side P-additive + agree, junction cdom, descending_append).

## UPDATE 2026-05-29 (continued 26): H1 brick green; closure needs a 2nd d1pos brick (TrMax_seg)

- **oper_d1pos_seg_mono GREEN** (merged into slice-wip-68): monoT (seg (M[n]) a b)
  for a block-start anchor a with le0 (M[n]) a b (the H1 single-mono-component
  fact). Proof = caseC hitail route (not zeroT + leR via adm_le0_seg). This is
  the mono-tail brick for the d0pos closure.
- **Closure still blocked on a SECOND d1pos brick.** Transcribing the caseC
  closure to d0pos needs, besides oper_d1pos_seg_mono, the TrMax-equality /
  boundary-stop analogue:
    **TrMax_seg_oper_d1pos_eq_caseA** : TrMax (seg (M[n]) j0' j1') = TrMax (seg N j0' (Lng N-1))
  i.e. the d1pos analogue of `TrMax_seg_oper_d0zero_eq_caseA` /
  `nextR1_boundary_stop_d0zero_caseA`. The d0zero version's hard branch (stop
  index at the period boundary) uses the UNSHIFTED periodicity `oper_d0zero_nth`;
  the d1pos version must replace it with `oper_d1pos_nth` and account for the
  +delta row-0 shift at the block-1 head (block-1 head = (N_{0,j0N}+delta, N_{1,j0N})).
  No such lemma exists yet — it is the next brick.
- Plan: prove TrMax_seg_oper_d1pos_eq_caseA, THEN the closure assembles from
  caseC's template (Br M' = take J1 (Br N') @ [mono tail], LOW via descending_take,
  tail via oper_d1pos_seg_mono, junction cdom, descending_append).

## UPDATE 2026-05-29 (continued 27): caseC-reduction is WRONG for d0pos — TrMax_seg_oper_d1pos_eq_caseA is FALSE

The empirical-first workflow again caught a false target before any proof was written.

- **`TrMax_seg_oper_d1pos_eq_caseA` is FALSE.** Counterexample (standard, all
  hyps hold): `N = (0,0)(1,1)(2,2)(3,3)` (diagonal), n=1, j0'=0, j1'=2.
  `oper(N,1) = (0,0)(1,1)(2,2)`; LHS `TrMax(seg N[1] 0 2) = 2`,
  RHS `TrMax(seg N 0 3) = 3`. 2 ≠ 3. (132/3288 caseA slices fail.)
- **Root cause:** the d0zero caseA reduction rests on `TrMax N' < Lng N' - 1`
  (the reference slice N' = seg N j0' (Lng N-1) has a confined trunk), which
  comes from `entry N 1 (Lng N-1) = 0` (d0zero). For d1pos i1=1 means
  `entry N 1 (Lng N-1) > 0`, so the N'-trunk is NOT confined — it can fill the
  whole reference slice (TrMax N' = Lng N'-1, the diagonal/trunk-filling family).
  Then `TrMax M' = TrMax N'` simply fails.
- **Consequence — the d0pos closure CANNOT mirror caseC's "reduce to N'" route.**
  caseC/d0zero decompose `Br M' = take J1 (Br N') @ [tail]` via TrMax M' = TrMax N';
  that foundation is false for d1pos. The agent's diagnosis: compare against the
  **M'-trunk directly**, not the reference slice N'. The boundary-stop helper
  (`nextR1_boundary_stop_d1pos_caseA`) is provable (row-1 unshifted, bstop_fail=0)
  but useless because the TrMax-equality it would feed is false.
- **descending(Br M') itself is still empirically TRUE (932/0)** — provable, but
  the route must be re-derived around the M'-trunk.

**Next step (re-map, not re-prove):** empirically determine the ACTUAL d1pos
decomposition — what is `TrMax (seg M[n] j0' j1')` in terms of the M'-trunk, and
how does `Br M'` actually decompose for i1=1 — BEFORE attempting any closure proof.
Counterexample finder: `python/d1pos_trmax_caseA_k4.py`.

## UPDATE 2026-05-29 (continued 28): correct d0pos design — M'-trunk-direct, descending(P Y') via row-1 tie-break

The re-map workflow (both agents "mapped", 0 empirical failures) gives the correct
caseC-FREE design for d0pos.

### TrMax M' closed form (python/d1pos_trmax_formula.py, 474/0, 1215/0)
`TrMax (seg M' j0' j1') = min(trunkM'(j0'), j1'-j0')`, where (j0'<=j0N)
`trunkM'(j0') = min(TrMax(seg N j0' (Lng N-1)), (j1N-1)-j0')`. The defect vs the
(false) caseA equality is the **off-by-one (j1N-1 not j1N)**: d1pos drops N's last
column and (d1=0) keeps row-1 constant across the tail, so the M'-trunk breaks one
column early. n does NOT appear (trunk fixed by the first block). A conditional
caseA equality holds excluding the trunk-filling + window-binding families.

### Br M' decomposition (python/d1pos_br_decomp.py, d1pos_br_cdom.py)
caseC's `take J1 (Br N') @ [tail]` REFUTED (FirstNodes identity fails 67/244;
#BrM'-#BrN' ranges -2..+2). Correct = **M'-trunk-direct**: `Br M' = P Y'`,
`Y' = seg M' (TrMax M'+1)(Lng M'-1)`, with (0 failures):
- **(S1)** every component is monoT/zeroT (a single block-anchored le0 slice; H1 per cut).
- **(S2)** the branch window is entirely inside the delta-fold (j0'+TrMax M'+1 >= j0N).
- **(S3)** cdom-descending: row-0 weakly decreasing is FREE (m_6_4_P_leftend_mono on
  Y'∈T_PS); the row-1 tie-break (row-0 tie => row-1 strictly falls) is the genuine content.

This is the SAME shape as the already-green §6.8 prop2 (m_6_8_standard_P_descending):
a row-1 tie-break on P-components — NOT the caseC machinery.

### Closure = 3 bricks (everything else GREEN; descending_take/append/const_head NOT needed)
- **B1 oper_d1pos_Br_comp_mono** (S1, MEDIUM): generalize H1 (oper_d1pos_seg_mono) over P's IdxSum cuts.
- **B2 oper_d1pos_Br_cdom_step** (S3 row-1 tie, HARD, irreducible core): "row-0 tie of two
  fold cells => row-1 weakly decreasing in P-cut order" — via m_6_4_P_IdxSum (cut left-ends),
  oper_d1pos_entry0/entry1 (row-1 block-invariant), oper_d1pos_le0_blockstarts/block_chain.
- **B3 oper_d1pos_Br_descending** (assembly, EASY): descendingI_cdom + cdom_trans + row-0(B1?)/row-1(B2),
  STEP0 Br=[] trivial; both regimes (j0'<j0N, j0N<=j0') reduce to the same STEP1-3
  (regime B folds via oper_d1pos_seg_period_reduce).

Both regimes use the M'-trunk-direct view; the dead TrMax-equality route is fully abandoned.

## UPDATE 2026-05-29 (continued 29): B1 green; B2 needs standardness (now 373/0), reduces to nextrel1

- **B1 oper_d1pos_Br_comp_mono GREEN** (merged): every Br M' component is monoT/zeroT.
  Surprise simplification — reduces in 3 lines to the generic `m_6_2_P_components_1`
  (P never emits a multi component for any T_PS source); no d1pos-specific work, only
  Q ∈ T_PS. So S1 is essentially free.
- **B2 oper_d1pos_Br_cdom_step (row-1 tie) — literal form is FALSE; needs STANDARDNESS.**
  - Q ∈ T_PS form: 2649/14733 row-0-tie pairs FAIL (e.g. N=(0,0)(0,1)(1,2), Q=seg M 0 1
    has row-0 tie but row-1 increases). Branch-region-of-monoT (no std): still 1062/3738.
  - The isolated fold-cell arithmetic ("row-0 tie => row-1 weakly decreasing") and the
    naive "le0 N a b => entry N 1 a >= entry N 1 b" are BOTH false even for standard N.
  - **With M=N[n] STANDARD (the prop1 M ∈ SkT_PS k context), B2 HOLDS.** Parent-widened
    sweep: len5/val2 = 373 tie pairs / 0 fails (the agent's thin 36-pair/shared-offset
    pool was just length≤4). Robust.
  - **Reduction (the irreducible core):** map the two consecutive branch left-minima to
    absolute M-indices; row-1 = entry N 1 joff (block-invariant, oper_d1pos_entry1). The
    row-0 tie forces `nextrel1 N joffR joffL` (joffR is the row-1 parent of joffL in N),
    giving entry N 1 joffR < entry N 1 joffL = B2. Deriving nextrel1 from the tie NEEDS
    N's standardness/admissibility — same hard kernel as the green prop2
    (m_6_8_standard_P_descending), but transported to a branch region of a NON-standard
    monoT slice of M.
- **Plan:** restate B2 to carry the SkT_PS/ST_PS hypothesis (M standard), prove the
  "tie ⟹ nextrel1 N joffR joffL" core (the row-1 parent derivation), likely reusing
  prop2's admissibility machinery; then B3 assembly closes the d0pos sorry. python:
  d1pos_b2_std.py (standard 373/0), d1pos_b2_audit.py (T_PS false), d1pos_b2_hyp.py.

## UPDATE 2026-05-29 (continued 30): the nextrel1 route is FALSE; B2 = `nlocal_adj_tie` (clean) + structural facts

The continued-29 `nextrel1 N joffR joffL` reduction is **EMPIRICALLY FALSE** (workflow
wzz3gc4gj, agent B2b): holds at len4/val2 (36/36) but FAILS at len5/val2 — only 185/373,
and in 217/373 `joffR > joffL` (joffR is to the RIGHT, not the row-1 parent). Refuted.

### The TRUE decomposition (python/d1pos_b2_local.py, all 0-fail)
For the d1pos branch region `Yp = seg M' (TrMax M'+1)(Lng M'-1)`, over the row-0 **tie**
pairs of consecutive P-components (J-1, J):
- **(S-adj)** the two components are M-adjacent: `pR = pL+1`  (373/373)
- **(S-sgl)** the LEFT component is a singleton: `Lng (P Yp!(J-1)) = 1`  (373/373)
- These are NOT general P facts (fail on arbitrary multiT Q, e.g. Q=(0,0)(1,0)(0,0):
  left Lng=2, non-adjacent) — they need the *branch-region-of-a-monoT-slice-of-standard-M*
  context (python/d1pos_b2_struct_general.py).

Because **M is standard** (`M ∈ SkT_PS k` in the prop1 induction) and `Yp` is a contiguous
segment of M (`Yp = seg M (j0'+TrMax M'+1) j1'`), a tie pair sits at **adjacent absolute
M-indices**. So B2's row-1 conclusion (`entry(P Yp!J) 1 0 ≤ entry(P Yp!(J-1)) 1 0`) reduces,
via (S-adj)+(S-sgl), to applying to standard M the **N-local adjacent-tie lemma**:

### `nlocal_adj_tie` — the real irreducible core (TRUE, 604/0 at len6/val2)
> `N ∈ SkT_PS k ⟹ Suc j < Lng N ⟹ entry N 0 j = entry N 0 (Suc j) ⟹ entry N 1 (Suc j) ≤ entry N 1 j`

Clean **k-induction** (mirrors `SkT_P_descending`), full skeleton (all cases closed by hand):
- **k=0** (`N = diagSeq u v`): row-0 strictly increasing ⇒ no adjacent ties ⇒ vacuous.
- **Suc k**, `N = M'[n]`, `M' ∈ SkT_PS k` (use `poper_oper_expand`; note `d1 = 0` always
  since `i1 = idx1 ∈ {0,1}` and `d1 = (if 1<i1 ..)`; and `d0 = 0` when `i1=0`):
  - degenerate oper (`= Pred M' = butlast M'`): adjacent ties = ties in M' ⇒ IH.
  - block form `take j0 M' @ concat(map blocks [0..<n])`, `w = j1-j0`, `j1 = Lng M'-1`:
    - **prefix ∪ block-0** (= first `j1` elements of M', unshifted): adjacent tie maps to
      an adjacent tie in M' ⇒ **IH on M'**.
    - **within block copy k**: cells map to M'-indices `j0+t, j0+t+1`, row-0 shifted by
      `k*d0` uniformly, row-1 by `k*d1=0`; tie ⇒ M'-tie at `(j0+t, j0+t+1)` ⇒ **IH**.
    - **block boundary** (copy k → k+1; left = M' `j1-1` +k, right = M' `j0` +(k+1)):
      tie ⇒ `entry M' 0 (j1-1) = entry M' 0 j0 + d0`.
      - **i1=1**: `d0 = entry M' 0 j1 - entry M' 0 j0` ⇒ `entry M' 0 (j1-1) = entry M' 0 j1`
        = an adjacent M'-tie at `(j1-1, j1)` ⇒ IH gives `entry M' 1 j1 ≤ entry M' 1 (j1-1)`;
        `j0 = ` nextrel1-parent of `j1` ⇒ `entry M' 1 j0 < entry M' 1 j1` (nextrel1_def);
        chain ⇒ `entry M' 1 j0 ≤ entry M' 1 (j1-1)` = the goal (d1=0). ✓
      - **i1=0**: `d0=0`; `j0 = ` nextrel0-parent of `j1` ⇒ `entry M' 0 (j1-1) ≥ entry M' 0 j1
        > entry M' 0 j0` (w≥2), contradicting the tie ⇒ **vacuous**; `w=1` ⇒ both map to `j0`
        ⇒ equal ⇒ goal holds with equality. ✓

### Closure = 3 bricks (B1 GREEN)
- **B1 oper_d1pos_Br_comp_mono** — GREEN (merged, slice 7d5cb06).
- **NEW core: `nlocal_adj_tie`** — the clean k-induction above; needs **general** oper
  entry-in-block lemmas (generalize oper_d1pos_entry0/entry1/nth/LngM off the d1pos-only
  hyps to the `poper_oper_expand` block form, or prove fresh `oper_entry_block`).
- **B2' reduction** = (S-adj)+(S-sgl) on Yp ⇒ adjacent M-tie ⇒ `nlocal_adj_tie` on M.
  (S-adj/S-sgl) are the remaining context-dependent structural facts to establish for Yp;
  alternatively look for a P-of-segment-of-standard route via `SkT_P_descending` on M.
- **B3 assembly** (EASY): descendingI_cdom + cdom_trans + row-0 free (m_6_4_P_leftend_mono)
  + the row-1 tie via B2'.

python: d1pos_b2_local.py (S-adj/S-sgl/M-loc/N-loc all 0-fail), d1pos_b2_struct_general.py
(S-adj/S-sgl context-dependent, not general P).

## UPDATE 2026-05-29 (continued 31): (S-adj)/(S-sgl) is FALSE; §6.8 collapses to ONE core `slice_P_tiebreak`

⚠️ **The continued-30 reduction (S-adj)+(S-sgl)+`nlocal_adj_tie` is REFUTED.** The
continued-30 `python/d1pos_b2_local.py` "373/373 0-fail" was a **sampling artifact of a
too-narrow generator** (it only folded standard d1pos `N` at one level; it never produced
the failing slices). With a proper rank-stratified standard generator (`nlocal_verify2/3.py`,
diagSeq→oper→SkT_PS), (S-adj)/(S-sgl) **FAIL 16/94** on the d0pos domain.

Counterexample (yaBMS-standard) `M' = (0,0)(1,1)(2,0)(1,1)(2,0)(1,0)`, `TrMax M'=1`,
`Yp = (2,0)(1,1)(2,0)(1,0)`, `P Yp = [(2,0)],[(1,1)(2,0)],[(1,0)]`, `IdxSum=[0,1,3,4]`.
The row-0 tie is between comp J=1 head `(1,1)` and J=2 head `(1,0)`: the left comp has
**Lng 2** (S-sgl false) and `pR=pL+2` (S-adj false). Worse, the tie is **non-local** — the
intermediate index between the two tied cut-heads has a strictly larger row-0 (a "dip"), so
there is **no chain of adjacent row-0 ties**, and the adjacent-only `nlocal_adj_tie` can
NEVER bridge it. So `nlocal_adj_tie` (though TRUE and now GREEN) is structurally
insufficient for the tie-break. (Lesson: a narrow empirical sweep gives false confidence —
always use the rank-stratified standard generator. This is the THIRD refuted B2 route.)

### The real, clean core — `slice_P_tiebreak` (verified 237/0 at len7/val3, 487/0 at len8/val4)
> `M ∈ SkT_PS k ⟹ a≤b ⟹ b≤Lng M-1 ⟹ J0≤J1 ⟹ J1≤Lng(P(seg M a b))-1 ⟹`
> `entry(P(seg M a b)!J0) 0 0 = entry(...!J1) 0 0 ⟹ entry(...!J1) 1 0 ≤ entry(...!J0) 1 0`

This is the row-1 tie-break of the P-decomposition of ANY slice of a standard form — exactly
the article's `slice_P_descending` core (content.md 1450–1615). Via `m_6_7_standard_prefix`
+ `seg_to_last_eq_drop` it equals **the drop-core** `N∈ST_PS ⟹ descending(P(drop j N))`,
which is *the same core* that the already-green `m_6_8_standard_slice_Br_descending_of_drop`
(pss_mechanized.thy ~8050) and `slice_P_descending_of_drop` (~8026) assume.

### State after this update (slice-wip-68 commit 9177499, GREEN)
- All 5 cases of `m_6_8_slice_Br_descending_monoT` (base/caseA/B/C/d0pos) now CLOSED
  **modulo the single `slice_P_tiebreak` stub** (agent-B B3 assembly replaced the d0pos sorry).
- agent-A merged: general i1-agnostic oper helpers `oper_gen_block_nth/entry0/entry1`,
  `oper_gen_nth_prefix` (off `poper_oper_expand`+`nth_concat_map_const_len`) + `nlocal_adj_tie`
  (real proof, GREEN — kept; the helpers are reusable, nlocal may feed the core's adjacent
  sub-cases).
- **§6.8 prop1 now hinges on exactly ONE lemma**: `slice_P_tiebreak` ⟺ the drop-core. Proving
  it discharges BOTH route 2 (`m_6_8_slice_Br_descending_monoT`) AND route 1 (the `_of_drop`
  assembly). This is the genuine §6.8 hard core; next step = its k-induction over `oper`
  (study SkT_P_descending's standard-form induction + the article 1450–1615).

python: nlocal_verify.py (nlocal_adj_tie 74/74), nlocal_verify2.py (S-adj/S-sgl 16/94 FAIL +
descending(Br M') 805/805), nlocal_verify3.py (slice_P_tiebreak C1 237/0..487/0),
nlocal_verify4.py (drop-head NOT global left-min, 175/316). ⚠️ d1pos_b2_local.py is UNRELIABLE
(narrow generator — do not trust its 0-fail claims).

## UPDATE 2026-05-29 (continued 32): ROUTE DECISION — article-faithful direct d0pos (route 2)

User chose the **article-faithful direct route** for the §6.8 hard core: close the d0pos
case of `m_6_8_slice_Br_descending_monoT` by transcribing the article's content.md d0pos
(i1=1) case analysis (using the IH on a slice of `N`), making the `slice_P_tiebreak`
stub UNNECESSARY (it/`m_6_8_standard_slice_Br_descending_of_drop`/the drop-core route are
NOT pursued). The agent-B B3 assembly + `slice_P_tiebreak` stub remain ONLY as the current
green checkpoint (slice-wip-68 9177499); they get REPLACED by the direct proof.

### Why the i1=1 fold P-structure differs from d0zero (the crux)
For i1=1, `d0 = δ > 0`: block k starts with row-0 `entry M 0 j0 + k·δ`, which is LARGER
than block 0's start. So a delta-shifted block boundary is NOT a global row-0 left-min, and
**P does NOT split at block boundaries** (this is why the naive `oper_d1pos_seg_P_split` is
FALSE — refuted long ago). The article therefore does a regime/sub-case analysis instead of
a uniform split. The existing d0zero helpers `oper_d0zero_seg_P_blk0fold/_split/_blk1fold/
_hfold` (10733–11126) are the i1=0 templates; their i1=1 (delta-shifted) analogues must be
built (these are the "blk0fold/split/hfold do NOT yet exist" pieces in the d0pos docstring).

### Article d0pos (i1=1) proof map (content.md, faithful)
Setup: `M = N[n]`, `i1 = idx1 N (j1^N) = 1`; if no row-1 parent `j_{-2}^N = parent N 1 (j1^N)`
then `M = Pred N` (done). Else `δ = N_{0,j1^N} − N_{0,j_{-2}^N} > 0`, fold blocks
`IncrFirst^{kδ}((N_j)_{j=j_{-2}^N}^{j1^N})`. First establish the block chain
`(0,j_{-2}^N) ≤_M (0,j1)` (have: `oper_d1pos_block_chain`, `oper_d1pos_le0_blockstarts`).
Then:
- **Regime A — `j'_0 < j_{-2}^N`** (if `j'_1 ≤ j_{-2}^N`: slice is in `N`, IH on N; else
  `j'_0 < j_{-2}^N < j'_1`): derive `(0,j'_0) ≤_N (0,j1^N)` ⇒ IH gives `N'` monoT +
  `descending(Br N')`, `N' = seg N j'_0 (Lng N−1)`. Sub-cases:
  - `J_1 = −1` (`j_{-2}^N=j_0^N=j1^N−1`, `j'_1=j_1`): `Br M'` = one block, `Lng=1`, descending.
  - `J_1 ≥ 0`, `TrMax(N') < j1^N−j'_0`, with `j_{-3} = ` row-0 parent of `j_{-2}^N−j'_0` in N':
    - `j_{-2}^N−j'_0 ≤ TrMax(N')`: `Br M' = (Br N')[0..J_1−1] @ [seg M (j_{-1}+j'_0) j'_1]`,
      `j_{-1}=FirstNodes(N')_{J_1}`; head `M_{j_{-1}} = N_{j_{-1}} = (Br N'_{J_1})_0`. desc.
    - `j_{-3} ≤ TrMax(N') < j_{-2}^N−j'_0`: `FirstNodes(N')_{J_1} = j_{-2}^N−j'_0`,
      `Br M' = (Br N')[0..J_1−1] @ repeated-blocks @ tail`; head `N_{j_{-2}^N}=(Br N'_{J_1})_0`. desc.
    - `TrMax(N') < j_{-3}`: `Br M' = (Br N')[0..J_1−1] @ [seg M ... j'_1]`; head=`N_..=(Br N'_{J_1})_0`. desc.
- **Regime B — `j_{-2}^N ≤ j'_0`**: divide `j'_0−j_{-2}^N` by `w=j1^N−j_{-2}^N`, period-reduce to
  `q=0` (have: `oper_d1pos_seg_period_reduce`). Then:
  - `j'_1 < j1^N`: `(M_j)_{0..j1^N−1}=Pred N` ⇒ slice in N ⇒ IH on N. desc.
  - `j'_1 ≥ j1^N`: `(0,j'_0) ≤_N (0,j1^N)` ⇒ IH gives `N'` monoT + `descending(Br N')`. Sub-cases:
    - `j1^N−j'_0 ≤ TrMax(N')`: `j_{-2}^N=j_0^N=j1^N−1`, `j'_0=j_0^N`; `Br M'`=one block. desc.
    - `j_0^N−j'_0 ≤ TrMax(N') < j1^N−j'_0`: `FirstNodes(N')_{J_1}=j1^N−j'_0`,
      `Br M'=(Br N')[0..J_1−1] @ [seg M j1^N j_1]`; **THE row-1 tie-break case**: head row-0
      `M_{0,j1^N}=N_{0,j1^N}=(Br N'_{J_1})_{0,0}` (TIE) while row-1
      `M_{1,j1^N}=N_{1,j_{-2}^N} < N_{1,j1^N}=(Br N'_{J_1})_{1,0}` (strict drop). desc.
    - `TrMax(N') < j_0^N−j'_0`: `Br M'=(Br N')[0..J_1−1] @ [seg M (j_{-1}+j'_0) j_1]`;
      head=`N_..=(Br N'_{J_1})_0`. desc.

### Build order (each empirically pin the actual i1=1 P-decomposition FIRST, then prove)
1. i1=1 fold P-decomposition helpers (delta-shifted analogues of the d0zero `_blk0fold/
   _split/_blk1fold/_hfold`) — the foundational missing pieces. Reuse agent-A's i1-agnostic
   `oper_gen_block_*` + existing `oper_d1pos_*` (block_chain, le0_blockstarts, seg_period_reduce,
   seg_mono=H1, Br_comp_mono=B1).
2. Block chain `(0,j_{-2}^N) ≤_M (0,j_1)` + regime split (j'_0 vs j_{-2}^N).
3. Regime A sub-cases; Regime B sub-cases (incl. the row-1 tie-break sub-case).
Then remove the slice_P_tiebreak stub + B3 assembly, replace with the direct proof.

## UPDATE 2026-05-29 (continued 33): d0pos collapses to the ¬brle multi-component remainder

Two parallel agents (workflow w01qu1rhv) on the article-direct route produced the decisive
reconciliation (python/d1pos_Br_singleton_check.py, rank-stratified std generator, 149
witnesses):

- **`brle` := (TrMax M' = Lng M'−1 ∨ le0 M' (TrMax M'+1)(Lng M'−1)) holds IFF Br M' is a
  SINGLE P-component** — `#Br M'` distribution {1: 137, 2: 12}, and brle ok/no = 137/12
  (exact match). The delta-shifted i1=1 block boundaries are not row-0 left-minima, so when
  brle holds the whole branch region Yp is monoT ⇒ `P Yp = [Yp]` ⇒ descending is trivial.
- agent-A green lemmas (merged, slice bdc0a84): `monoT_seg_of_le0` (le0 M a b, a<b ⇒
  monoT(seg M a b) — the a-free, oper-hyp-free generalization of oper_d1pos_seg_mono) and
  `descending_Br_of_branch_le0` (brle ⇒ descending(Br M'), single-component).
- The d0pos closure now case-splits on brle: **brle (137/149) is FULLY PROVEN**; the
  over-general `slice_P_tiebreak` stub is REMOVED. Only **¬brle (12/149, multi-component)**
  remains as a narrow inline residual sorry.

### The remaining piece — ¬brle (Yp multiT, Br M' multi-component)
This is the article regime A/B decomposition `Br M' = (Br N')[0..J₁−1] @ [tail]` with the
junction row-1 tie-break (D3 = 132/132): prefix descends by IHk on N-slices, junction is a
row-0 tie with row-1 weakly decreasing (article: `N_{1,j_{-2}^N} < N_{1,j1^N}`), tail is one
component. This is the genuine last d0pos brick. NOTE the earlier "agent A says Yp always
single (5548/5548)" was over a brle-restricted sub-family; the true picture is the {1:137,
2:12} split above (verify with the rank-stratified generator, never a narrow one-level one).

## UPDATE 2026-05-29 (continued 34): d0pos ¬brle = full article regime A+B (delta-shift); 3 bricks banked

Depth correction: the ¬brle MULTI case is NOT all regime B (KMAX=4 gave 12/12 B — a shallow
artifact). On KMAX=5 the 149 ¬brle-multi witnesses split **57 regime A / 92 regime B**; within
B, 80 reach the next block boundary, 12 do not. And the prefix is NOT raw-equal to Br N′ — it
is the **row-0 +k·δ IncrFirst shift** of `take J₁ (Br N′)` (raw equality fails 3/12 even
shallow). So ¬brle = the FULL article regime A+B with the delta-shift ≈ a port of the d0zero
caseC (lines ~12128/13271/12681–13146) PLUS novel funpow-IncrFirst-oper machinery.

### 3 reusable green bricks banked (slice 5c1f990)
- `descending_map_IncrFirst` — descending invariant under componentwise IncrFirst.
- `descending_shift_append` — descending Q + a +c-row-0-shifted PRE (len Lng Q−1) + junction
  TL (row-0 = last+c, row-1 ≤ last) ⇒ descending(PRE@[TL]). The regime-B head assembly.
- `oper_d1pos_notbrle_P_split` — P Yp = P(seg Yp 0 (c−1)) @ [tail] at a row-0 left-min anchor
  c, ¬multiT tail (tail may be a zeroT singleton, not always monoT).

### Precise remaining reduction (agent-verified 204/204), for `descending(LOW)`, LOW = P(seg Yp 0 (c−1))
With jm2 = parent N 1 (Lng N−1), w = j1N−jm2, δ = N₀,j1N − N₀,jm2, q = (j0′−jm2) div w,
j0red = jm2 + (j0′−jm2) mod w, Np = seg N j0red (Lng N−1), fnM = j0′+FirstNodes(M′)!J₁:
- (a) **LOW source identity**: `seg M j0′ (fnM−1) = IncrFirst^{q·δ}(seg N j0red (j0red+(fnM−1−j0′)))`
  — needs NEW funpow-IncrFirst-oper block-read (no `funpow IncrFirst` lemma exists yet).
- (b) **P–shift commute**: `P(IncrFirst^s X) = map (IncrFirst^s) (P X)` — funpow-iterate the
  existing `m_6_2_P_IncrFirst` (small).
- (c) `LOW = map (IncrFirst^{q·δ}) (take J₁ (Br Np))` — from (a)+(b)+`oper_d1pos_seg_period_reduce`.
- (d) `descending (take J₁ (Br Np))` — `descending_take[OF IHk Np …]` (IHk on N at rank k = ALLOWED).
- (e) `descending LOW` — `descending_map_IncrFirst` (GREEN) on (c)+(d).
Junction: row-0 tie via `oper_d1pos_entry0` (+q·δ both sides), row-1 drop via
`nextrel1 N jm2 j1N` (entry N 1 jm2 < entry N 1 j1N). Then `descending_shift_append` (GREEN).
Next build target = (a)+(b)+(c) (the funpow-IncrFirst LOW-identity machinery); then the
regime A/B assembly wires (d)+(e)+junction.

## UPDATE 2026-05-30 (continued 35): ¬brle is NOT vacuous (agent-B reshaping rejected); LOW machinery banked

⚠️ Agent B (LOW workflow) reshaped the ¬brle residual to a single `brYp_single`
(le0 M' (TrMax+1)(Lng-1)) claiming the ¬brle case is VACUOUS in the d0pos-branch context
(notbrle=0 over 30309 slices). **This is FALSE — a shallow-generator artifact (the THIRD
such).** With the EXACT residual context (incl. `bge: Lng N-1 ≤ j1'`) and a deeper sweep
(python/d1pos_residual_vacuity.py, len8/val3/KMAX5): **¬brle = 18/183 in context** — NOT
vacuous. `brYp_single` would be a FALSE stub. Concrete: N=(0,0)(1,1)(1,1)(1,1), n=2,
j0'=0, j1'=3 (bge: 3≤3 ✓): M'=(0,0)(1,1)(1,1)(1,0), Br M' has 2 components, brle false.
(Note: the bge constraint DOES filter some — 6 of the 24 no-bge ¬brle cases are jsmall,
IH-handled — but 18 genuinely reach the residual.) The agent-B brYp_single reshaping was
REJECTED; the ¬brle residual sorry is kept unchanged.

LESSON (now 3×): agents keep reporting false "vacuous/always-single/all-regime-B" from
shallow generators. ALWAYS re-verify simplicity claims with the deep rank-stratified
generator AND the exact in-context hypotheses before trusting.

### All bricks for the regime A+B assembly now exist (slice f0a51e8, green)
- `oper_d1pos_notbrle_P_split`: Br M' = LOW @ [tail] (LOW = P(seg Yp 0 (c-1)), c the
  last-component anchor; tail = single ¬multiT component).
- LOW machinery (a)(b)(c): `P_funpow_IncrFirst`, `oper_d1pos_LOW_source_eq`,
  `oper_d1pos_notbrle_LOW_eq` (LOW = map(IncrFirst^{qδ}) of the N-side P-slice).
- `descending_map_IncrFirst`, `descending_shift_append`, `descending_Br_of_branch_le0`,
  `monoT_seg_of_le0`, `descending_take`, `descending_append`, IHk on N.

### Remaining = the assembly WIRING (the FirstNodes/Br/TrMax bookkeeping)
Connect `oper_d1pos_notbrle_LOW_eq`'s P(seg M (j0+s0)(j0+e0)) to `take J1 (Br Np)` (Np = the
N-side reference slice), so LOW = map(IncrFirst^{qδ})(take J1 (Br Np)); then descending(LOW)
= descending_map_IncrFirst on descending_take[OF IHk]; junction via descending_shift_append
(row-0 tie after +qδ shift, row-1 drop via nextrel1 N jm2 j1N). This identification (the c =
FirstNodes anchor + the N-side Br/TrMax bookkeeping) is the last piece — both agents punted
on it (agent B via the false vacuity). python/d1pos_residual_vacuity.py + notbrle_low_check.py.

## UPDATE 2026-05-30 (continued 36): ¬brle descending assembly GREEN; residual = the existential identification

The wiring workflow (wcwc0hnf3) closed the ¬brle descending-assembly half (slice 15998e6,
green). The inline ¬brle sorry is REMOVED; the d0pos case now reduces to ONE existential stub.

- **Assembly (PROVEN)**: regime A (18) + regime B (12) close uniformly via
  `descending_shift_append`: obtain (j0red, shamt, LOW, tail) from the stub; descending(Br Np)
  via IHk on N (Np = seg N j0red (Lng N-1)); descending_shift_append wires LOW @ [tail].
- **The single residual** = `oper_d1pos_notbrle_LOW_take_eq` (existential): for the ¬brle
  d0pos slice, ∃ j0red shamt LOW tail with Br M' = LOW @ [tail], LOW the +shamt-IncrFirst-shift
  of `take (len-1) (Br Np)` and the junction tail facts. Empirically 30/30 in residual context.
- **Anchor correction** (deep gen, the warned class, caught): anchor on Jm = length(Br M')−1,
  NOT J1 = Lng(Br Np)−1 (refuted 3/150 — Br M' is generally SHORTER, last comp a truncation).
- **TrEq holds in context**: TrMax M' = TrMax Np is TRUE 681/681 in the PRECISE regime-B ¬brle
  residual context (my earlier "TrEq false for d1pos" warning was for a broader regime). So the
  d0zero caseC TrEq-based block-fold/first-node bookkeeping (~12084-13271) DOES port here.
- Banked helper: `oper_d1pos_notbrle_take_map` (agent-A combinator, P_funpow_IncrFirst-based).

### Remaining = prove the existential stub (the last d0pos piece)
Provide the witnesses (j0red via period-reduction, shamt = q·δ, LOW/tail from
`oper_d1pos_notbrle_P_split`) and discharge the facts using TrEq (provable) + the d0zero caseC
FirstNodes/Br/TrMax bookkeeping + `oper_d1pos_notbrle_take_map`/LOW machinery. python:
notbrle_low_take_check.py (anchor 681/681), d1pos_notbrle_wire.py (full fact set 30/30),
d1pos_residual_vacuity.py (¬brle 18/183 non-vacuous).

## UPDATE 2026-05-30 (continued 37): the identification stub was FALSE (Lng N-1 endpoint); fixed to free j1red

The stub-proof workflow (wzvkg801x) split: agent B reported "green" (30/30 at KMAX=5) but
agent A (KMAX=7) REFUTED the stub as stated. **Independently confirmed (python/
d1pos_stub_endpoint.py, KMAX=6, len10/val4)**: the committed stub
`oper_d1pos_notbrle_LOW_take_eq` hardcoded the N-side reference endpoint as `Lng N-1`
(Np = seg N j0red (Lng N-1)), and `length(Br M') = Lng(Br Np)` **FAILS 36/207 at rank 6**
(when the d0pos slice ends strictly INSIDE a block, Br M' is shorter than Br of the
full-length Np). Minimal witness: N=(0,0)(1,1)(2,0)(1,1)(1,1), n=2, j0'=4, j1'=7
(len(Br M')=2 but Lng(Br(seg N 0 4))=3). **This was the 4th shallow-generator false
claim** (agent B's KMAX=5 had 0 fails — the refutation only appears at rank≥6).

**FIX (deep-verified 207/207)**: generalize the N-side endpoint from `Lng N-1` to a FREE
`j1red` with `j0red < j1red ≤ Lng N-1` and `le0 N j0red j1red`, so `Np = seg N j0red j1red`.
With the free endpoint the existential identification holds 207/207. The ¬brle assembly's
IHk application still works (IHk is ∀ slices with j1red < Lng N). Both the stub statement
and the assembly's `obtain`/`?Np`/IHk were corrected (slice 4965840, green). The stub is now
a TRUE sorry (dischargeable); proving it (the block-fold + first-node geometry with the free
endpoint + TrEq, which holds 1912/1912) is the final d0pos piece. python/d1pos_stub_endpoint.py.

⚠️ LESSON (now 4×): EVERY simplicity/length/vacuity claim from a sub-agent MUST be re-checked
at rank≥6-7 with the exact in-context hypotheses before trusting; KMAX=5 is too shallow for
the d0pos fold.

## UPDATE 2026-05-30 (continued 38): witness PINNED (formula G); the stub proof = the ~1000-line d0zero-caseC port for d1pos

Both independent attempts at the corrected free-endpoint stub BLOCKED — but together they
PIN the witness and EXPOSE the true scope.

### Witness = formula G (deep-verified, independently reconfirmed 207/207 at KMAX6/len11/val4)
With jm2=parent N 1 (Lng N-1), w=Lng N-1-jm2, delta=entry N 0 (Lng N-1)-entry N 0 jm2,
q=(j0'-jm2) div w:
- `j0red = (jm2 ≤ j0' ? jm2 + (j0'-jm2) mod w : j0')`,  `shamt = q*delta`
- `j1red = min (j0red + (j1'-j0')) (Lng N-1)`   ← **the MIN-CAP is essential** (uncapped
  `j0red+(j1'-j0')` is FALSE 436/1083; agent B missed the cap and wrongly concluded "no
  closed form"; agent A's formula G with the cap is 1083/1083 at KMAX7, and I reconfirm
  bound/le0/TrEq/length all 207/207 at KMAX6).
- `LOW = butlast (Br M')`,  `tail = last (Br M')`.
- TrEq `TrMax M' = TrMax (seg N j0red j1red)` holds at this j1red (207/207, 1083/1083).

### True scope: the stub PROOF is the genuine §6.8 d0pos heart (~1000 lines)
The existential is TRUE with formula G, but proving it constructively needs the
**delta-shifted block-fold machinery** — the i1=1 analogues of `oper_d0zero_seg_P_blk0fold/
_split/_blk1fold/_hfold` (lines ~10733-11126) PLUS a d1pos TrEq brick PLUS the FirstNodes/
Br/IdxSum identification — i.e. essentially the entire GREEN d0zero caseC closure (~12084-
13271, ~1000+ lines) re-derived for the delta-shifted fold, with an added min-cap case split.
This is NOT a single self-contained lemma; it is a multi-session infrastructure build.

### Status summary (§6.8 prop1)
- ✅ brle (single-component branch) — fully proven.
- ✅ ¬brle descending ASSEMBLY (regime A+B, descending_shift_append) — proven modulo the stub.
- ✅ surrounding bricks green: LOW machinery, descending_map_IncrFirst, descending_shift_append,
  oper_d1pos_notbrle_P_split, oper_d1pos_notbrle_take_map, monoT_seg_of_le0, nlocal_adj_tie,
  d0pos Z1-Z7/H1/B1.
- 🚨 the ONE residual = oper_d1pos_notbrle_LOW_take_eq (TRUE, witness=formula G PINNED) — its
  proof = the delta-shifted block-fold machinery (the next major effort).
- 4 shallow-generator false claims caught this push; ALWAYS verify at rank≥6.

## UPDATE 2026-05-30 (continued 39): block-fold brick 1 = d1pos TrEq keystone (uncapped, conditional)

The block-fold infrastructure build began. BRICK 1 banked (slice 8c779b8, green):
`TrMax_seg_oper_d1pos_eq` — TrMax(seg (N[n]) j0' j1') = TrMax(seg N j0red j1red) via the
IncrFirst-invariance route (TrMax_funpow_IncrFirst + oper_d1pos_nth in-block agreement +
TrMax_eq_of_prefix_agree). Both independent attempts CONVERGED (deep gen, NO shallow-false
this round): the keystone is FALSE without notbrle (A 1833 / B 15 counterexamples, all brle)
and TRUE under notbrle (22431/22431). Good sign the brick-by-brick build is converging.

### Brick map (the remaining ~1000-line block-fold port, sub-cases identified)
- **Brick 1a (DONE)**: TrEq for the UNCAPPED case (span `j1red = j0red+(j1'-j0')`, j1red≤Lng N-1),
  CONDITIONAL on `tnc` (TrMax Nred ≤ j1red-1-j0red) + `stop` (boundary stop). 0 sorries.
- **Brick 1b**: TrEq for the CAPPED across-block case (j1red = Lng N-1 < j0red+(j1'-j0'));
  the harder sub-case (deep-verified tnc/stop hold 15246, but the keystone's `span` hyp is
  uncapped — needs a capped variant / generalized span).
- **Brick 2**: discharge `tnc` + `stop` from notbrle (the trunk-confinement — ¬brle forces the
  M'-trunk strictly below the block-q boundary; `TrMax M' < c` ⟺ the boundary row-1 step
  nextrel1 fails because the next block restarts row-1 from the unshifted block-start; both
  attempts deep-verified 2206/2206 strict). The block-fold row-1 chain-break structure.
- **Brick 3**: the Br = LOW @ [tail] decomposition with LOW = (IncrFirst^^shamt)-shift of
  take (Lng(Br Np)-1) (Br Np) — the FirstNodes/Br/IdxSum alignment (uses TrEq to line up
  BrM'P=P(seg M a j1') and BrNpP=P(seg N a' j1red); oper_d1pos_notbrle_LOW_eq + take_map).
- **Brick 4**: the junction facts (tail row-0 tie after shift, row-1 drop via nextrel1 N jm2).
Then assemble the stub oper_d1pos_notbrle_LOW_take_eq from bricks 1-4 + formula-G witnesses.

## UPDATE 2026-05-30 (continued 40): trunk-confinement family DONE (sound); 6 shallow-false catches; Br-alignment remains

The block-fold infrastructure build advanced substantially. The TRUNK-CONFINEMENT family
(the keystone for the §6.8 d0pos ¬brle identification) is essentially complete and SOUND
(slice 3c76a84, green). Bricks landed:
- `TrMax_seg_oper_d1pos_eq` (TrEq keystone, conditional on tnc/stop) ✅
- `TrMax_eq_of_prefix_agree_sym` (symmetric companion, breaks d1pos circularity) ✅
- `TrMax_seg_oper_d1pos_eq_span` (capped-generalized) ✅
- `TrMax_seg_oper_d1pos_eq_notbrle_uncapped` (uncapped TrEq, notbrle-unconditional) ✅
- `TrMax_seg_oper_d1pos_brle_uncapped` (uncapped trunk-fill ⟹ brle) ✅
- `TrMax_seg_oper_d1pos_brle_capped` (capped trunk-fill ⟹ brle, modulo the B3N inline residual) ✅
- `oper_d1pos_seg_le0_boundary` + 4 reusable helpers (oper_d1pos_nextrel0_within / le0_within /
  le0_start_to_start / le0_start_to_any — block-(q+1) start row-0-reaches any in-range index,
  the k+1<n-free within-block le0 machinery) ✅

### 6 shallow-generator false-claims caught this push (the discipline that saved soundness)
Each appeared only at progressively DEEPER ranks; the verifier (me) re-checked every sub-agent
simplicity/length/vacuity claim at rank≥6-8 before integrating:
1. agent A "Yp always single P-component 5548/5548" — brle-restricted sub-family.
2. agent B "¬brle multi all regime B / 12 cases" — KMAX=4 artifact (really 57 A / 92 B).
3. agent B "¬brle case vacuous (brYp_single)" — KMAX=4 artifact (really 18/183 in context).
4. agent B "stub take-eq 30/30 KMAX=5" — the N-side endpoint Lng N-1 is FALSE 36/207 at rank 6
   (fixed to the free j1red, 207/207).
5. agent B "general H2 increment bound 1016/1016 KMAX=7" — FALSE 6/4133 at rank 8.
6. agent A "last-column H2 191/191" — ALSO FALSE 10/11219 at rank 8 (this one had reached
   COMMITTED code; removed the false standalone H2 stub, replaced with the inline B3N residual
   true-in-context). LESSON: even KMAX=7 is too shallow for the d0pos fold; verify at rank≥8.

### Remaining for the §6.8 d0pos ¬brle stub
- **B3N** (inline residual in TrMax_seg_oper_d1pos_brle_capped): entry N 1 jm2 ≤ entry N 1 (Lng N-2),
  TRUE in the full capped ¬brle slice context (1688/1688) — needs the context-specific derivation
  (NOT the false H2 decomposition).
- **Brick 3** (Br = LOW @ [tail] alignment): with TrEq now available, line up BrM'P=P(seg M a j1')
  and BrNpP=P(seg N a' j1red), LOW = (IncrFirst^^shamt)-shift of take (Lng(Br Np)-1)(Br Np), via
  oper_d1pos_notbrle_LOW_eq + oper_d1pos_notbrle_take_map; the le0 helpers above feed it.
- **Brick 4** (junction): tail row-0 tie after shift, row-1 drop via nextrel1 N jm2.
Then assemble the main stub oper_d1pos_notbrle_LOW_take_eq from TrEq + B3N + bricks 3-4 + formula-G.

## UPDATE 2026-05-30 (continued 41): main stub is TRUE; reduces to 4 brick-families (across-block P-collapse = core)

Both independent attempts at the main identification stub oper_d1pos_notbrle_LOW_take_eq
CONVERGED (no shallow-false; both deep-verified the stub TRUE at rank≥8 with the free-j1red
formula-G witnesses: 1395/1395 at KMAX8/len12, 3276/3276 at KMAX8/len11/val5). So the stub is a
SOUND residual. Its proof, however, is the FULL remaining §6.8 d0pos multi-block fold
infrastructure — 4 brick-families, none green yet:

1. **Regime A keystone (267/1395 cases, j0'<jm2)** — ENTIRELY uncovered. Every existing d1pos
   TrEq/reshape/le0 brick hard-requires jm2≤j0' (regime B, via s0eq/j0'eq). A regime-A TrEq +
   reshape must be authored.
2. **¬brle-route Br_align for the CAPPED case (857/1395) + regime A** — oper_d1pos_notbrle_Br_align
   takes tnc/stop as HYPOTHESES (routes through the conditional keystone). The ¬brle keystones
   derive tnc/stop only for uncapped regime-B; a ¬brle Br_align supplying Br Np ≠ [] for capped /
   regime A is missing.
3. **THE ACROSS-BLOCK P-COLLAPSE (the CORE missing brick)**: the M'-branch region spans MULTIPLE
   blocks in 1047/1395 cases (up to 3), yet F7 holds with a UNIFORM shamt=q·δ because P collapses
   ALL across-block growth into the SINGLE non-multiT LAST component (tail); LOW=butlast lies
   entirely in block q (uniform in-block shift, where LOW_eq/take_map apply). Needs the d1pos
   analogues `oper_d1pos_seg_P_split/_hfold/_blk1fold/_blk0fold` (of the d0zero blk-fold family):
   P(branch) = map(IncrFirst^^shamt)(butlast(Br Np)) @ [collapsed monoT tail].
4. **F8/F9 tail tie/drop**: tail row-0=+shamt tie, row-1 drop via nextrel1 N jm2 (Lng N-1);
   partly present (oper_d1pos_seg_le0_boundary) but unassembled, absent for regime A.

### State (slice 346171b, green; SOUND — the one remaining sorry is a TRUE stub)
DONE & sound: trunk-confinement family (TrEq keystone/sym/span/uncapped+capped notbrle TrEq +
uncapped+capped trunk-fill⟹brle), B3N (oper_d1pos_b3n_boundary), le0-boundary + 4 le0 helpers,
Br_seg_reshape, oper_d1pos_notbrle_Br_align (skeleton), LOW machinery + take_map. The §6.8 d0pos
heart is now precisely: the across-block P-collapse (brick-family 3) + regime A (1) + the ¬brle
Br_align (2) + tail (4). This is a multi-session infra build (the d0zero blk-fold port for d1pos),
not a single lemma. python/d1pos_stub_full_G.py (1395/1395 rank-8 full-stub verification).

## UPDATE 2026-05-30 (continued 42): brick-families 1 + 3 DONE (collapse + regime A green, slice 1267715)

Two parallel deep-verified agents closed the two CORE brick-families; both integrated to
slice-wip-68 HEAD **1267715**, build green ("Finished PSS"), sorry count unchanged at 7 (both are
sorry-free structural/conditional lemmas — no false-stub risk).

1. **Brick-family 3 (the CORE across-block P-collapse) — `oper_d1pos_collapse`**: a *structural*
   identity, NOT empirical. For a branch region S∈T_PS with last row-0 left-min cut c
   (c0:0<c, cle:c≤Lng S−1, lmin:∀j<c. entry S 0 c ≤ entry S 0 j), single tail
   (tailnm:¬multiT(seg S c (Lng S−1))), LOW prefix a shift (lowshift: seg S 0 (c−1)=(IncrFirst^^shamt) base)
   and butl (butlast BN=P base): **P S = map(IncrFirst^^shamt)(butlast BN) @ [seg S c (Lng S−1)]**.
   Proof = additive split at c (oper_d1pos_notbrle_P_split) + P(seg S 0 (c−1))=P((IncrFirst^^shamt)base)
   =map(shift)(P base)=map(shift)(butlast BN) via P_funpow_IncrFirst. Cites only proven facts.
   The hypotheses (lowshift/butl/tailnm/lmin) are the per-regime discharge job (the final assembly).
   The d1pos collapse vs d0zero SPLIT: δ>0 shifts every block in row 0, so the boundaries are NOT
   row-0 left-minima — only ONE genuine left-min (the last anchor c) survives and the whole tail is
   one monoT component. Deep-verified 1395/1395 rank-8 (every hypothesis holds in context).

2. **Brick-family 1 (regime A keystone, j0'<jm2, q=0, shamt=0)** — 3 green lemmas:
   `oper_d1pos_nth_low_verbatim` ((N[n])!x=N!x for x<Lng N−1; the full-seg verbatim is FALSE at the
   boundary x=Lng N−1 — strict-prefix only, agent self-caught), `TrMax_seg_oper_d1pos_eq_regA`
   (regime-A TrEq via verbatim prefix-agreement + TrMax_eq_of_prefix_agree),
   `oper_d1pos_notbrle_Br_align_regA` (regime-A Br-align via Br_seg_reshape). Deep-verified
   2460/2460 rank-8. shamt=0 ⇒ IncrFirst^^0=id ⇒ LOW=butlast(Br Np) verbatim.

### Remaining: the FINAL ASSEMBLY (workflow wx8fo9kps running)
Wire the green bricks into `oper_d1pos_notbrle_LOW_take_eq`: obtain formula-G witnesses, discharge
oper_d1pos_collapse's hypotheses per regime (B via Br_align + LOW_source_eq + le0 helpers; A via the
regA bricks + shamt=0), read off Br M'=LOW@[tail], length LOW=Lng(Br Np)−1, the entry conjuncts via
entry_funpow_IncrFirst0 (row-0 +shamt) / entry_funpow_IncrFirst1 (row-1 unchanged), and the tail
junction (row-0 +shamt tie, row-1 drop via b3n + nextrel1). Brick-families 2 (¬brle Br_align capped)
and 4 (tail tie/drop) are absorbed into this assembly. After it closes: WLOG-monoT wrapper +
integrate §6.8 prop1 into main, merge slice-wip-68 → main.

## UPDATE 2026-05-30 (continued 43): FirstNodes-anchor identification GREEN — purely STRUCTURAL (slice 103aa05)

The documented "core gap" (the FirstNodes-anchor identification + the delta-shifted block-fold
family) turned out to need NO block-fold for the structural half. Two converging deep-verified agents
both found the concrete cut **c = IdxSum (P S) ! (length (P S) − 1)** (the last P-component's left
endpoint, = Lng S − Lng(last(P S))), and discharged the collapse hypotheses STRUCTURALLY:
- `oper_d1pos_branch_anchor` (GREEN): for S∈T_PS with 1<length(P S), this c gives 0<c, c≤Lng S−1,
  lmin (via idxsum_leftend_lmin at the last component), ¬multiT(seg S c (Lng S−1)) (via
  m_6_2_P_components_1: every P-component is zeroT∨monoT), plus seg S c (Lng S−1)=last(P S),
  c=Lng S−Lng(last(P S)). PURE idxsum geometry — no block-fold. Deep-verified 1395/1395 rank-8.
- `oper_d1pos_branch_collapse_concrete` (GREEN): anchor + oper_d1pos_collapse ⇒
  P S = map(IncrFirst^^shamt)(butlast BN) @ [last(P S)], given lowshift+butl.
- `oper_d1pos_branch_butl` (GREEN): butlast(P Snside)=P(seg Snside 0 (cN−1)) via the anchor split on
  the N side ⇒ base = seg Snside 0 (cN−1).
- `oper_d1pos_branch_lowshift_regB` (GREEN): lowshift for uncapped regime B (single-block A≥jm2,
  e0<w taken as hyps) via oper_d1pos_LOW_source_eq.

So the §6.8 d0pos remainder is now just: (a) the CONTEXT-level lowshift — derive the block
realization (regime B) / verbatim shamt=0 (regime A) so base = seg Snside 0 (cN−1); (b) the tail
junction F8 (entry last(P S) 0 0 = entry last(P Snside) 0 0 + shamt) / F9 (row-1 drop); (c) the final
existential assembly threading collapse_concrete + branch_butl + lowshift_ctx + tail + the entry
facts (entry_funpow_IncrFirst0/1) + le0 N j0red j1red + the Br reshapes. Workflow wzxdjxihh runs
(a)+(b). No block-fold family (oper_d1pos_seg_P_split/_hfold/...) is needed after all — the idxsum
anchor + the single-block source-eq cover it.

## UPDATE 2026-05-30 (continued 44): regime-A anchor coincidence c=cN + F8end/F9end GREEN; residual = clt/cNlt + regime-B shift (slice f3a5cd3)

The lowshift-ctx + tail-junction bricks landed (slice 4c2decb): oper_d1pos_seg_low_verbatim,
oper_d1pos_branch_lowshift_regA (regime A, shamt=0), oper_d1pos_branch_lowshift_regB_plug (base =
seg Snside 0 (cN−1)), oper_d1pos_anchor_tail_entry (entry(last(P S)) i 0 = entry S i c),
oper_d1pos_tail_junction (F8/F9 from F8end/F9end). Then the anchor-coincidence (slice f3a5cd3):
- **`P_butlast_take_at_anchor` (GREEN, reusable core)**: truncating S above its last anchor c
  preserves butlast(P S): butlast(P(seg S 0 (m−1))) = butlast(P S) for c<m≤Lng S. (FALSE at m=c.)
- **`notmulti_seg_prefix` (GREEN)**: a start-prefix of a non-multi T_PS seq is non-multi.
- **`oper_d1pos_anchor_coincide_regA` (GREEN)**: regime-A c=cN, F8end (shamt=0 tie), F9end — derived
  via the KEY CORRECTION that S and Snside are NOT element-wise verbatim (0/267) but agree on
  ALL-BUT-LAST [0,Lng Snside−2]; c=cN reduces to butlast(P S)=butlast(P Snside) via
  P_butlast_take_at_anchor on both. Residual: two deep-verified bounds clt:c<Lng Snside−1,
  cNlt:cN<Lng Snside−1 (the last branch component has length≥2; from the periodic tail having
  row-0 above the running min, no left-min at index≥m).

So the §6.8 d0pos stub is now reduced to: (regime A) discharge clt/cNlt → fully green + the regime-A
branch assembly; (regime B, jm2≤j0') the SHIFT analogue of anchor_coincide_regA — butlast(P S) =
map(IncrFirst^^shamt)(butlast(P Snside)) via P_butlast_take_at_anchor + the single-block shift
seg-eq (oper_d1pos_LOW_source_eq) + P_funpow_IncrFirst, then c=cN (Lng_funpow_IncrFirst preserves
lengths), baseEq, F8end (+shamt), F9end. Workflow wcy5tmj4j runs both. NB a verification-script bug
(IdxSum[−1]=Lng S vs the correct IdxSum[len−1]=last anchor) caused a spurious "regime-B multi-block /
c≠cN" false alarm — with the correct anchor, regime B is single-block 1128/1128.
