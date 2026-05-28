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
