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
