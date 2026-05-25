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

## Plan

1. ✅ design (this doc) + empirical reduction confirmed.
2. Prove the easy reusable helpers green: `descending_P_of_ST`,
   `branch_seg_T_PS`, the row-0 part of `descending (Br M')`.
3. Build `Br_oper_decomp` and the row-1 characterization; then the `k`-induction
   for the tie-break. (Largest remaining piece; may span sessions.)
4. Assemble `m_6_8_standard_slice_Br_descending`.
