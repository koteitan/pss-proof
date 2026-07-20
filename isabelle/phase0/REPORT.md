# Isabelle reorganization Phase 0 report

Date: 2026-07-20
Scope: dependency analysis only; no theory content was moved.

## Verdict

The reorganization is feasible as an incremental, green-gated relocation. The
project fact graph is acyclic, its existing append order is already a valid
dependency-first order, and the proposed 128 proposition-file graph is also
acyclic with no import from an earlier chapter to a later chapter.

The verdict by chapter is:

| Chapter | Proposition files | Proof association | Verdict | Estimated edit/build rounds |
| --- | ---: | --- | --- | ---: |
| §5 | 13 | 13 exact clean equivalents | GO for the pilot after approval | 2–3 |
| §6 | 55 | 54 exact, 1 named corrected/partial family | GO | 7–9 |
| §7 | 27 | 17 exact, 8 named corrected/partial families, 2 unmapped | Conditional GO after the one helper placement fix and two manual proof associations | 5–7 |
| §8 | 33 | 25 exact, 2 named corrected/partial families, 6 unmapped | Conditional GO after six manual proof associations | 10–14 |

These round counts are planning estimates for relocation plus Isabelle build
feedback, not measured per-file timings. No pilot work was performed in Phase 0.

## Build and audit baseline

After fast-forwarding `codex` to `main` at v0.2.0, the unmodified baseline was
built with:

```sh
isbman build -m pss-phase0-baseline -d . -v PSS_C
```

`PSS_A`, `PSS_B`, and `PSS_C` all finished successfully. `Finished PSS_C`
appeared once and the existing ML audit at the end of
`layerC/pss_scratch.thy` ran without `AUDIT FAILED`. The five existing project
theories and `ROOT` were not edited during this phase, so the current
0-sorry/0-hypothesis termination result and the audit block are unchanged.

## Extraction method and graph semantics

The raw export was produced in a disposable child session of `PSS_C`. Its
wrapper imported `PSS_C.pss_scratch` and loaded
[`extract_fact_dag.ML`](extract_fact_dag.ML). The extractor uses:

- `Global_Theory.dest_thm_names` for theorem identities and namespace metadata;
- `Thm_Deps.thm_deps` for proof-term dependencies;
- `Thm_Deps.has_skip_proof` for skip-proof metadata; and
- alpha-equivalence of `Thm.full_prop_of` for article-to-clean-proof candidates.

Thus source text is not used to infer dependency edges. Source locations are
used only to identify the top-level `lemma`, `theorem`, `corollary`, and
`proposition` commands and to assign chapter ownership. Dependencies through
generated facts or aliases are contracted rather than dropped.

The count normalization is:

| Stage | Count |
| --- | ---: |
| Raw Isabelle theorem identities | 6,612 |
| Raw fact-name groups before source filtering | 5,806 |
| Top-level declaration groups before resolving shadowing | 4,365 |
| Shadowed earlier declarations | 12 |
| Canonical top-level facts | 4,353 |
| Raw internal proof-term edges | 49,900 |
| Canonical internal edges after grouping/contraction | 15,283 |
| External Isabelle/HOL identity edges retained only in raw data | 506,517 |

An edge `A -> B` means that the proof of `A` uses `B`. The canonical graph has:

- 4,353 nodes and 15,283 internal edges;
- zero cyclic nodes;
- a complete 4,353-node dependency-first topological order; and
- zero edges that violate the existing theorem serial/append order.

The machine-readable order is in
[`topological_order.tsv`](data/topological_order.tsv), and the canonical edge
list is in [`dependencies.tsv`](data/dependencies.tsv).

## Helper partition

Of the 4,353 canonical facts, 3,571 are helpers whose short name does not begin
with `p_5`…`p_8` or `m_5`…`m_8`. Reachability was computed from every clean
`p_`/`m_` root, then combined with the 128 article-proof closures.

| Proposed physical bucket | Count | Rule |
| --- | ---: | --- |
| `PSS/cross-chapter` | 1,011 | Used by roots/propositions in at least two chapters |
| `PSS/compat-unreached` | 1,277 | Not reached from a selected article or `p_`/`m_` root; retain as a compatibility layer rather than silently delete frozen API |
| `5/` local/support | 1 | Used only by chapter 5 |
| `6/` local/support | 52 | Used only by chapter 6 |
| `7/` local/support | 93 | Used only by chapter 7 |
| `8/` local/support | 1,137 | Used only by chapter 8 |
| **Total shared `PSS/`** | **2,288** | Cross-chapter plus compatibility |
| **Total chapter-local** | **1,283** | Exactly one consumer chapter |
| **Total helpers** | **3,571** | |

The full per-fact decision, consumer chapters, dependency chapters, and earliest
availability frontier are in
[`helper_partition.tsv`](data/helper_partition.tsv).

The shared layer cannot be one monolithic theory. Its planned dependency-first
shape is:

```text
PSS/Defs + PSS/Pre_5
  -> §5 proposition/support frontier shards -> PSS/After_5
  -> §6 proposition/support frontier shards -> PSS/After_6
  -> §7 proposition/support frontier shards -> PSS/After_7
  -> §8 proposition/support frontier shards -> PSS/After_8 + PSS/Compat
```

The shared-helper availability counts are:

| Frontier | Cross-chapter | Compatibility |
| --- | ---: | ---: |
| Before §5 | 625 | 646 |
| After a §5 prerequisite | 63 | 73 |
| After a §6 prerequisite | 277 | 135 |
| After a §7 prerequisite | 46 | 119 |
| After a §8 prerequisite | 0 | 304 |

“After §N” is a dependency frontier, not necessarily the end of the whole
chapter. When a later proposition in the same chapter needs such a helper, the
helper must be exported by a fine-grained `PSS/Frontier_N_*` shard immediately
after its prerequisite proposition, then collected by `PSS/After_N`. A helper
used by multiple propositions of only one chapter belongs in that chapter's
`Support_*` shard; a helper used by only one proposition may remain in that
proposition file. This prevents a synthetic cycle while retaining the
one-article-proposition-per-file rule.

## Upper-triangular references

The supervisor's text probe produced 22 apparent upper-triangular references:
8 from §6 to §7 and 14 from §7 to §8. All 22 were checked against the contracted
`Thm_Deps.thm_deps` edge set. None is a proof dependency, so none requires a
later-chapter import or theorem relocation. Their common resolution is **T**:
retain the associated comment/annotation as appropriate, but discard the item
as a dependency-graph back-edge.

| # | Earlier fact | Later token mentioned | Resolution |
| ---: | --- | --- | --- |
| 1 | `m_6_5_Red_Pred` | `m_7_2_RightNodes_subexpr` | T |
| 2 | `m_6_5_Red_oper_final` | `m_7_2_scb_replaceable_corr_mod_image` | T |
| 3 | `m_6_6_Red_diag_prefix` | `m_7_2_scb_replaceable` | T |
| 4 | `m_6_6_Red_diag_prefix` | `m_7_2_scb_replaceable_corr` | T |
| 5 | `m_6_6_Red_diag_prefix` | `p_7_2_scb_replaceable` | T |
| 6 | `m_6_6_condAB_coeff` | `p_7_4_Adm_nextAdm` | T |
| 7 | `m_6_6_reduced_leftend` | `m_7_2_add_scb` | T |
| 8 | `m_6_8_standard_slice_Br_descending` | `m_7_1_term_components` | T |
| 9 | `m_7_1_lessBT_linord` | `m_8_7_OT_examples` | T |
| 10 | `p_7_1_term_components` | `m_8_7_toplevel_OT_tail_annihilate` | T |
| 11 | `m_7_2_add_scb_conj3` | `m_8_4_oper_Suc_append` | T |
| 12 | `m_7_2_add_scb_conj3` | `m_8_7_OT_dom_hereditary` | T |
| 13 | `m_7_2_add_scb_conj3_uncond` | `m_8_2_j0eq_Adm0` | T |
| 14 | `m_7_2_add_scb_conj3_uncond` | `m_8_2_j1eq_Adm0` | T |
| 15 | `m_7_2_add_scb_conj3_uncond` | `m_8_2_parent_le_TrMax_Adm0` | T |
| 16 | `m_7_2_add_scb_conj3_uncond` | `m_8_2_subexpr_component_Pred_Adm0` | T |
| 17 | `m_7_2_add_scb_conj3_uncond` | `m_8_2_subexpr_component_Pred_Adm0_clause1_keystone` | T |
| 18 | `m_7_2_scb_fseq_kind1_basic` | `m_8_2_subexpr_component_Pred_Adm0_clause4_core` | T |
| 19 | `m_7_2_scb_fseq_kind1_general` | `p_8_6_trailing_principal_annihilable` | T |
| 20 | `m_7_3_Mark_P_invariance` | `m_8_1_Pred_diagSeq_Trans` | T |
| 21 | `m_7_3_Trans_monoT` | `m_8_3_kind0_branch_rule` | T |
| 22 | `m_7_4_Mark_Trans_repr` | `m_8_1_c1_around_part1_noeq` | T |

The complete probe comparison is in
[`upper_back_edges.tsv`](data/upper_back_edges.tsv). The real named-section
proof-edge table, [`proof_upper_back_edges.tsv`](data/proof_upper_back_edges.tsv),
contains only its header because the real count is zero.

There is one different, helper-mediated placement issue that the section-name
probe could not see:

```text
pss_wip.Trans_two_zero                 chapter-7-local consumer
  -> pss_wip.m_8_7_cnst_Trans          later-named dependency
```

Resolution: during the §7 phase, relocate `m_8_7_cnst_Trans` verbatim to a
neutral shared frontier available after §6, keeping its fact name and all
annotations; keep `Trans_two_zero` chapter-7-local. This is a physical ownership
change, not a statement or proof change. After this planned resolution the
partition has zero placement violations. The record is in
[`helper_back_edges.tsv`](data/helper_back_edges.tsv).

## Proposition-file plan

The complete 128-row plan is in
[`chapter_file_plan.tsv`](data/chapter_file_plan.tsv). Each row records the
target path, clean proof root or named family, transitive article-file imports,
helper buckets, and proof-closure size. Its resulting file graph is acyclic,
has a 128-file topological order, and has zero earlier-chapter-to-later-chapter
imports.

The eight rows marked `unmapped` have deliberately incomplete import closures;
their proof wrapper/family must be associated manually before moving them. They
are:

- §7: `p_7_3_Mark_IncrFirst_Red`, `p_7_3_Trans_IncrFirst_Red`;
- §8: `p_8_1_condI_III_c1_around`,
  `p_8_2_condIIIV_terminal_slice_Trans`, `p_8_6_Trans_fseq_condVI`,
  `p_8_6_trailing_principal_annihilable`, `p_8_7_OT_tail_annihilable`, and
  `p_8_7_Pred_oper0`.

This is an association task for the existing frozen proofs, not authorization
to re-prove or alter a statement.

### §5 detailed pilot plan

Every file imports the relevant `PSS/Pre_5`/frontier shards. The table
below lists its transitive **article-file** import closure; blank means no other
§5 proposition file is needed.

| Target file | Transitive §5 article imports |
| --- | --- |
| `5/P_5_1_parent_basic_1.thy` | — |
| `5/P_5_1_parent_basic_2.thy` | — |
| `5/P_5_1_parent_exists_1.thy` | — |
| `5/P_5_1_parent_exists_2.thy` | — |
| `5/P_5_1_ancestor_basic_1.thy` | — |
| `5/P_5_3_pred_is_oper1.thy` | — |
| `5/P_5_4_F_oper_dom.thy` | — |
| `5/P_5_4_F_oper_val.thy` | — |
| `5/P_5_1_parent_exists_3.thy` | `P_5_1_parent_exists_1` |
| `5/P_5_1_ancestor_tree_1.thy` | `P_5_1_ancestor_basic_1`, `P_5_1_parent_exists_1`, `P_5_1_parent_exists_3` |
| `5/P_5_1_ancestor_basic_2.thy` | `P_5_1_ancestor_basic_1`, `P_5_1_ancestor_tree_1`, `P_5_1_parent_exists_1`, `P_5_1_parent_exists_3` |
| `5/P_5_1_parent_exists_4.thy` | `P_5_1_ancestor_basic_1`, `P_5_1_ancestor_tree_1`, `P_5_1_parent_exists_1`, `P_5_1_parent_exists_2`, `P_5_1_parent_exists_3` |
| `5/P_5_1_ancestor_tree_2.thy` | `P_5_1_ancestor_basic_1`, `P_5_1_ancestor_basic_2`, `P_5_1_ancestor_tree_1`, `P_5_1_parent_exists_1`, `P_5_1_parent_exists_2`, `P_5_1_parent_exists_3`, `P_5_1_parent_exists_4` |

The order shown is a valid chapter-local build order. §5 uses one local helper;
shared helper closures range from zero to nine facts per proposition and are
exported through the fine-grained shared frontiers described above.

### §6–§8 rollout sketch

| Chapter | Physical plan | Import boundary |
| --- | --- | --- |
| §6 | 55 `6/P_*.thy` files plus dependency-ordered `6/Support_*` shards for 52 local helpers | `PSS/After_5`, §5 proposition closures, and earlier §6/frontier files only |
| §7 | 27 `7/P_*.thy` files plus `7/Support_*` shards for 93 local helpers | `PSS/After_6`, earlier chapters, and earlier §7/frontier files only; first apply the `m_8_7_cnst_Trans` neutral relocation |
| §8 | 33 `8/P_*.thy` files plus `8/Support_*` shards for 1,137 local helpers | `PSS/After_7`, earlier chapters, and earlier §8/frontier files only |

The current layered sessions remain intact: the split files are assigned within
`PSS_A`, `PSS_B`, and `PSS_C` during later phases so the frozen-heap property is
preserved. `ROOT`, theory imports, and the audit are intentionally untouched in
Phase 0.

## Machine-readable artifacts and reproduction

| Artifact | Purpose |
| --- | --- |
| [`facts.raw.tsv`](data/facts.raw.tsv) | Raw theorem identities and metadata |
| [`dependencies.raw.tsv.gz`](data/dependencies.raw.tsv.gz) | Raw proof-term dependency rows, gzip-compressed without semantic changes |
| [`proposition_matches.raw.tsv`](data/proposition_matches.raw.tsv) | Raw alpha-equivalent proposition candidates |
| [`facts.tsv`](data/facts.tsv) | Canonical 4,353 top-level fact nodes |
| [`dependencies.tsv`](data/dependencies.tsv) | Canonical contracted edge list |
| [`topological_order.tsv`](data/topological_order.tsv) | Dependency-first order |
| [`helper_partition.tsv`](data/helper_partition.tsv) | Per-helper ownership and availability |
| [`upper_back_edges.tsv`](data/upper_back_edges.tsv) | The 22 text candidates checked against the real graph |
| [`proof_upper_back_edges.tsv`](data/proof_upper_back_edges.tsv) | Real upper-triangular named-section edges; empty |
| [`helper_back_edges.tsv`](data/helper_back_edges.tsv) | The one helper-mediated placement issue and resolution |
| [`chapter_file_plan.tsv`](data/chapter_file_plan.tsv) | Complete proposition-file/import plan |
| [`summary.json`](data/summary.json) | Counts and all graph-level checks |

The raw export was generated by a disposable session `PSS_PHASE0 = PSS_C +`
whose sole theory imported `PSS_C.pss_scratch` and used
`ML_file` on `extract_fact_dag.ML`:

```sh
PSS_PHASE0_OUT="$PWD/isabelle/phase0/data" \
  isbman build -m pss-phase0-dag -d . \
  -d /tmp/pss-phase0-session -v PSS_PHASE0
```

The temporary session wrapper is intentionally outside the repository: it
observes the finished `PSS_C` heap and cannot alter the production session
graph. After export, source paths in `facts.raw.tsv` were normalized to
repository-relative paths and the large raw edge table was gzip-compressed.

The derived artifacts can be regenerated from the raw export with:

```sh
python3 isabelle/phase0/analyze_fact_dag.py \
  isabelle/phase0/data isabelle/phase0/data
```

The analyzer reads either `dependencies.raw.tsv` or
`dependencies.raw.tsv.gz`. No existing `.thy` file is written by either the ML
extractor or the Python analyzer.
