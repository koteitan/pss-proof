# isabelle/ reorg — mirror the lean/ layout (chapter dirs, 1 proposition = 1 file)

Author: handed off by the Claude supervisor (user directive 2026-07-20). Read this
whole file before starting. This reorganizes the **completed, frozen** Isabelle proof;
it is a *relocation*, not a re-proof.

## Goal (target layout, mirroring `lean/`)

```
isabelle/
  PSS/            shared layer: definitions + reusable helpers  (≈ lean/PSS/)
  5/ 6/ 7/ 8/     one ARTICLE PROPOSITION per .thy, named after its p_<§>_<slug>
                  claim (statement + its mechanized proof + proposition-local lemmas),
                  importing the shared-layer theories it needs
  ROOT            keep the layered sessions (see below)
```

- Keep `ROOT`'s **layered sessions** (`PSS_A`/`PSS_B` frozen heaps, `PSS_C` active).
  We split the theory *files* within the sessions; the "frozen body built once" property
  is preserved because a frozen session builds once regardless of how many files it holds.
- The `p_<§>_<slug>` / `m_<§>_<slug>` naming already maps every claim to a section, so the
  target file set is well-defined. ~128 article propositions, ~4,400 supporting facts.

## Non-negotiable invariants (the proof is DONE — do not regress it)

1. **0 sorry / 0 hypotheses** for the termination theorems — exactly as now.
2. The **ML AUDIT** at the end of `layerC/pss_scratch.thy` (the block that raises
   `error "AUDIT FAILED: ... depends on sorry"`, ~line 24912) must keep running and
   passing. **Relocate it, never weaken or remove it.** A green build must still IMPLY
   audit-pass.
3. **Faithfulness unchanged — and keep ALL annotations.** You are *moving* statements/
   proofs verbatim, not altering them; statement text stays byte-identical. **Every
   comment/annotation in the original theories must survive into the destination file** —
   the `(* §x … *)` section tags, the original Japanese names, banner comments, design
   notes, `corrections.md` id references (Axx), `sorry`-citation notes, etc. Drop nothing.
   If the reorg makes a comment inconsistent (it says "the lemma above", cites
   `pss_wip.thy:NNN` / a line number, or references a sibling fact now in another file),
   **fix the reference so it is correct in the new layout** (point to the new file/theory
   name) rather than leaving a stale or contradictory note. (User directive 2026-07-20.)
4. **Green** per CLAUDE.md: target session's own `Finished PSS_x` == 1 line, 0 real
   errors, 0 `sorry`/`oops` in edited theories, `AUDIT FAILED` == 0.
5. Do **not** disturb the `tmp` symlink or `@{file}` antiquotations. `@{file}` theories
   need `tmp/content.md` at their dir root; keep them where `tmp/` resolves, or add a
   `tmp -> ..`-style symlink into any new dir that hosts an `@{file}` theory.

## Isolation & cadence

- Work on branch **`codex`** (keeps `main` green). FIRST run `git merge main` — you are
  behind by 3, tree clean, so this fast-forwards you to v0.2.0.
- **Incremental, chapter by chapter, green-gated.** Commit a green checkpoint after each
  chapter. Green push is allowed. Do NOT do all chapters in one shot.

## PHASE 0 — dependency DAG FIRST (do this before ANY file move)

Do **not** move a single line until the DAG is built and analyzed. A first-pass
section-level probe (by the supervisor) already found:

- The section→section reference graph is **near lower-triangular** (§5<§6<§7<§8):
  `§5` cites only §5; `§6` cites §5/§6; `§7` cites §5/§6/§7; `§8` cites all. So a
  chapter-dir layout with `imports` 5←6←7←8 + a shared base is natural.
- **~22 upper-triangular back-edges** exist (`§6→§7`≈8, `§7→§8`≈14). Enumerate and
  resolve each (a fact named for the section it is *about* but proved earlier/later,
  or a genuine back-reference to relocate/rename).
- **41% of references cross section boundaries**; **3,571 of 4,353 facts (82%) are
  helpers** (non `p_`/`m_`). The helper layer, not the 128 propositions, is the mass.

Deliverables of Phase 0 (a report + machine-readable data, NO file moves):

1. A **fact-level dependency DAG** built with Isabelle's real tooling
   (`Thm_Deps.thm_deps` / proof-term analysis / `isabelle dump` or
   `export_theory`), not text-grep. One node per top-level fact; edges = uses.
2. Confirm it is acyclic and give a **topological order** consistent with the
   append order it already has.
3. A proposed **helper partition**: which of the 3,571 helpers go into the shared
   `PSS/` layer (used by ≥2 chapters) vs stay chapter-local (used by one chapter's
   propositions only). Give counts per bucket.
4. The **~22 upper-triangular back-edges** listed with a resolution for each.
5. A per-chapter **file plan**: for §5 first (then a sketch for §6–§8), the list of
   target `.thy` files and, for each, its `imports` closure.
6. A go/no-go feasibility verdict per chapter with the estimated round cost.

**STOP after Phase 0 and report to the supervisor (the Claude watcher).**
**Overnight autonomy (user delegated 2026-07-20 night):** the human is asleep. The
supervisor reviews your Phase-0 report and **authorizes each phase itself** — do NOT wait
for the human. After the supervisor's go, proceed §5 → §6 → §7 → §8 **to completion**,
each chapter green + audit + annotations gated (invariants above), committing a green
checkpoint per chapter and reporting at each phase boundary so the supervisor can verify
before the next chapter.

## PHASE 1 (PILOT) — after the supervisor's Phase-0 go: do §5 ONLY, then STOP and report

§5 = 13 propositions: `p_5_1_parent_exists_{1..4}`, `p_5_1_parent_basic_{1,2}`,
`p_5_1_ancestor_basic_{1,2}`, `p_5_1_ancestor_tree_{1,2}`, `p_5_3_pred_is_oper1`,
`p_5_4_F_oper_dom`, `p_5_4_F_oper_val`.

1. Create `isabelle/5/` with one `.thy` per proposition (its `pss_paper` statement +
   its `pss_mechanized`/`pss_wip` proof + any proposition-local lemmas), each importing a
   shared `PSS`-layer theory for `pss_defs` and the helpers it uses.
2. Establish the **shared-helper factoring mechanism** (how helpers like `seg_*`,
   `idxsum_*`, `Lng_*`, `poper_*`, `adm_*` are pulled into the `PSS/` layer and imported).
   The pilot's real purpose is to VALIDATE this mechanism and the ROOT wiring.
3. Wire the new files into `ROOT`, rebuild **GREEN + audit-pass**, commit
   `isabelle: reorg pilot — §5 to chapter-dir/per-proposition files`.
4. **Report** (do not continue to §6–§8): what worked, the helper-factoring scheme, the
   per-file build cost, and any blocker. The supervisor relays your report to the user,
   who decides on the full roll-out.

## Expected hard part

The ~4,400 supporting lemmas are heavily coupled through shared helpers (`seg_` 356×,
`scb` 336×, `idxsum_` 225×, `Lng_` 197×, `poper_` 195×, `adm_` 135× in mechanized alone).
The shared-helper theory(ies) are the crux: topologically order them, no import cycles.
§5 is shallow (parent/ancestor/F basics over `pss_defs`), so it is a clean first validation.
