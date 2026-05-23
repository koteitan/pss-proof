# CLAUDE.md — pss-proof developer guide

Formal verification, in Isabelle/HOL, of the termination of the pair sequence
system (ペア数列システム). The source is P進大好きbot's article "ペア数列の停止性"
(Termination of the pair sequence system) on the Googology Wiki. This file is a
working guide for contributors (human and Claude alike). For the overall picture
see [README.md](README.md); for progress see [task.md](task.md); for proposed
corrections to the source see [amendments.md](amendments.md).

## Build

```
isbman build -d . -v PSS          # preferred (per-directory heap isolation)
# bms-proof runs concurrently on the same machine; ALWAYS tag PSS builds -m "pss-...":
isbman build -m "pss-§6.4-trunk" -d . -v PSS
```

- `isbman` wraps `isabelle build` (`isbman ps` lists builds, `isbman kill <id>`
  stops one). Never run `isabelle build` or `pkill` directly — blanket kills
  clobber other sessions' builds.
- Session is defined in `ROOT` (`session PSS = HOL`, `sessions HOL-Library`,
  `options [document = false, quick_and_dirty]`). `quick_and_dirty` is
  **required** because we use `sorry`.
- For long proof search, extend the timeout: `ISBMAN_TIMEOUT=2400 isbman build ...`.

## File layout and roles

| File | Role |
|---|---|
| `pss_defs.thy` | Formalized **definitions** of the article (pair-sequence side, §4–§6) |
| `pss_paper.thy` | **Statements only** of the article's propositions/lemmas/corollaries/theorems, transcribed as `sorry`. The §7 Buchholz notation system (definitions of the external reference [Buc1]) also lives here |
| `pss_mechanized.thy` | Our own **mechanized proofs** discharging the `sorry`s |

Import chain: `pss_defs` ← `pss_paper` ← `pss_mechanized`.

## Naming and traceability

- Article claims are named `p_<§>_<slug>` in `pss_paper.thy` (e.g.
  `p_6_4_mono_slice`); our proofs are `m_<§>_<slug>` in `pss_mechanized.thy`.
- Tag every fact's comment with the article section (§) and the original
  Japanese name, so it can be matched against `tmp/content.md` (the extracted
  article text).
- Give auxiliary lemmas a content prefix (`idxsum_*`, `poper_*`, `P_add_*`, …).

## Faithfulness policy

- Transcribe the article **faithfully**; do not introduce original elements.
  Where a proof is omitted, use `sorry` for now.
- Definitions that involve a modelling choice (e.g. `≤_M` as a reflexive-
  transitive closure) are not verbatim, so a **faithfulness lemma** (in the
  忠実性補題 section of `pss_mechanized.thy`) shows they coincide with the
  article's literal definition.
- Collect typos/corrections to the source in `amendments.md`, as edits to the
  HTML(LaTeX) source (for author feedback). Reference them by id (A1, A2, …)
  from the code and `task.md`.

## Isabelle gotchas (actually hit in this project)

- **`P.simps` simp loop**: the recursive function `P` auto-registers `P.simps`
  as `[simp]`, which unfolds forever. Work in the region with
  `declare P.simps[simp del]`, or unfold once with `subst P.simps`. Same for
  `Red` (use `Red.psimps`; termination is deferred so they are conditional).
- **oper notation `M[n]` parses ambiguously** against list application `M [n]`.
  Disambiguate with a type annotation: `(M::pairseq)[n]`.
- **`1::nat` normalization**: simp rewrites `1` to `Suc 0`, which stops rules
  like `oper1_eq` / `entry_pair` from firing. Avoid with `unfolding` (no
  normalization) or by expanding the definition directly.
- **`upt_Suc`** expands `[a..<Suc b]` and leaves arithmetic residue like
  `Suc(b-a)=Suc b-a`; use `simp ... del: upt_Suc`.
- **`Least`/`THE` higher-order unifiers**: multiple unifiers → instantiate
  explicitly, e.g. `Least_le[where P="λj. ...", OF wit]`.
- **`length_greater_0_conv[symmetric]` in the simpset loops** → use `cases`.

## Reusable helpers (in `pss_mechanized.thy`; grep for them)

- List/segment: `drop_eq_map_nth`, `seg_0_eq_take`, `seg_to_last_eq_drop`,
  `drop_eq_seg`, `Lng_seg`, `entry_seg`, `T_PS_Lng_gt1`, `multiT_imp_Lng_gt1`,
  `P_nonempty`.
- §6.2 fundamental sequence: `poper_*` (`poper_P_nonmulti`, `poper_oper_drop`,
  `poper_last_P_multi`, `poper_parent_*`, …), `P_add_*`, `Pcut_le`.
- §6.4 trunk/branches: `idxsum_*` (`idxsum_concat_P` = `concat (P M) = M`,
  `idxsum_nth`, `idxsum_mono`, `idxsum_leftend_lmin`, parent uniqueness, …).
- IncrFirst-invariance family, §6.3 admissibility `adm_*`.

## Workflow

- **Commits do not need confirmation** (write the message in `commit-msg.txt`).
  **Commit messages are in English.** **`git push` always needs the user's OK.**
- Prototype large new definitions (§6.5 `Red`, §7 Buchholz, …) in a **separate
  git worktree** to keep `main` green, then integrate (`git worktree add <dir>
  HEAD` is detached and creates no branch).
- For parallel proving with agents, use worktree isolation (independent heaps).
  After integrating, remove the worktree AND delete its branch with
  `git branch -D worktree-agent-<id>`.

## Design documents (`docs/`)

- [docs/red-termination.md](docs/red-termination.md) — the §6.5 `Red`
  definition and its termination measure.
- [docs/buchholz.md](docs/buchholz.md) — the Buchholz notation system [Buc1]
  definitions used in §7.
