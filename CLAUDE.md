# CLAUDE.md — pss-proof developer guide

Formal verification of the termination of the pair sequence system (ペア数列システム).
The source is P進大好きbot's article "ペア数列の停止性" (Termination of the pair sequence
system) on the Googology Wiki. Proposed corrections to the source: [corrections.md](corrections.md)
(30 live) and [corrections-old.md](corrections-old.md) (17 retracted — our own errors).

## Where things are (2026-07-20 reorganization)

| dir | what | status |
|---|---|---|
| `isabelle/` | Isabelle/HOL formalization. **Termination proved: zero hypotheses, zero `sorry`** (build-enforced ML audit). The approved file-layout reorganization is incremental; §5 is the completed pilot. | **PROOF frozen / layout reorg** |
| `lean/` | Lean 4 port. One article proposition = one file (`lean/7/7.2-scb-unique.lean`). | **ACTIVE** |
| `python/` | Counterexample search + numeric models (`red_model.py`, `trans_model.py` are canonical) | shared |
| `tools/` | Article processing (`make_content.py` regenerates `tmp/content.md`) | shared |

**Current work is the Lean port, driven by the wave plan in
[lean/workflow.md](lean/workflow.md) (start there after a fresh session).** Read, in this order:
[lean/spec.md](lean/spec.md) (structure) → [lean/step.md](lean/step.md) (procedure) →
[lean/task.md](lean/task.md) (progress tree) → [lean/memo.md](lean/memo.md) (design +
dead ends) → [lean/kimina.md](lean/kimina.md) (the Lean check server, incl. how workflow
agents use it).

The Isabelle progress tree is [isabelle/task.md](isabelle/task.md) (all ✅), and
the layout migration is governed by [isabelle/REORG-PLAN.md](isabelle/REORG-PLAN.md);
its design notes are [isabelle/memo.md](isabelle/memo.md). **The Isabelle proof is the
blueprint for the Lean port** — when a Lean proof stalls, the answer is almost always
already in `isabelle/5/`, `isabelle/PSS/`, `isabelle/pss_mechanized.thy`, or
`isabelle/layerC/pss_scratch.thy`. grep first.

The sections below describe the **Isabelle** side. They still apply when working in
`isabelle/` (note: all `isbman` commands now run from `isabelle/`, e.g.
`cd isabelle && isbman build -d . -v PSS_C`).

## Build — layered session split (append-only; never reprocess the stable body)

`ROOT` defines **nested sessions** so the huge proven body sits in pre-built heaps
and is never reprocessed; only the thin **active top layer** is built each round.
Each session lives in its own directory (Isabelle forbids two sessions in one dir)
and imports its parent's top theory **session-qualified** (`imports "PSS_A.pss_mechanized"`).

| session | dir | theory | role | green check |
|---|---|---|---|---|
| `PSS_A` | `.` | `pss_defs` + `PSS/` + `5/` + `pss_paper` + **`pss_mechanized`** | FROZEN base | `Finished PSS_A` |
| `PSS_B` | `layerB` | `pss_wip` | FROZEN base | `Finished PSS_B` |
| `PSS_C` | `layerC` | `pss_scratch` | **ACTIVE top** (current work) | `Finished PSS_C` |

```
isbman build -m "pss-..." -d . -v PSS_C   # everyone (sub-agents AND main): only the active layer
isbman build -m "pss-..." -d . -v PSS_B   # one-time: freeze the base (build A then B), then never again
```

- **Frozen base = A + B**: built **once**, then reused as heaps. NOT rebuilt per
  round. (A's first build reprocesses the 66k-line mechanized — that one ~11 min
  cost is paid once.)
- **Active layer = the top scratch session** (`PSS_C` now). **Both sub-agents and
  main build only this.** Per round: sub-agents prove lemmas in `pss_scratch` →
  verified → main collects them into `pss_scratch`, builds `PSS_C`, commits.
  **Proven lemmas ACCUMULATE in the active scratch — they are NOT moved back down
  into `pss_wip`** (that would force a 40k-line `PSS_B` rebuild every round — the
  whole point is to avoid it).
- **Freeze when the active layer fattens** (~a completed § or ~10k lines): rename
  `pss_scratch.thy` to a permanent `pss_segN.thy`, turn its `PSS_C` into a frozen
  layer, and start a **fresh empty `pss_scratch`** as a new top session `PSS_D` in
  `layerD` (imports `"PSS_C.pss_segN"`). Per-freeze cost = only the new chunk's
  heap (bounded — the body below is never reprocessed). The active layer stays thin.
- **Consolidation (rare safety valve)**: to reset the growing session/file count,
  fold the frozen `pss_segN` chunks into `pss_mechanized` and rebuild `PSS_A` once.
- **C→B fold (preferred over the freeze-chain; done 2026-07-11)**: when the active
  scratch fattens (per-round build in the minutes), append its whole body into
  `layerB/pss_wip.thy` (before the final `end`, with a dated banner) and reset the
  scratch, then rebuild once. Session names, build commands and the green check all
  stay unchanged. Measured at the 2026-07-11 fold (78k scratch lines → 118k-line
  `pss_wip`): one-time `PSS_B` rebuild 5:31; per-round `PSS_C` build drops from
  ~4:52 back to ~7 s. Each worktree pays the one-time `PSS_B` rebuild on its first
  build after syncing past the fold commit. After every fold, regenerate the TOC
  (`python3 tools/make_toc.py` → `docs/thy-toc.md`): a line-anchored index of all
  banner comments and section headings — agents grep it for topic/round/prefix
  orientation, then jump into the .thy at the reported line. The only authorized
  split of the frozen theories is the dependency-ordered chapter migration in
  `isabelle/REORG-PLAN.md`; keep the layered sessions and green gates intact.
- **Green = the target session's OWN `Finished` line**, NOT a bare `Finished PSS`
  (substring-matches all layers). Active build green: `grep -c 'Finished PSS_C'`
  == 1; plus no real errors and `sorry`/`oops` == 0 in the edited theory. (A `***`
  count is unreliable under concurrent worktree builds — use the real-error grep,
  see agent-workflow.md.)
- `isbman` wraps `isabelle build` (`isbman ps` lists builds, `isbman kill <id>`
  stops one). Never run `isabelle build` or `pkill` directly — blanket kills
  clobber other sessions' builds. `quick_and_dirty` is **required** (we use `sorry`).
- For long proof search, extend the timeout: `ISBMAN_TIMEOUT=2400 isbman build ...`.

## Repository layout and external files

The git repo lives in `git/`; its parent directory holds the large **external
sources** (gitignored, kept out of the tree): `original.html` (the raw article
HTML/LaTeX), `content.md` (the extracted article text), the `yaBMS/` calculator,
and reference PDFs/xlsx. `tmp/` is a symlink (`git/tmp -> ..`) so the in-repo
references `tmp/content.md`, `tmp/original.html`, `tmp/yaBMS/`, … resolve to the
parent. **Do not `git merge` a branch that tracks `tmp` as a committed symlink**
— that once clobbered the gitignored `tmp/` and lost `content.md`.

`content.md` is DERIVED from `original.html` and **regenerable**:
`python3 tools/make_content.py` (html2text + extraction recipe, anchored to
`tools/content-anchors.md` to keep the `content.md line NNN` references valid).
The Isabelle build only needs `tmp/content.md` to *exist* (`@{file}` check).

## File layout and roles

| File | Layer / dir | Role |
|---|---|---|
| `pss_defs.thy` | a (`.`) | Formalized **definitions** of the article (pair-sequence side, §4–§6) |
| `PSS/*.thy` | a (`PSS/`) | Dependency-ordered shared helpers; `Pre_5` plus proposition-dependent frontier shards |
| `5/P_*.thy` | a (`5/`) | One §5 article proposition per theory, with its exact clean proof and proposition-local material |
| `5/Support_*.thy` | a (`5/`) | Helpers used only within chapter 5 but shared by more than one proposition step |
| `pss_paper.thy` | a (`.`) | Remaining §6–§8 article statements, transcribed as `sorry`; imports the completed §5 proposition theories. The §7 Buchholz notation system also lives here |
| `pss_mechanized.thy` | a (`.`) | Remaining §6–§8 mechanized proofs; imports the completed §5 layer through `pss_paper` |
| `layerB/pss_wip.thy` | b | Earlier campaign's proven body — now FROZEN into the base heap |
| `layerC/pss_scratch.thy` | c | **ACTIVE** layer: the lemmas currently being proven (see the Build section) |

Import chain: `pss_defs` ← `PSS/Pre_5` ← §5 proposition/frontier theories ←
`pss_paper` ← `pss_mechanized` ← `pss_wip` ← `pss_scratch` (the last two
cross-session, imported session-qualified). Active proof work happens in
`layerC/pss_scratch.thy`; the rest is pre-built. When moving an `@{file}`
antiquotation into a chapter directory, adjust its relative path and add a local
`tmp` symlink only if it still addresses `tmp/...`.

## Naming and traceability

- Article claims are named `p_<§>_<slug>` and their proofs `m_<§>_<slug>`. For §5
  both live in the matching `5/P_<§>_<slug>.thy`; unmigrated chapters retain
  `p_` in `pss_paper.thy` and `m_` in their current proof layer.
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
- Collect typos/corrections to the source in `corrections.md`, as edits to the
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
- **Collapsing `if (A ∧ B) …` from a negated hypothesis** (e.g. after
  `subst P.simps` in the `P.simps[simp del]` region): `simp` rewrites a chained
  `¬(A ∧ B)` by de Morgan to `A ⟶ ¬B`, which no longer collapses the `if`, so
  it splits into spurious `(A∧B) ⟶ …` goals. Use `(rule if_not_P[OF nc])` with
  `nc : ¬(A ∧ B)` instead of `simp`.
- **`P.induct` on a goal with a meta-premise** mentioning the recursion variable
  (e.g. `M ≠ [] ⟹ …`) breaks the `case`/`.IH` structure. State the premise as
  an object implication (`M ≠ [] ⟶ …`), induct, then `… using assms by blast`.
  The IH is referenced **quoted**: `"1.IH"[OF <recursion-cond>]`.
- **`length_greater_0_conv[symmetric]` in the simpset loops** → use `cases`.
- **`linarith`/`presburger` loop in preprocessing on `let`-abbreviation goals
  where the abbreviation re-expands a complex atom**: e.g. with `let ?w = "Lng M
  - 1 - parent M 0 (Lng M-1)"`, a goal like `?j0 + (?w - 1) < Lng M` expands to
  `parent.. + (Lng M-1 - parent.. - 1) < Lng M` (the `parent` atom appears twice,
  under nested nat-subtraction). Supplying an extra hypothesis (`j0lt`) tips the
  preprocessing simplifier into a >2400s loop — **both** linarith and presburger.
  Fix: never hand such a goal to a decision procedure. Chain through a cheap
  `w0`-only assoc step (`?j0 + (?w-1) = ?j0 + ?w - 1`, fast) plus a pre-proved
  flat equation (`?j0 + ?w - 1 = Lng M - 2`, `by simp`) via `by simp` transitivity.
- **`Lng_seg` (a `[simp]` rule) rewrites `Lng (seg ..) - 1` mid-goal**, shifting
  `?j0 + (Lng Q - 1)` into an assoc-different `qb*w+r2` form that `simp` then
  won't re-close (`a+(b+c)` vs `a+b+c` inside a `seg` argument). Rewrite the
  endpoint with `arg_cong[OF eq, of "seg M a"]` instead of `simp`. Likewise
  `¬ zeroT (seg M a b)` blows up when `Lng(seg..)=1` normalizes messily: extract
  the `Lng = 1` conjunct (`zeroT_def`) and contradict `1 < Lng ..`, don't `simp`
  the whole `zeroT_def` (it evaluates the `entry ..` conjunct into garbage).

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
  **Commit messages are in English.** **`git push` is freely allowed in this
  repository — push whenever convenient, without asking** (2026-06-23 ユーザー明示:
  「このリポジトリでは自由に push して ok」). This supersedes the earlier
  "push is the USER's action" rule. Still: only push **green** (`Finished PSS`)
  commits, and never end turns with questions or option-choices (no asking
  permission, no "go か別か") — work autonomously and continue (2026-06-20 ユーザー明示).
- Prototype large new definitions (§6.5 `Red`, §7 Buchholz, …) in a **separate
  git worktree** to keep `main` green, then integrate (`git worktree add <dir>
  HEAD` is detached and creates no branch).
- **Worktree location** (2026-06-13): create every new worktree under
  `/home/koteitan/proofs/pss-proof/<worktree>/` (i.e. **alongside `git/`, not in
  `/home/koteitan/`**).
  `git worktree add /home/koteitan/proofs/pss-proof/wt-<name> HEAD`.
  Always use the **absolute path** in worktree paths and isbman `-d` arguments —
  agents copy these commands verbatim and `~`/relative forms cause confusion
  across contexts (2026-06-13 ユーザー指示). Rationale for the location: keeps
  every Isabelle session rooted in the same parent so `tmp/` symlinks (`<wt>/tmp
  -> ..`) resolve to the canonical external sources (`content.md`,
  `original.html`, `yaBMS/`, …), and isbman heap-isolation slugs stay under one
  tree. **Do not** create worktrees in `/home/koteitan/` or anywhere else —
  those leak past the parent's `tmp/` symlink and break the build.
- For parallel proving with agents, use worktree isolation (independent heaps).
  After integrating, remove the worktree AND delete its branch with
  `git branch -D worktree-agent-<id>`.
- **Spawning or working as a sub-agent? Read and follow
  [agent-workflow.md](agent-workflow.md)** — the parent/sub-agent rules
  (one self-contained lemma, no circular/false-axiom citation, empirical
  truth-check, blocker-first reporting, parent-builds-at-merge). It exists
  because aggressive fan-out produced circular false proofs and multi-hour
  stalls.
- don't use agent teams. use workflow.

## Design documents (`docs/`)

- [docs/red-termination.md](docs/red-termination.md) — the §6.5 `Red`
  definition and its termination measure.
- [docs/buchholz.md](docs/buchholz.md) — the Buchholz notation system [Buc1]
  definitions used in §7.
