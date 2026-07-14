# agent-workflow.md — parent + sub-agent workflow for pss-proof

How the **parent** (orchestrator session) and **sub-agents** (worktree provers)
collaborate to discharge `sorry`s. Read this together with
[CLAUDE.md](CLAUDE.md). Lessons here were paid for in circular false proofs and
multi-hour stalls — follow them.

## Roles

- **Parent**: picks targets, spawns sub-agents (worktree-isolated), integrates
  their proofs into `main`, and is the **only one who decides "done"** (by a
  green build). Never trusts a self-report as truth.
- **Sub-agent**: proves **one** self-contained lemma in its own worktree,
  reports the proof text + a quoted `Finished PSS`, and **does not commit/push**.

## Sub-agent rules (put these in every spawn prompt)

1. **Scope = one self-contained lemma.** Read CLAUDE.md first (esp. the layered
   Build section). **Add your lemmas to the ACTIVE layer `layerC/pss_scratch.thy`**
   (never edit `pss_wip`/`pss_mechanized` — those are the frozen base). Build the
   active session: `isbman build -m "pss-..." -d <worktree> -v PSS_C` (never
   `isabelle build`). After the base heap exists, only `pss_scratch` is rebuilt.
2. **Green = the line `Finished PSS_C`** (the active session's own line; a bare
   `Finished PSS` substring-matches the base layers too). NOT "Finished at" (that
   prints on failure). Under concurrent worktree builds a `***` may be a spurious
   SQLite-export artifact — judge by `Finished PSS_C` present AND the real-error
   grep `grep -cE 'Failed to|Type unification|Undefined fact|Outer syntax|Step
   error|Duplicate fact|exception|Unfinished'` == 0, not by `***` alone.
3. **NO `sorry` / `oops`** in the final proof (`grep -c "sorry\|oops"` must not
   increase).
4. **NO circular / forward / false-axiom citation.** Do **not** cite the goal
   itself, nor any *unproven* `p_*` `sorry` lemma, nor a proposition known false
   on the stated domain. Cite only already-proven facts and library lemmas.
   After finishing, `grep` your proof body to confirm. *(This is the one class
   of error a build does NOT catch — see "Why" below.)*
5. **Empirically check the statement is TRUE first.** Several article props in
   this project are false on their stated domain (e.g. `Red_le` on `T_PS`). Use
   `python/red_model.py` or hand examples. If you find a counterexample, STOP
   and report it — do not prove a false statement.
6. **Blocker-first reporting (anti-stall).** If the *same* obligation resists
   ~3–5 serious attempts, **STOP and report what it reduces to** (e.g. "needs
   `seg(Red(coreReduce M))..∈PT_PS`, which is the unproven `p_6_5_monoT_Red`").
   Do **not** grind silently for hours, and do **not** paper over with `sorry`
   or a fake cite. An honest partial result + named blocker beats a fake green.
7. **`tmp/` and `corrections.md` are symlinked into your worktree by the
   parent** — if `@{file "tmp/content.md"}` still errors, symlink them yourself.
8. **Report**: the quoted `Finished PSS` line; the complete proof text; the
   line range + names of every lemma/helper you added (for line-range
   extraction); confirmation of the grep audit (rule 4). Do not commit/push.

## Parent rules

1. **Spawn worktree-isolated on the current green HEAD** (Agent tool
   `isolation:"worktree"` bases on current HEAD — avoids stale-base divergence).
   Immediately `ln -s <main>/tmp <wt>/tmp` and `ln -s <main>/corrections.md
   <wt>/corrections.md` (worktrees lack them; otherwise `@{file}` errors spam
   the build).
2. **Pick INDEPENDENT, self-contained, empirically-true lemmas.** Do **not**
   parallelize an interdependent cluster (e.g. the §6.6 reducedness chain) —
   agents will cite each other's `sorry` statements and produce circular proofs.
   Parallelize only mutually-independent lemmas; do dependency chains
   sequentially.
3. **Bound task size.** One lemma. Never hand an agent a giant block with hidden
   hard dependencies (the `Red_IncrFirst` 2568-line port stalled for hours
   because part of it — dead-branch[20] — was an unproven dependency, not a bug).
4. **Long-running agents — judge by reasoning, not by build.**
   - A mid-flight worktree build is **not informative**: the worktree may be
     half-edited, and "not green yet" tells you nothing new and cannot
     distinguish *converging* from *thrashing*. Do not rely on spot-builds.
   - Instead, read the agent's **recent reasoning** (`tail` of its output, or
     ask it) to judge converging-vs-stuck, and set an **iteration/time budget**
     (e.g. "report if not green after N build attempts"). If it is thrashing on
     the same spot or chasing an impossible obligation, redirect, shrink the
     task, or take over.
   - Prevention (rules 2–3) matters far more than monitoring.
5. **Integration is the only place "done" is decided — always build.**
   - Extract the agent's block by **line range / marker**, not `diff | grep`
     (blank-line alignment drops lines and grabs adjacent lemmas).
   - Splice before the final `end`; watch helper-name collisions.
   - **Build and verify `Finished PSS`**, then commit. This build is the source
     of truth; never integrate on a self-report alone. (A clean splice can still
     break on base differences or name clashes.)
6. **Cleanup**: after integrating, `git worktree remove <wt>` and
   `git branch -D worktree-agent-<id>` so orphans don't accumulate.
7. **`git push` only on the user's explicit OK, each time.**

## Why rule 4 (no circular/false cite) is the critical one

The parent's integration build is a reliable safety net for almost everything:
a not-green proof is caught at merge. The **one** failure mode a build does
**not** catch is a proof that is green but **unsound** — i.e. it cited the goal
itself, or an unproven/false `sorry` axiom. Those build fine and silently
corrupt the development. So empirical truth-checking (rule 5) + the grep audit
(rule 4) are the irreplaceable defenses; everything else is backstopped by the
merge build.
