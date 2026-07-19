# Instructions: close the last open leaf — §8.4 fseq-basic part (2)

（koteitan → codex への指示書。2026-07-22 作成、本線セッション cd058bfc による。
以下は agent 向けなので英語。базовые rules は spec.md / step.md / kimina.md を先に読むこと。）

## 0. Context — where the project stands

- **The main theorem is DONE**: `p_8_7_termination` (lean/8/8.7-termination.lean) is
  **unconditional** — zero hypotheses, zero sorry, axioms exactly
  `[propext, Classical.choice, Quot.sound]`. Do NOT touch it.
- The progress tree (lean/task.md) has **exactly one open leaf**:
  `§8.4 補題（条件(III)か(IV)の下での基本列の基本性質）` part (2)
  (line: `🚨 part (2) — 8.4-l6-readouts-close [r6]`).
  Parts (1)(3) are ✅. Closing part (2) folds the whole tree to all-✅
  (= 原文カバレッジ完了, matching the Isabelle side).
- Everything below is **pure article coverage**; nothing gates the main theorem.
  A33 is retracted: part (2) is TRUE (empirically 130/130, and 41/41 on the
  producer-regime pool via `python/_l6_readouts_audit.py`).

## 1. The statement to close

Part (2) of the article lemma (content.md 5000; pss_paper.thy:2017
`p_8_4_oper_basic`): for `M` in the condIII/IV run regime,

```
operB (Trans M) (numBT (n - 1))
  = Trans ((fun N => oper N 1)^[(Lng M - 1) - 1 - parent M 1 (Lng M - 1)]
      (oper M (n + 1)))
```

The conditional form already exists and is green:
`oper_basic_part2 (hres : Oper84BasicPart2Residual) …`
in `lean/8/8.4-fseq-basic-close.lean:237`.

**Definition of done**: a green theorem `oper_basic_part2_uncond` with that exact
statement minus `hres`, axioms exactly `[propext, Classical.choice, Quot.sound]`,
then the board flip (§6 below).

## 2. The reduction chain that is ALREADY GREEN (do not re-prove)

The residual has been sharpened across five waves. The chain, all green on `main`:

```
L1SliceWrapperBridge ──(l6_base_leaf3_holds, 8.4-l1-slice-close)──► leaf (3')
LpReadoutResidual ──(lp_half2_lpc, 8.4-lp-readout-close)──► leaves (4') ∧ (2)
leaves (3')(4')(2)  =  L6BaseCoreResidual        (def in 8.4-l6-readouts-close)
L6BaseCoreResidual ──(l6BaseReadouts_of_core)──► L6BaseReadoutsResidual
                   ──(l6TowerResidual_holds, 8.4-l6-base-readouts)──► L6TowerResidual
                   ──(l6TransSliceClosed_holds, 8.4-l6-slice-close)──► L6TransSliceClosed_p2
                   ──(oper84BasicPart2_holds, 8.4-fseq-basic-part2)──► Oper84BasicPart2Residual
                   ──(oper_basic_part2, 8.4-fseq-basic-close)──► part (2)  ∎
```

(`oper_basic_part2_core` in 8.4-l6-readouts-close already packages the lower half:
`L6BaseCoreResidual → part (2)`.)

**So the ONLY remaining work = prove the two named Props at the top:**

### Target A: `L1SliceWrapperBridge` (def in lean/8/8.4-l1-slice-close.lean)

For the (unconditional, already available) `oper_rule_basic_part5` (n=2)
scb-decomposition `sb` of `Trans (s84x_L M 1)` at center
`Dprin (entry M 1 (s84x_jm2 M)) BZero`, the wrapper equals the producer's
assembled wrapper:
`sb.1 = s1 ++ Sym.dsym e3 :: s0` ∧ `sb.2 = b0 ++ b1` ∧
`(entry M 1 (s84x_jm2 M) : ℕ∞) = ub`.

- Isabelle blueprint: **base5** (isabelle/layerB/pss_wip.thy:60231) — the local
  `sbL`/`holeL1` construction pins the wrapper by comparing
  `s84c2_Trans_c2_decomp (L1)` against the M-side `dc1` via scb uniqueness.
- Lean assets already green: `l1SliceData_holds` (8.4-l1-slice-data — note:
  L1SliceData_se is ALREADY discharged, don't redo it; 14th asset-blindness catch),
  `leaf3_cr2` (8.4-corner-readouts; the condIV∧admeq corner of the L1 flat form is
  DONE there), `Trans_c1_c2_decomp` (8.3-condII-masterCF),
  `c2hole_scb_ch` (c2hole engine), `scb_unique_decomp_unconditional`
  (7.4-Mark-nextAdm; private — copy if needed), `flatBT_injective`.

### Target B: `LpReadoutResidual` (def in lean/8/8.4-lp-readout-close.lean)

Under the same binders/hypotheses: `Trans (s84x_Lp M)` is a **single principal**
with head `entry M 1 (s84x_jm2 M)`, and its flat is
`Sym.dsym ub :: flatBT (ins BZero)` (the lpv leaf).

- Isabelle blueprint: **m_8_4_rightend_Trans** (pss_wip.thy:54650) + the
  `s84d_dec*` Lp readout.
- Lean assets: `slice_Trans_principal_head` (8.2-condIIIV-terminal-slice-Trans —
  the master key for single-principal slice forms), `mono_slice` (6.4),
  `s84x_Lp` definition (8.4-exch84 corpus — grep), `m1_bounds`.

### If A/B bottom out: the cfbx_reg corpus

Five consecutive waves hit the same wall: the Isabelle proofs of base5 /
rightend_Trans consume the **cfbx_reg / REGS / REGSP regularity corpus**
(pss_wip.thy roughly 55000–62000), unported in Lean. If direct proofs of A/B
stall, port the **minimal** chain feeding base5 + rightend_Trans only — not the
whole corpus. Grep `cfbx_reg`, `REGS`, `REGSP`, `base5`, `s84d_L1_data`,
`s84d_c2hole_L1`, `m_8_4_rightend_Trans` and map the dependency cone first.

## 3. Known traps (all machine-verified this campaign — do not re-derive)

- **FALSE shortcuts**: `Rm84LpValue`, `MnformBottomResidual`, `Rm84Np`, `Rm84Lp`,
  `Rm84HeadValue` are all REFUTED value-claims. Do not route through them.
- **Pointwise trap**: Props that drop an IH or a `descending` hypothesis tend to
  be false or unprovable (11 refutations). Match Isabelle's hypothesis bundle
  character-by-character.
- **Asset blindness** (14 incidents): before porting ANYTHING, content-grep
  lean/ for an existing twin (search by conclusion shape, not by name).
- **Numeric check FIRST**: any new value claim must pass
  `python/_l6_readouts_audit.py` (41-host condIII/IV producer pool) or an
  adapted probe BEFORE you try to prove it.
- The audit script `python/audit_8_7_termination.py` is diagnostic only.

## 4. Verification rules (green = all three, per file)

1. `python3 python/check_lean.py lean/8/<file>.lean` → rc=0, no errors, **no sorry**
   (uses the kimina server on localhost:12345 — see lean/kimina.md; if you
   `lake build`, RESTART kimina afterwards: `pkill -f "python -m server"`, then in
   a separate shell `cd ~/proofs/pss-proof/kimina-lean-server && setsid nohup
   .venv/bin/python -m server >> /tmp/kimina-pss.log 2>&1 < /dev/null & disown`).
2. `#print axioms` for every public theorem → exactly
   `[propext, Classical.choice, Quot.sound]` (no sorryAx, no native_decide).
3. Statement faithful to the (corrected) article; cite 訂正 ids in the header.

House style: one new file per lemma cluster (`lean/8/8.4-<name>.lean`),
`namespace PSS`, header docstring with 原文/Isabelle line refs, discharge named
Props by making them the theorem's TYPE (`theorem foo_holds : SomeProp`),
collision-grep all new names, keep the file green after every 1–2 theorems.

## 5. Final composition (after A and B are green)

In a closing file (suggest `lean/8/8.4-part2-close.lean`), importing the chain files:

```lean
theorem l6BaseCore_holds : L6BaseCoreResidual := …   -- from A + B via
  -- l6_base_leaf3_holds (needs A) and lp_half2_lpc (needs B)
theorem oper_basic_part2_uncond … :=                 -- statement from
  -- 8.4-fseq-basic-close:237 minus hres
  oper_basic_part2 (oper84BasicPart2_holds …) …      -- or via oper_basic_part2_core
```

Then `cd lean && lake build` (expect ~3318 jobs, green), re-verify the closing
file, and run the full-tree canary: `python3 python/check_lean.py
lean/8/8.7-termination.lean` must stay green.

## 6. Board flip + commit (after everything is green)

- lean/task.md and lean/memo.md **together, same structure**:
  - part (2) → ✅ with the final file name and round count.
  - `8.4-fseq-basic` children now all ✅ → fold into one line, sum the [rN].
  - §8.4 children now all ✅ → fold §8.4 (sum). §8 children now all ✅ → fold §8.
  - The tree is then ALL ✅ → note the 原文カバレッジ完了 in memo.md (one dated
    entry appended to the Wave log, brief).
- Commit message in English; `git add <explicit paths>` only (**`git add -A`
  forbidden** — credential protection); chained `add && commit && push` is fine;
  push only green commits. Work on branch `codex` as usual; koteitan/the mainline
  session reviews and ff-merges.

## 7. Quick orientation pointers

- lean/memo.md — Wave AY/AZ/BA/BB/BC entries = the full history of this leaf
  (what was tried, what is false, exact residual statements).
- lean/spec.md（構造）, lean/step.md（手順・✅ 3 条件）, lean/kimina.md（checker）.
- isabelle/pss_wip.thy is frozen truth — when stuck, the answer is there; grep by
  content. docs/thy-toc.md is the line-anchored index.
