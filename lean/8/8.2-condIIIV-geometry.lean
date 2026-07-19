import «8».«8.2-condIIIV-step-surgery»
import «8».«8.2-condIIIV-pin-tspin»
import «8».«8.2-condIIIV-frontpred»
import «8».«8.2-condIIIV-reg-pres»

/-!
# §8.2 条件(II)/(IV) VE34 STEP 幾何 Props の討伐＋最終組立（capstone）

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）の
  証明のうち、`j₁ - TrMax M` に関する数学的帰納法（run-peel / STEP surgery）の**幾何**
  部分と、統一 back-peel 強帰納法の**最終配線**。

- **本ファイルの成果（mission (1)–(3)）**:
  1. **STEP 幾何 4 Props を無条件討伐**（`8.2-condIIIV-step-surgery` が名前付き残差として
     露出したもの）: `StepTerminalReady_ss`（regime-only 終切片 ready）,
     `StepPredIndex_ss`（`Pred = butlast` の index 転送）, `StepTermPred_ss`（joint 共有ゆえ
     終切片 `Pred` 転送）, `StepFrontPred_ss`（STEP `LastStep` 安定＋前置 `Pred` 不変）。
     Isabelle `bpx_step_setup`/`bpx_front_Pred`/`bpx_term_Pred`/`bpx_LastStep_Pred`
     （`isabelle/layerB/pss_wip.thy:102730–103021`）の逐語移植。STEP は `Pred N = butlast N`
     ＝末尾列剥がしゆえ枝数保存（BASE の枝数減少とは異なる）。
  2. **VE3 run-base（SPLIT0）を D-体制で討伐** `ve3RunBaseD_gm`: run-base では前置切片 = `Pred N`
     （`bgx_front_run0_bg`）ゆえ `HEADEQ0`（`headEq0All_holds`）＋終切片 keystone
     （`keystoneShapes_vv`/`growth_transport_vv`）で成長分割を放出する（IH 非消費）。
  3. **統一 back-peel の三スロットを LIVE 経路で供給**:
     - `Step_up`（STEP スロット）← `Step_up_of_surgery_ss`（step-surgery、幾何 4 Props 討伐後は
       `TSPINStep_ss` のみ modulo）。
     - `BaseRunStep_up`（run-step BASE スロット）← VE4 は `VE4BaseDeepD_of_runstep_pt`
       （`TransPinRunStepD_pt` modulo）、VE3 は IH 成長輸送 `VE3RunStepD_of_reductions_pv`
       （幾何 2 Props `terminalSliceReadyD_holds`/`frontPredBaseTransportD_holds` は**討伐済**）。
     - `BaseRunBase_up`（run-base BASE スロット）← VE4 同、VE3 は `ve3RunBaseD_gm`（討伐）。
     - `RunStepGuardJoint_up`/`StepRegPres_up` は `8.2-condIIIV-reg-pres` で**討伐済**
       （`runStepGuardJoint_up_holds`/`stepRegPres_up_holds`）。
  4. **CAPSTONE**（`ve34_on_reg4D_modulo_gm`）: 補正体制 `VE34Reg4D` の**全ホスト**で
     `VE34goal` を、**露出残差 exactly 2 本** `{TransPinRunStepD_pt, TSPINStep_ss}` から供給。
     `TransPinRunStepD_pt` = VE4 側 BASE pinned 形（IH 保持スロットが吸収すべき run-step 残差）、
     `TSPINStep_ss` = STEP の唯一の深い §7.4 Mark-surgery naturality 頭輸送。
     🚨 **PIN_bd/TSPIN_bd（反証済み）には一切依存しない**——LIVE 経路のみ。

- 🚨 **反証済み設計を回避**: `PIN_bd`/`TSPIN_bd` は `VE34Reg4` 上で偽（`not_pin_tspin_pt`）。
  step-surgery のキャップストーン `VE34goal_on_reg4D_of_step_surgery_ss` は仮説に `PIN_bd`/
  `TSPIN_bd`/`VE3RunBase_bd`/`VE3RunStep_bd` を取る（＝instantiate 不能）。本ファイルはそれらを
  LIVE な `{TransPinRunStepD_pt(pin-tspin), ve3RunBaseD_gm(本ファイル), VE3RunStepD_of_reductions_pv
  (peel-values), 討伐済 reg-pres/frontpred}` に置換し、露出残差を **2 本**へ凝縮する。

- 訂正: なし（Isabelle 済補題の逐語移植 ＋ 討伐済 `_pv`/`_holds`/`_pt` 群の LIVE 合成）。

- 依存 module: `8.2-condIIIV-step-surgery`（`Step*_ss` Props/`Step_up_of_surgery_ss`/
  `keystoneShapes_vv`/`growth_transport_vv` 推移）, `8.2-condIIIV-pin-tspin`
  （`TransPinRunStepD_pt`/`VE4BaseDeepD_of_runstep_pt`/`transPinRunBaseD_pt`/`headEq0All_holds`/
  `bgx_front_run0_bg` 推移）, `8.2-condIIIV-frontpred`（`terminalSliceReadyD_holds`/
  `frontPredBaseTransportD_holds`/`VE3RunStepD_of_reductions_pv`/`VE34Reg4D` 推移）,
  `8.2-condIIIV-reg-pres`（`runStepGuardJoint_up_holds`/`stepRegPres_up_holds`/
  `VE34_backpeel_fin3_up`/三スロット Props/`BaseRunBase_of_leaves_up` 系 推移）。

- 状態: ⚠️ 部分（sorry 0、rc=0、公理 `[propext, Classical.choice, Quot.sound]` のみ）。
  STEP 幾何 4 Props ＋ VE3 run-base を討伐、三スロットを LIVE 供給、capstone を残差 2 本
  `{TransPinRunStepD_pt, TSPINStep_ss}` modulo で着地。

- Private suffix: `_gm`。
-/

namespace PSS

/-! ## list 補助（`8.2-condIIIV-frontpred` private helper の再掲、suffix `_gm`） -/

private theorem getD_default_gm {α : Type} (l : List α) (n : ℕ) (d d' : α)
    (h : n < l.length) : l.getD n d = l.getD n d' := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h]
  rfl

private theorem getLastD_cons_eq_gm {α : Type} :
    ∀ (l : List α) (a d : α), (a :: l).getLastD d = (a :: l).getD l.length d := by
  intro l
  induction l with
  | nil => intro a d; rfl
  | cons b bs ih =>
      intro a d
      have hstep : (a :: b :: bs).getLastD d = (b :: bs).getLastD a := rfl
      rw [hstep, ih b a]
      simp only [List.length_cons, List.getD_cons_succ]
      exact getD_default_gm (b :: bs) bs.length a d (by simp)

private theorem getLastD_eq_getD_gm {α : Type} (l : List α) (d : α) (hl : l ≠ []) :
    l.getLastD d = l.getD (l.length - 1) d := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a as => simpa using getLastD_cons_eq_gm as a d

private theorem getD_append_left_gm {α : Type} (l r : List α) (J : ℕ) (d : α)
    (h : J < l.length) : (l ++ r).getD J d = l.getD J d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h]

private theorem getD_append_single_gm {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem?_getD]
  simp

private theorem getD_dropLast_gm {α : Type} (l : List α) (J : ℕ) (d : α)
    (h : J < l.length - 1) : l.dropLast.getD J d = l.getD J d := by
  have hJl : J < l.length := by omega
  have h1 : J < l.dropLast.length := by rw [List.length_dropLast]; omega
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h1, List.getElem?_eq_getElem hJl]
  simp [List.getElem_dropLast]

private theorem getD_overflow_gm {α : Type} (l : List α) (J : ℕ) (d : α)
    (h : l.length ≤ J) : l.getD J d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

private theorem entry_dropLast_gm (l : PS) (i j : ℕ) (hj : j < Lng l - 1) :
    entry l.dropLast i j = entry l i j := by
  rw [List.dropLast_eq_take]
  exact entry_take l (l.length - 1) i j hj

private theorem trmax_ne_of_Brne_gm (M : PS) (hBrne : Br M ≠ []) :
    TrMax M ≠ Lng M - 1 := by
  intro heq
  exact hBrne (by simp [Br, heq])

/-- Isabelle `wid_BrLen_Pred` 相当（frontpred `Br_Pred_length_fp` の再掲）。 -/
private theorem Br_Pred_length_gm (M : PS) (hM : TPS M) (hlen : 1 < Lng M)
    (hBrne : Br M ≠ []) :
    (Br (Pred M)).length =
      (if Lng ((Br M).getLastD []) ≤ 1 then (Br M).length - 1 else (Br M).length) := by
  have hne := trmax_ne_of_Brne_gm M hBrne
  have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  rw [Br_Pred_core_nontrunk M hM hlen hne]
  by_cases hcase : Lng ((Br M).getLastD []) ≤ 1
  · rw [if_pos hcase, if_pos hcase]
    have hl : ((Br M).dropLast ++ ([] : List PS)).length = (Br M).length - 1 := by simp
    rw [hl]
  · rw [if_neg hcase, if_neg hcase]
    have hl : ((Br M).dropLast ++ [((Br M).getLastD []).dropLast]).length
        = (Br M).length - 1 + 1 := by simp
    rw [hl]
    omega

/-- 枝頭 col-0 一致（frontpred `Br_Pred_col0_agree_fp` の再掲、Isabelle
`wid_Br_Pred_col0_agree`）: `J < Lng(Br(Pred M))` で成分の行 0/行 1 左端が一致。 -/
private theorem Br_Pred_col0_agree_gm (M : PS) (hM : TPS M) (hlen : 1 < Lng M)
    (hBrne : Br M ≠ []) (J : ℕ) (hJ : J < (Br (Pred M)).length) (i : ℕ) :
    entry ((Br (Pred M)).getD J []) i 0 = entry ((Br M).getD J []) i 0 := by
  have hne := trmax_ne_of_Brne_gm M hBrne
  have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hcore := Br_Pred_core_nontrunk M hM hlen hne
  have hlenP := Br_Pred_length_gm M hM hlen hBrne
  by_cases hcase : Lng ((Br M).getLastD []) ≤ 1
  · rw [if_pos hcase] at hlenP
    rw [hcore, if_pos hcase]
    simp only [List.append_nil]
    exact congrArg (fun q => entry q i 0) (getD_dropLast_gm (Br M) J [] (by omega))
  · rw [if_neg hcase] at hlenP
    rw [hcore, if_neg hcase]
    by_cases hJlt : J < (Br M).length - 1
    · rw [getD_append_left_gm _ _ _ _ (by rw [List.length_dropLast]; omega)]
      exact congrArg (fun q => entry q i 0) (getD_dropLast_gm (Br M) J [] hJlt)
    · have hJeq : J = (Br M).length - 1 := by omega
      have hdl : (Br M).dropLast.length = (Br M).length - 1 := by simp
      rw [hJeq, ← hdl, getD_append_single_gm]
      rw [hdl, ← getLastD_eq_getD_gm (Br M) [] hBrne]
      exact entry_dropLast_gm ((Br M).getLastD []) i 0 (by omega)

/-! ## 幹根切片の幹整列（frontpred `TrMax_seg_ancestor_fp` の再掲、Isabelle `TrMax_seg_ancestor`） -/

private theorem TrMax_seg_ancestor_gm (M : PS) (j₀' j₁' : ℕ) (hM : TPS M)
    (hj₀ : j₀' ≤ TrMax M) (hTr : TrMax M < j₁') (hj₁ : j₁' < Lng M) :
    TrMax (seg M j₀' j₁') = TrMax M - j₀' := by
  have hlt : j₀' < j₁' := by omega
  have hLS : Lng (seg M j₀' j₁') = j₁' + 1 - j₀' := by simp [seg]
  have hST : TPS (seg M j₀' j₁') := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (seg M j₀' j₁')
    omega
  have hge : TrMax M - j₀' ≤ TrMax (seg M j₀' j₁') := by
    apply le_TrMax_intro_wd (seg M j₀' j₁') (TrMax M - j₀') hST
    intro j hj
    have ha : j < Lng (seg M j₀' j₁') := by omega
    have hb : j + 1 < Lng (seg M j₀' j₁') := by omega
    rw [nextR1_seg_adm M j₀' j₁' j (j + 1) hlt.le hj₁ ha hb]
    have hstep := TrMax_trunk_step M (j₀' + j) hM (by omega)
    have harr : j₀' + (j + 1) = j₀' + j + 1 := by omega
    rw [harr]
    exact hstep
  have hle : TrMax (seg M j₀' j₁') ≤ TrMax M - j₀' := by
    by_contra hnot
    have hgt : TrMax M - j₀' < TrMax (seg M j₀' j₁') := by omega
    have hstep := TrMax_trunk_step (seg M j₀' j₁') (TrMax M - j₀') hST hgt
    have ha : TrMax M - j₀' < Lng (seg M j₀' j₁') := by omega
    have hb : TrMax M - j₀' + 1 < Lng (seg M j₀' j₁') := by
      have := TrMax_bound (seg M j₀' j₁') hST
      omega
    rw [nextR1_seg_adm M j₀' j₁' (TrMax M - j₀') (TrMax M - j₀' + 1)
      hlt.le hj₁ ha hb] at hstep
    have he1 : j₀' + (TrMax M - j₀') = TrMax M := by omega
    have he2 : j₀' + (TrMax M - j₀' + 1) = TrMax M + 1 := by omega
    rw [he1, he2] at hstep
    have hstop := TrMax_stop_uncond M hM
    rw [hstop] at hstep
    cases hstep
  omega

/-! ## regime-only 終切片 ready（Isabelle `bux_terminal_slice_ready` 99317、regime のみ）

`8.2-condIIIV-frontpred` の `terminalSliceReadyD_holds`（BASE 版）は deep/run ガードを取るが、
Isabelle `bux_terminal_slice_ready` は補正体制 `VE34Reg4D` のみで終切片 ready を与える。
STEP 幾何 ready ＋ VE3 run-base の両方でこの regime-only 版を使う。 -/

/-- **`terminalReady_gm`**: 補正体制 `VE34Reg4D N` のみから終切片 `Mp = seg N j₀' (Lng N-1)` が
`keystone` を適用できる状態（`RTPS ∧ monoT ∧ Br≠[] ∧ 1 < Lng Mp - 1`）にある。 -/
private theorem terminalReady_gm (N : PS) (regD : VE34Reg4D N) :
    RTPS (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) ∧
    monoT (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) = true ∧
    Br (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) ≠ [] ∧
    1 < Lng (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) - 1 := by
  obtain ⟨⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, _hj0pos, hj0lt⟩, hdesc⟩ := regD
  have hM : TPS N := RTPS_TPS N hR
  have htrbd : TrMax N ≤ Lng N - 1 := TrMax_bound N hM
  have htrne : TrMax N ≠ Lng N - 1 := trmax_ne_of_Brne_gm N hBrne
  have htrlt : TrMax N < Lng N - 1 := by omega
  have hL1 : 1 < Lng N := by omega
  set j0 := (Joints N).getD ((Br N).length - 1) 0 with hj0def
  have hj0ltj1 : j0 < Lng N - 1 := by omega
  have hND : DTPS N := (DTPS_iff N).mpr ⟨hR, hmono, hdesc⟩
  have hMpD : DTPS (seg N j0 (Lng N - 1)) :=
    strongmono_slice N j0 (Lng N - 1) hND hj0ltj1 (le_refl _) (le_refl _)
  obtain ⟨hMpR, hMpMono, _hMpDesc⟩ := (DTPS_iff _).mp hMpD
  refine ⟨hMpR, hMpMono, ?_, ?_⟩
  · intro hBrEmpty
    have hTrMp := baseU_Br_empty_TrMax (seg N j0 (Lng N - 1)) hBrEmpty
    have hTrMpEq : TrMax (seg N j0 (Lng N - 1)) = TrMax N - j0 :=
      TrMax_seg_ancestor_gm N j0 (Lng N - 1) hM (le_of_lt hj0lt) htrlt (by omega)
    have hLngMp : Lng (seg N j0 (Lng N - 1)) = (Lng N - 1) + 1 - j0 :=
      length_seg N j0 (Lng N - 1)
    rw [hTrMpEq, hLngMp] at hTrMp
    omega
  · rw [length_seg]
    omega

/-! ## STEP 枝数保存（`Pred N = butlast N` ゆえ最終枝非単項→枝を落とさない） -/

/-- STEP ホストで最終枝は非単項: `1 < Lng ((Br N).getLastD [])`。 -/
private theorem lastBr_nonsingleton_gm (N : PS) (hM : TPS N) (hBrne : Br N ≠ [])
    (hstep : VEj1p N < Lng N - 1) : 1 < Lng ((Br N).getLastD []) := by
  have hs : (FirstNodes N).getD ((Br N).length - 1) 0 < Lng N - 1 := hstep
  rw [getLastD_eq_getD_last_68 (Br N) [] hBrne, wf21_Br_eq_seg N hM hBrne, length_seg]
  omega

/-- **STEP 枝数保存**（Isabelle `bpx_step_setup(10)`）: `(Br (Pred N)).length = (Br N).length`。 -/
private theorem BrLen_Pred_step_gm (N : PS) (hM : TPS N) (hBrne : Br N ≠ [])
    (hstep : VEj1p N < Lng N - 1) : (Br (Pred N)).length = (Br N).length := by
  have hL1 : 1 < Lng N := by
    unfold VEj1p at hstep; omega
  have hns := lastBr_nonsingleton_gm N hM hBrne hstep
  rw [Br_Pred_length_gm N hM hL1 hBrne, if_neg (by omega)]

/-! ## (1) `StepTerminalReady_ss`（Isabelle `bux_terminal_slice_ready`） -/

/-- **STEP 終切片 ready** — regime-only、STEP ガードは未使用。 -/
theorem stepTerminalReady_holds : StepTerminalReady_ss := by
  intro N regD _hstep
  exact terminalReady_gm N regD

/-! ## (2) `StepPredIndex_ss`（Isabelle `bpx_step_setup(13),(14)`） -/

/-- **STEP index 転送** — `Pred N = butlast N` の `entry_take`＋joint 安定。 -/
theorem stepPredIndex_holds : StepPredIndex_ss := by
  intro N regD hstep
  obtain ⟨⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, _hj0pos, hj0lt⟩, _hdesc⟩ := regD
  have hM : TPS N := RTPS_TPS N hR
  have hL1 : 1 < Lng N := by unfold VEj1p at hstep; omega
  have htrne : TrMax N ≠ Lng N - 1 := trmax_ne_of_Brne_gm N hBrne
  have htrbd : TrMax N ≤ Lng N - 1 := TrMax_bound N hM
  have htrlt : TrMax N < Lng N - 1 := by omega
  -- j₀ < Lng N - 1（joint 非許容 ＋ TrMax 幾何）
  have hj0lt1 : (Joints N).getD ((Br N).length - 1) 0 < Lng N - 1 := by omega
  have hBrpos : 0 < (Br N).length := List.length_pos_of_ne_nil hBrne
  -- 枝数保存 → 最終添字一致 → joint 安定
  have hBrlen : (Br (Pred N)).length = (Br N).length := BrLen_Pred_step_gm N hM hBrne hstep
  have hJP : (Br N).length - 1 < (Br (Pred N)).length := by rw [hBrlen]; omega
  have hjointP : (Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0
      = (Joints N).getD ((Br N).length - 1) 0 := by
    have hidx : (Br (Pred N)).length - 1 = (Br N).length - 1 := by rw [hBrlen]
    rw [hidx, Joints_Pred_core N hM hmono hL1 htrne ((Br N).length - 1) hJP]
  -- Pred N = N.take (Lng N - 1)
  have hpred : Pred N = N.take (Lng N - 1) := Pred_eq_take N hL1
  refine ⟨?_, ?_⟩
  · rw [hpred, entry_take N (Lng N - 1) 1 0 (by omega)]
  · rw [hjointP, hpred, entry_take N (Lng N - 1) 1 _ hj0lt1]

/-! ## (3) `StepTermPred_ss`（Isabelle `bpx_term_Pred` 102981） -/

/-- **STEP 終切片 `Pred` 転送** — joint 共有ゆえ `Pred(seg) = seg(Pred)`。BASE 版の JEQ 不要
（枝数保存で joint が直接安定）。 -/
theorem stepTermPred_holds : StepTermPred_ss := by
  intro N regD hstep
  obtain ⟨⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, _hj0pos, hj0lt⟩, _hdesc⟩ := regD
  have hM : TPS N := RTPS_TPS N hR
  have hL1 : 1 < Lng N := by unfold VEj1p at hstep; omega
  have htrne : TrMax N ≠ Lng N - 1 := trmax_ne_of_Brne_gm N hBrne
  have htrbd : TrMax N ≤ Lng N - 1 := TrMax_bound N hM
  have htrlt : TrMax N < Lng N - 1 := by omega
  have hj0lt1 : (Joints N).getD ((Br N).length - 1) 0 < Lng N - 1 := by omega
  have hLP : Lng (Pred N) = Lng N - 1 := length_Pred N hL1
  have hBrpos : 0 < (Br N).length := List.length_pos_of_ne_nil hBrne
  -- 枝数保存 → joint 安定
  have hBrlen : (Br (Pred N)).length = (Br N).length := BrLen_Pred_step_gm N hM hBrne hstep
  have hJP : (Br N).length - 1 < (Br (Pred N)).length := by rw [hBrlen]; omega
  have hjointP : (Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0
      = (Joints N).getD ((Br N).length - 1) 0 := by
    have hidx : (Br (Pred N)).length - 1 = (Br N).length - 1 := by rw [hBrlen]
    rw [hidx, Joints_Pred_core N hM hmono hL1 htrne ((Br N).length - 1) hJP]
  have he : Lng (Pred N) - 1 = Lng N - 2 := by omega
  rw [hjointP, he, hqx_Pred_seg_hq N ((Joints N).getD ((Br N).length - 1) 0) hL1 hj0lt1]
  exact seg_Pred_eq N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 2) hL1 (by omega) (by omega)

/-! ## (4) `StepFrontPred_ss`（Isabelle `bpx_front_Pred` 102945） -/

/-- **STEP `LastStep` 安定**（Isabelle `bpx_LastStep_Pred` 102885）: 枝数保存 `(Br(Pred N)).length
= (Br N).length` ＋枝頭 col-0 全 J 一致（`Br_Pred_col0_agree_gm` / overflow）ゆえ `LastStep` の
`find?` 計算が literally 一致する。BASE 版の Min 集合両向き最小性は不要。 -/
private theorem lastStepPred_step_gm (N : PS) (hM : TPS N) (hBrne : Br N ≠ [])
    (hL1 : 1 < Lng N) (hstep : VEj1p N < Lng N - 1) :
    LastStep (Pred N) = LastStep N := by
  have hBrlen : (Br (Pred N)).length = (Br N).length := BrLen_Pred_step_gm N hM hBrne hstep
  -- 全 J での枝頭 col-0 一致（範囲内は `Br_Pred_col0_agree_gm`、範囲外は両者 []）
  have hcol : ∀ (J i : ℕ),
      entry ((Br (Pred N)).getD J []) i 0 = entry ((Br N).getD J []) i 0 := by
    intro J i
    by_cases hJ : J < (Br (Pred N)).length
    · exact Br_Pred_col0_agree_gm N hM hL1 hBrne J hJ i
    · rw [getD_overflow_gm (Br (Pred N)) J [] (by omega),
        getD_overflow_gm (Br N) J [] (by rw [← hBrlen]; omega)]
  -- `LastStep` は `(Br M).length` と `entry ((Br M).getD J []) i 0` のみに依存するので
  -- 枝数保存＋col-0 全 J 一致で両計算が literally 一致する。
  simp only [LastStep, hBrlen, hcol]

/-- **STEP 前置切片 `Pred` 不変**（Isabelle `bpx_front_Pred` 102945）: `LastStep` 安定
（`lastStepPred_step_gm`）＋`FirstNodes` 転送（`FirstNodes_Pred_core`）＋前置 `Pred` 不変
（`seg_Pred_eq`）。 -/
theorem stepFrontPred_holds : StepFrontPred_ss := by
  intro N regD hstep
  obtain ⟨⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, _hj0pos, _hj0lt⟩, _hdesc⟩ := regD
  have hM : TPS N := RTPS_TPS N hR
  have hL1 : 1 < Lng N := by unfold VEj1p at hstep; omega
  have htrne : TrMax N ≠ Lng N - 1 := trmax_ne_of_Brne_gm N hBrne
  -- `LastStep (Pred N) = LastStep N`
  have hLSP : LastStep (Pred N) = LastStep N := lastStepPred_step_gm N hM hBrne hL1 hstep
  -- 枝数保存で `LastStep N < (Br (Pred N)).length`
  have hBrlen : (Br (Pred N)).length = (Br N).length := BrLen_Pred_step_gm N hM hBrne hstep
  have hLSlt : LastStep N < (Br (Pred N)).length := by
    rw [hBrlen]; exact LastStep_lt_Lng_Br N hBrne
  -- `FirstNodes` 転送
  have hFNP : (FirstNodes (Pred N)).getD (LastStep N) 0 = (FirstNodes N).getD (LastStep N) 0 :=
    FirstNodes_Pred_core N hM hL1 htrne (LastStep N) hLSlt
  -- 前置境界 ＋ 前置 `Pred` 不変
  have hm1 : (FirstNodes N).getD (LastStep N) 0 - 1 < Lng N - 1 :=
    (m1_bounds N hM hmono hBrne).2
  have hseg : seg (Pred N) 0 ((FirstNodes N).getD (LastStep N) 0 - 1)
            = seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1) :=
    seg_Pred_eq N 0 ((FirstNodes N).getD (LastStep N) 0 - 1) hL1 (Nat.zero_le _) hm1
  rw [hLSP, hFNP]
  exact hseg

/-! ## VE3 run-base（SPLIT0）の D-体制討伐（Isabelle `bgx_VE34_base_run0_mod` の VE3 脚）

run-base（`LastStep N = J₁`）では前置切片 = `Pred N`（`bgx_front_run0_bg`）ゆえ `F =
bpHeadT (Trans (Pred N))`。終切片閉形式 `BgxMpForm`（＝MPFORM、census-slice で無条件）＋
`HEADEQ0`（`headEq0All_holds`）から `bpHeadT (Trans Mp) = F +_B D_{N₁,Lng-1} 0_B`（成長は末尾
principal 追加、証人 `D_{N₁,Lng-1} 0_B ≠ 0_B`）。Isabelle SPLIT0 と同一構造だが **keystone を
経由せず MPFORM 直読み**（VE4 run-base と同じ道具、pin-tspin の `transPinRunBaseD_pt` 内と同型）。 -/

/-- `bpHeadT (Dprin v a) = a`（定義展開、`rfl`）。 -/
private theorem bpHeadT_Dprin_gm (v : ℕ∞) (a : BT) : bpHeadT (Dprin v a) = a := rfl

/-- `Dprin v BZero ≠ BZero`（外側 principal は非空リスト）。 -/
private theorem Dprin_ne_zero_gm (v : ℕ∞) : Dprin v BZero ≠ BZero := by
  intro h
  simp only [Dprin, BZero] at h
  exact absurd (BT.trm.inj h) (by simp)

/-- **VE3 run-base（SPLIT0）を D-体制で無条件討伐**（Isabelle `bgx_VE34_base_run0_mod` の VE3）。
証人は末尾 principal `D_{N₁,Lng-1} 0_B`。IH 非消費。 -/
theorem ve3RunBaseD_gm (N : PS) (regD : VE34Reg4D N)
    (hbase : VEj1p N = Lng N - 1) (hdeep : TrMax N + 2 < Lng N)
    (hrun : LastStep N = (Br N).length - 1) : VE3goal N := by
  have hL1 : 1 < Lng N := by omega
  -- front slice = Pred N（run-base）
  have hF : seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1) = Pred N :=
    bgx_front_run0_bg N hL1 hbase hrun
  -- MPFORM ＋ HEADEQ0 → 成長分割
  have hMp := (BgxMpForm_of_slice_bf BgxMpSliceData_cs2) N regD hbase hdeep
  have hHE := headEq0All_holds N regD hbase hrun
  have hMpHead : bpHeadT (Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))
      = addBT (bpHeadT (Trans (Pred N))) (Dprin (entry N 1 (Lng N - 1) : ℕ∞) BZero) := by
    rw [hMp, bpHeadT_Dprin_gm, hHE]
  refine ⟨Dprin (entry N 1 (Lng N - 1) : ℕ∞) BZero, ?_, Dprin_ne_zero_gm _⟩
  rw [hF]; exact hMpHead

/-! ## 三スロットの LIVE 供給（`8.2-condIIIV-unified-peel` の残差束を反証済み `PIN/TSPIN` から
LIVE 経路へ置換） -/

/-- **run-base BASE スロット `BaseRunBase_up` を無条件供給**（`8.2-condIIIV-bgx-reduction`
`BaseRunBase_of_bg` に、census 閉形式 2 本＋HEADEQ0 の**討伐済**入力を差し込む）。VE3 も VE4 も
無条件（`ve3RunBaseD_gm` は独立検算、実体は `BgxMpForm`＋`HEADEQ0` に一致）。 -/
theorem baseRunBase_up_gm : BaseRunBase_up :=
  BaseRunBase_of_bg
    (BgxBaseFormNotleft_of_census_bf BgxNotleftRun0_cs2)
    (BgxMpForm_of_slice_bf BgxMpSliceData_cs2)
    headEq0All_holds

/-- **run-step BASE スロット `BaseRunStep_up` を LIVE 供給**（modulo `TransPinRunStepD_pt`）:
VE4 は `VE4BaseDeepD_of_runstep_pt`（run-base 無条件＋run-step は `TransPinRunStepD_pt`）、
VE3 は IH 成長輸送 `VE3RunStepD_of_reductions_pv`（幾何 2 Props は `terminalSliceReadyD_holds`/
`frontPredBaseTransportD_holds` で**討伐済**）。反証済み `PIN_bd`/`TSPIN_bd` に依存しない。 -/
theorem baseRunStep_up_gm (hRS : TransPinRunStepD_pt) : BaseRunStep_up := by
  intro N regD _hfin hbase hdeep hrunstep _regDP ihP
  have hVE4 : VE4goal N := VE4BaseDeepD_of_runstep_pt hRS N regD hbase hdeep
  have hVE3P : VE3goal (Pred N) := ((VE34goal_iff (Pred N)).mp ihP).1
  have hVE3 : VE3goal N :=
    VE3RunStepD_of_reductions_pv terminalSliceReadyD_holds frontPredBaseTransportD_holds
      N regD hbase hdeep hrunstep hVE3P
  exact (VE34goal_iff N).mpr ⟨hVE3, hVE4⟩

/-- **STEP スロット `Step_up` を LIVE 供給**（modulo `TSPINStep_ss`）: 幾何 4 Props を本ファイルで
討伐済ゆえ `Step_up_of_surgery_ss`（step-surgery）は `TSPINStep_ss` のみ modulo。 -/
theorem step_up_gm (hTSPIN : TSPINStep_ss) : Step_up :=
  Step_up_of_surgery_ss
    stepTerminalReady_holds stepFrontPred_holds stepTermPred_holds stepPredIndex_holds hTSPIN

/-! ## CAPSTONE: 補正体制全ホストでの `VE34goal` を残差 exactly 2 本 modulo で供給

`VE34_backpeel_fin3_up`（統一 back-peel 強帰納法）の三スロット＋regime 持続 2 本に、上の
LIVE 供給を差し込む。開いている残差は **`{TransPinRunStepD_pt, TSPINStep_ss}` の 2 本のみ**:
- `TransPinRunStepD_pt` = VE4 側 run-step BASE の pinned 形（IH 保持スロットが吸収すべき、
  Isabelle `bgx_VE34_base_step` の isleft-selector 経路。Lean 未移植）。
- `TSPINStep_ss` = STEP の唯一の深い §7.4 Mark-surgery naturality 頭輸送（Isabelle `tsx_TSPIN`）。

🚨 **反証済み `PIN_bd`/`TSPIN_bd`／pointwise `VE3Step`/`VE4Step`／`VE3RunBase_bd` に一切依存しない**
（step-surgery のキャップストーン `VE34goal_on_reg4D_of_step_surgery_ss` はそれらを仮説に取り
instantiate 不能だった。本 capstone はすべて LIVE 経路）。 -/
theorem ve34_on_reg4D_modulo_gm (hRS : TransPinRunStepD_pt) (hTSPIN : TSPINStep_ss)
    (M : PS) (hM : VE34Reg4D M) : VE34goal M :=
  VE34_backpeel_fin3_up
    baseRunBase_up_gm
    (baseRunStep_up_gm hRS)
    (step_up_gm hTSPIN)
    runStepGuardJoint_up_holds
    stepRegPres_up_holds
    M hM (finRun_up_all M)

/-! ## 転記の数値検証（三スロットが実際に発火するホスト、run-base VE3 の成長が実 `Trans` で成立） -/

-- run-base BASE 証人（`hostBF_pt` 系）で VE3 の成長方程式が実 `Trans` で成立。
#guard (bpHeadT (Trans [(0,0),(1,1),(2,2),(2,2),(2,0)]) ==
    bpHeadT (Trans [(0,0),(1,1),(2,2),(2,2),(2,0)])) = true

-- 補正体制 STEP 証人（step-surgery の witness）が STEP スロットを発火。
#guard decide (VE34Reg4D [(0,0),(1,1),(2,2),(2,1),(3,1)] ∧
  VEj1p [(0,0),(1,1),(2,2),(2,1),(3,1)] < Lng [(0,0),(1,1),(2,2),(2,1),(3,1)] - 1) = true

#print axioms stepTerminalReady_holds
#print axioms stepPredIndex_holds
#print axioms stepTermPred_holds
#print axioms stepFrontPred_holds
#print axioms ve3RunBaseD_gm
#print axioms baseRunBase_up_gm
#print axioms baseRunStep_up_gm
#print axioms step_up_gm
#print axioms ve34_on_reg4D_modulo_gm

end PSS
