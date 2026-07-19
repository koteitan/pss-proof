import «8».«8.2-condIIIV-unified-peel»

/-!
# §8.2 条件(II)/(IV) VE34 統一 back-peel — **regime 持続の 2 残差討伐**

`8.2-condIIIV-unified-peel` の統一強帰納法 `VE34_backpeel_fin3_up` は、補正体制
`VE34Reg4D`（＝Isabelle `vg7x_reg4 = vg4x_reg4 ∧ descending (Br)`）の持続を 2 本の残差に
分けて仮定していた。本ファイルはその両方を無条件で討伐する:

1. **`StepRegPres_up`**（＝Isabelle `vg7x_RPERS`, `layerB/pss_wip.thy:97463`）— STEP ホスト
   （`VEj1p N < Lng N - 1`）で `VE34Reg4D` が `Pred N` に遺伝する。枝数保存の run-peel。
   `vg4x_reg4` 半（guard/joint 境界）は最終枝が非単項ゆえ枝数が保存され、`FirstNodes`/`Joints`
   の輸送（`FirstNodes_Pred_core`/`Joints_Pred_core`）＋`entry_Pred` で最終添字上に持ち上がる。
   `descending` 半は `descending_Br_Pred` 直撃。

2. **`RunStepGuardJoint_up`**（＝Isabelle `bfx_gtP_base`＝guard／`bfx_Joints_Pred_last`＝joint
   境界, `layerB/pss_wip.thy:104809`/`104946`）— BASE run-step ホスト
   （`VEj1p N = Lng N - 1`, `TrMax N + 2 < Lng N`, `LastStep N < (Br N).length - 1`）で、
   最終枝が単項ゆえ `Pred N` は最終枝を丸ごと落とし枝が 1 本減る。生き残る最終枝は host の
   前枝（`J₁-1`）なので、その guard／joint 境界を移す。guard は **run 前枝ガード**
   `bfx_run_prev(2)`（descending の tie-break squeeze）、joint は **JEQ** `bfx_JEQ`
   （run 枝の joint 共有＝`nextR` 一意性）。**旧 4 連言の第 4（BASE 保存）は反証済み
   （Wave AM）ゆえ本ファイルの 3 連言には含めない**。ve-next の `RunSqueeze_vn` 経由の還元は
   その第 3 連言（単一列幾何）が反証済みなので使わず、`bfx_run_prev`＋`bfx_JEQ` を直接移植する。

## 移植したブリック（private suffix `_rp3`）

- `lastBr_len_rp3`（最終枝長＝`Lng N - VEj1p N`）／`a1_FN_lt_rp3`（`a1_FN_lt`）／
  `gtN_rp3`（`bfx_gtN`：最終枝頭は狭義ガード）／`descend_cdom_rp3`（`descending_def` の
  row-0 単調＋row-1 tie-break）／`lastStep_mem_rp3`（`LastStep N ∈ S`）／
  `run_prev_rp3`（`bfx_run_prev`）／`jeq_rp3`（`bfx_JEQ`）。

これらはいずれも `8.2-condIIIV-headeq0-close` の private `_h0` ブリック群および
`8.2-strongmono-props`／`6.5-Red-Pred-commute` の公開補題からの再導出で、keystone 非依存。

- 訂正: なし（Isabelle 済補題の逐語移植）。
- 状態: ✅（sorry 0, rc=0）。`StepRegPres_up` と `RunStepGuardJoint_up` を無条件討伐。
- 依存 module: `8.2-condIIIV-unified-peel`。
- Private suffix: `_rp3`。
-/

namespace PSS

/-! ## 共通補助（suffix `_rp3`） -/

/-- **最終枝の長さ**（`wf21_Br_eq_seg` の読み出し）: `Lng ((Br N).getLastD []) = Lng N - VEj1p N`。
BASE（`VEj1p = Lng N - 1`）で長さ 1、STEP（`VEj1p < Lng N - 1`）で長さ ≥ 2。 -/
private theorem lastBr_len_rp3 (N : PS) (hM : TPS N) (hBrne : Br N ≠ []) :
    Lng ((Br N).getLastD []) = Lng N - VEj1p N := by
  have hpos : 0 < Lng N := List.length_pos_of_ne_nil hM
  rw [getLastD_eq_getD_last_68 (Br N) [] hBrne, wf21_Br_eq_seg N hM hBrne, length_seg]
  simp only [VEj1p]
  omega

/-! ## `StepRegPres_up`（Isabelle `vg7x_RPERS`） -/

/-- **STEP regime 持続**（Isabelle `vg7x_RPERS`）: STEP ホスト（`VEj1p N < Lng N - 1`）で補正体制
`VE34Reg4D` が `Pred N` に遺伝する。最終枝が非単項ゆえ枝数保存、`FirstNodes`/`Joints` を最終添字で
輸送し guard/joint を持ち上げ、`descending` は `descending_Br_Pred`。 -/
theorem stepRegPres_up_holds : StepRegPres_up := by
  intro N regD hstep
  obtain ⟨reg4, hdesc⟩ := regD
  obtain ⟨reg3, hj0pos, hj0lt⟩ := reg4
  obtain ⟨reg, hguard⟩ := reg3
  obtain ⟨hR, hmono, hBrne⟩ := reg
  have hM : TPS N := RTPS_TPS N hR
  have hBrpos : 0 < (Br N).length := List.length_pos_of_ne_nil hBrne
  have hJ1lt : (Br N).length - 1 < (Br N).length := by omega
  -- geometry: TrMax N < VEj1p N
  have hgeom : TrMax N < (FirstNodes N).getD ((Br N).length - 1) 0 :=
    (FirstNodes_TrMax_Joints N ((Br N).length - 1) hM hmono hJ1lt).2
  have hgeom' : TrMax N < VEj1p N := by simpa only [VEj1p] using hgeom
  have hL1 : 1 < Lng N := by omega
  have htrne : TrMax N ≠ Lng N - 1 := by omega
  have hLP : Lng (Pred N) = Lng N - 1 := length_Pred N hL1
  have hLPgt : 1 < Lng (Pred N) := by omega
  have hTrP : TrMax (Pred N) = TrMax N := TrMax_Pred_nontrunk N hM hL1 htrne
  -- DTPS (Pred N) : RTPS / monoT / descending 半
  have hDN : DTPS N := (DTPS_iff N).mpr ⟨hR, hmono, hdesc⟩
  have hDQ : DTPS (Pred N) := descending_Br_Pred N hDN hBrne hLPgt
  obtain ⟨hRQ, hmonoQ, hdescQ⟩ := (DTPS_iff (Pred N)).mp hDQ
  -- 枝数保存（STEP: 最終枝は長さ ≥ 2）
  have hlastlen : Lng ((Br N).getLastD []) = Lng N - VEj1p N := lastBr_len_rp3 N hM hBrne
  have hlastgt : 1 < Lng ((Br N).getLastD []) := by rw [hlastlen]; omega
  have hBrlenP : (Br (Pred N)).length = (Br N).length := by
    rw [Br_Pred_core_nontrunk N hM hL1 htrne,
      if_neg (show ¬ Lng ((Br N).getLastD []) ≤ 1 by omega),
      List.length_append, List.length_dropLast, List.length_singleton]
    omega
  have hBrQne : Br (Pred N) ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hBrlenP]; omega)
  have hidxP : (Br (Pred N)).length - 1 = (Br N).length - 1 := by rw [hBrlenP]
  have hJlt : (Br N).length - 1 < (Br (Pred N)).length := by rw [hBrlenP]; omega
  -- VEj1p (Pred N) = VEj1p N
  have hVEjP : VEj1p (Pred N) = VEj1p N := by
    show (FirstNodes (Pred N)).getD ((Br (Pred N)).length - 1) 0
       = (FirstNodes N).getD ((Br N).length - 1) 0
    rw [hidxP, FirstNodes_Pred_core N hM hL1 htrne ((Br N).length - 1) hJlt]
  -- guard 持続
  have hguardP : entry (Pred N) 1 (VEj1p (Pred N)) < entry (Pred N) 0 (VEj1p (Pred N)) := by
    rw [hVEjP, entry_Pred N 1 (VEj1p N) hstep, entry_Pred N 0 (VEj1p N) hstep]
    exact hguard
  -- joint 持続
  have hjointP : (Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0
      = (Joints N).getD ((Br N).length - 1) 0 := by
    rw [hidxP, Joints_Pred_core N hM hmono hL1 htrne ((Br N).length - 1) hJlt]
  have hjposP : 0 < (Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0 := by
    rw [hjointP]; exact hj0pos
  have hjltP : (Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0 < TrMax (Pred N) := by
    rw [hjointP, hTrP]; exact hj0lt
  exact ⟨⟨⟨⟨hRQ, hmonoQ, hBrQne⟩, hguardP⟩, hjposP, hjltP⟩, hdescQ⟩

/-! ## `RunStepGuardJoint_up` の run-peel 幾何（Isabelle `bfx_run_prev`＋`bfx_JEQ`）

BASE run-step ホストの run 前枝（`J₁-1`）を扱う純幾何。keystone 非依存。 -/

/-- Isabelle `a1_FN_lt`: 枝の first node は範囲内 `< Lng M`（`Joints_nextR_FirstNodes` から）。 -/
private theorem a1_FN_lt_rp3 (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) : (FirstNodes M).getD J 0 < Lng M := by
  have hnx := Joints_nextR_FirstNodes M J hM hmono hJ
  have hn0 : nextrel0 M ((Joints M).getD J 0) ((FirstNodes M).getD J 0) = true := by
    simpa [nextR] using hnx
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hn0
  exact hn0.1.1.1.2

/-- Isabelle `bfx_gtN`: 最終枝頭は狭義ガード（体制 guard の枝成分表示）。 -/
private theorem gtN_rp3 (N : PS) (hR : RTPS N) (hBrne : Br N ≠ [])
    (hguard : entry N 1 (VEj1p N) < entry N 0 (VEj1p N)) :
    entry ((Br N).getD ((Br N).length - 1) []) 1 0
      < entry ((Br N).getD ((Br N).length - 1) []) 0 0 := by
  have hM : TPS N := RTPS_TPS N hR
  have hJ1lt : (Br N).length - 1 < (Br N).length := by
    have := List.length_pos_of_ne_nil hBrne; omega
  have h0 := entry_FirstNodes_eq_component_mr N ((Br N).length - 1) 0 hM hJ1lt
  have h1 := entry_FirstNodes_eq_component_mr N ((Br N).length - 1) 1 hM hJ1lt
  rw [← h0, ← h1]
  simpa only [VEj1p] using hguard

/-- `descending (Br N)`（`descendingB … = true`）の 2 成分: row-0 広義単調減少と、row-0 同点なら
row-1 も広義単調減少（`cdomB` の tie-break）。 -/
private theorem descend_cdom_rp3 (Q : List PS) (h : descendingB Q = true)
    (J₀ J₁ : ℕ) (hle : J₀ ≤ J₁) (hlt : J₁ < Q.length) :
    entry (Q.getD J₁ []) 0 0 ≤ entry (Q.getD J₀ []) 0 0
    ∧ (entry (Q.getD J₀ []) 0 0 = entry (Q.getD J₁ []) 0 0 →
        entry (Q.getD J₁ []) 1 0 ≤ entry (Q.getD J₀ []) 1 0) := by
  simp only [descendingB, List.all_eq_true, List.mem_range] at h
  have hc := h J₁ hlt J₀ (by omega)
  simp only [cdomB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', beq_eq_false_iff_ne] at hc
  refine ⟨hc.1, ?_⟩
  intro heq
  rcases hc.2 with hne | hle1
  · exact absurd heq hne
  · exact hle1

/-- **`LastStep N ∈ S`**: 最終枝が狭義ガード（`hgtN`）のとき、`LastStep N` 番目の枝は
`S`-述語（最終枝と同 row-0 枝頭 ∧ row-1 < row-0）を満たす。`8.2-condIIIV-deep3` の全域
`LastStep`（`find?`＋既定値 `J₁`）の membership 版。 -/
private theorem lastStep_mem_rp3 (M : PS) (hBrne : Br M ≠ [])
    (hgtN : entry ((Br M).getD ((Br M).length - 1) []) 1 0
          < entry ((Br M).getD ((Br M).length - 1) []) 0 0) :
    entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD (LastStep M) []) 0 0
    ∧ entry ((Br M).getD (LastStep M) []) 1 0 < entry ((Br M).getD (LastStep M) []) 0 0 := by
  have hLpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hL : (Br M).length ≠ 0 := by omega
  have hnd : entry ((Br M).getD ((Br M).length - 1) []) 0 0
           ≠ entry ((Br M).getD ((Br M).length - 1) []) 1 0 := by omega
  have hLSval : LastStep M = ((List.range (Br M).length).find? (fun J =>
      decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD J []) 0 0) &&
      decide (entry ((Br M).getD J []) 1 0 < entry ((Br M).getD J []) 0 0))).getD
        ((Br M).length - 1) := by
    unfold LastStep
    simp only [hL, if_false]
    split
    · next heq => exact absurd heq hnd
    · rfl
  cases hfind : (List.range (Br M).length).find? (fun J =>
      decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD J []) 0 0) &&
      decide (entry ((Br M).getD J []) 1 0 < entry ((Br M).getD J []) 0 0)) with
  | none =>
      rw [hLSval, hfind, Option.getD_none]
      exact ⟨rfl, hgtN⟩
  | some c =>
      rw [hLSval, hfind, Option.getD_some]
      have hp := List.find?_some hfind
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
      exact hp

/-- **`bfx_run_prev`**: run（`LastStep N < J₁`）で前枝（`J₁-1`）は最終枝と同 row-0 枝頭を持ち
（descending の squeeze で `LastStep ≤ J₁-1 ≤ J₁` を挟む）、それ自身が狭義ガード
（`LastStep ∈ S` の row-1 < row-0 が tie-break で前枝に伝わる）。 -/
private theorem run_prev_rp3 (N : PS) (hR : RTPS N) (hBrne : Br N ≠ [])
    (hdesc : descendingB (Br N) = true)
    (hguard : entry N 1 (VEj1p N) < entry N 0 (VEj1p N))
    (hrun : LastStep N < (Br N).length - 1) :
    entry ((Br N).getD ((Br N).length - 2) []) 0 0 = entry ((Br N).getD ((Br N).length - 1) []) 0 0
    ∧ entry ((Br N).getD ((Br N).length - 2) []) 1 0
        < entry ((Br N).getD ((Br N).length - 2) []) 0 0 := by
  have hBrpos : 0 < (Br N).length := List.length_pos_of_ne_nil hBrne
  have hLSlt : LastStep N < (Br N).length := LastStep_lt_Lng_Br N hBrne
  have hgtN := gtN_rp3 N hR hBrne hguard
  obtain ⟨hLS0, hLS1⟩ := lastStep_mem_rp3 N hBrne hgtN
  have hLSle : LastStep N ≤ (Br N).length - 2 := by omega
  have hJmle : (Br N).length - 2 ≤ (Br N).length - 1 := by omega
  have hJ1lt : (Br N).length - 1 < (Br N).length := by omega
  obtain ⟨d1a, d1b⟩ :=
    descend_cdom_rp3 (Br N) hdesc (LastStep N) ((Br N).length - 2) hLSle (by omega)
  obtain ⟨d2a, _⟩ :=
    descend_cdom_rp3 (Br N) hdesc ((Br N).length - 2) ((Br N).length - 1) hJmle hJ1lt
  have h0eq : entry ((Br N).getD ((Br N).length - 2) []) 0 0
            = entry ((Br N).getD ((Br N).length - 1) []) 0 0 := by omega
  refine ⟨h0eq, ?_⟩
  have hLSeqJm : entry ((Br N).getD (LastStep N) []) 0 0
              = entry ((Br N).getD ((Br N).length - 2) []) 0 0 := by omega
  have tie : entry ((Br N).getD ((Br N).length - 2) []) 1 0
           ≤ entry ((Br N).getD (LastStep N) []) 1 0 := d1b hLSeqJm
  omega

/-- **`bfx_JEQ`**: run 枝は joint を共有 — `Joints N ! (J₁-2) = Joints N ! (J₁-1)`。前枝と最終枝の
row-0 枝頭が一致する（`run_prev`）ので、`j₀ = Joints N ! (J₁-1)` は前枝 first node の `nextR` 親でも
あり（`nextrel0` の valley を FirstNodes 単調で部分区間に制限）、row-0 親の一意性で joint が一致。 -/
private theorem jeq_rp3 (N : PS) (hR : RTPS N) (hmono : monoT N = true) (hBrne : Br N ≠ [])
    (hdesc : descendingB (Br N) = true)
    (hguard : entry N 1 (VEj1p N) < entry N 0 (VEj1p N))
    (hj0lt : (Joints N).getD ((Br N).length - 1) 0 < TrMax N)
    (hrun : LastStep N < (Br N).length - 1) :
    (Joints N).getD ((Br N).length - 2) 0 = (Joints N).getD ((Br N).length - 1) 0 := by
  have hM : TPS N := RTPS_TPS N hR
  have hBrpos : 0 < (Br N).length := List.length_pos_of_ne_nil hBrne
  have hJmlt : (Br N).length - 2 < (Br N).length := by omega
  have hJ1lt : (Br N).length - 1 < (Br N).length := by omega
  -- run_prev(1): row-0 枝頭一致 → entry N 0 (FN_{J₁-2}) = entry N 0 (FN_{J₁-1})
  obtain ⟨hrp0, _⟩ := run_prev_rp3 N hR hBrne hdesc hguard hrun
  have hcompM := entry_FirstNodes_eq_component_mr N ((Br N).length - 2) 0 hM hJmlt
  have hcomp1 := entry_FirstNodes_eq_component_mr N ((Br N).length - 1) 0 hM hJ1lt
  have heqFN : entry N 0 ((FirstNodes N).getD ((Br N).length - 2) 0)
             = entry N 0 ((FirstNodes N).getD ((Br N).length - 1) 0) := by
    rw [hcompM, hcomp1]; exact hrp0
  -- nx1 : nextrel0 N j₀ (FN_{J₁-1})
  have hnx1 : nextR N 0 ((Joints N).getD ((Br N).length - 1) 0)
      ((FirstNodes N).getD ((Br N).length - 1) 0) = true :=
    Joints_nextR_FirstNodes N ((Br N).length - 1) hM hmono hJ1lt
  have hn1 : nextrel0 N ((Joints N).getD ((Br N).length - 1) 0)
      ((FirstNodes N).getD ((Br N).length - 1) 0) = true := by simpa [nextR] using hnx1
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hn1
  obtain ⟨⟨⟨⟨hj0Lng, hfn1Lng⟩, _hj0fn1⟩, he0lt⟩, hvalley⟩ := hn1
  -- geometry: j₀ < TrMax N < FN_{J₁-2}, FN_{J₁-2} ≤ FN_{J₁-1}, FN_{J₁-2} < Lng N
  have hgeomJm := FirstNodes_TrMax_Joints N ((Br N).length - 2) hM hmono hJmlt
  have hfnmlt : (FirstNodes N).getD ((Br N).length - 2) 0 < Lng N :=
    a1_FN_lt_rp3 N ((Br N).length - 2) hM hmono hJmlt
  have hfnmono := (FirstNodes_Joints_mono N ((Br N).length - 2) ((Br N).length - 1)
    hM hmono (by omega) hJ1lt).1
  -- build nextrel0 N j₀ (FN_{J₁-2})
  have hbuild : nextrel0 N ((Joints N).getD ((Br N).length - 1) 0)
      ((FirstNodes N).getD ((Br N).length - 2) 0) = true := by
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨hj0Lng, hfnmlt⟩, ?_⟩, ?_⟩, ?_⟩
    · omega
    · rw [heqFN]; exact he0lt
    · intro j hjlt
      by_cases hj0j : (Joints N).getD ((Br N).length - 1) 0 < j
      · have hjfn1 : j < (FirstNodes N).getD ((Br N).length - 1) 0 := by omega
        have hv := hvalley j (List.mem_range.mpr hjfn1)
        rw [decide_eq_true_eq.mpr hj0j] at hv
        simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hv
        have hle : entry N 0 ((FirstNodes N).getD ((Br N).length - 2) 0) ≤ entry N 0 j := by
          rw [heqFN]; exact hv
        simp only [decide_eq_true_eq.mpr hle, Bool.or_true]
      · simp only [decide_eq_false_iff_not.mpr hj0j, Bool.not_false, Bool.true_or]
  have hnxm : nextR N 0 ((Joints N).getD ((Br N).length - 1) 0)
      ((FirstNodes N).getD ((Br N).length - 2) 0) = true := by simpa [nextR] using hbuild
  have hnxm0 : nextR N 0 ((Joints N).getD ((Br N).length - 2) 0)
      ((FirstNodes N).getD ((Br N).length - 2) 0) = true :=
    Joints_nextR_FirstNodes N ((Br N).length - 2) hM hmono hJmlt
  exact (row0_parent_unique N ((Joints N).getD ((Br N).length - 1) 0)
    ((Joints N).getD ((Br N).length - 2) 0) ((FirstNodes N).getD ((Br N).length - 2) 0)
    hnxm hnxm0).symm

/-! ## `RunStepGuardJoint_up`（Isabelle `bfx_gtP_base`＋`bfx_Joints_Pred_last`） -/

/-- **run-step BASE の guard/joint 持続**（Isabelle `bfx_gtP_base`＝guard／
`bfx_Joints_Pred_last`＝joint 境界）。BASE では最終枝が単項ゆえ `Pred N` は最終枝を落とし枝が
1 本減り、生き残る最終枝は host 前枝（`J₁-1`）。その guard は `bfx_run_prev(2)`、joint は
`bfx_JEQ`＋輸送で移す。**BASE 保存（反証済み）は含まない**。 -/
theorem runStepGuardJoint_up_holds : RunStepGuardJoint_up := by
  intro N regD hbase hdeep hrun
  obtain ⟨reg4, hdesc⟩ := regD
  obtain ⟨reg3, hj0pos, hj0lt⟩ := reg4
  obtain ⟨reg, hguard⟩ := reg3
  obtain ⟨hR, hmono, hBrne⟩ := reg
  have hM : TPS N := RTPS_TPS N hR
  have hL1 : 1 < Lng N := by omega
  have htrne : TrMax N ≠ Lng N - 1 := by omega
  have hLP : Lng (Pred N) = Lng N - 1 := length_Pred N hL1
  have hLPgt : 1 < Lng (Pred N) := by omega
  have hTrP : TrMax (Pred N) = TrMax N := TrMax_Pred_nontrunk N hM hL1 htrne
  have hBrpos : 0 < (Br N).length := List.length_pos_of_ne_nil hBrne
  have hBrge2 : 2 ≤ (Br N).length := by omega
  -- BASE: 最終枝は単項 → 枝数が 1 本減る
  have hlastsing : Lng ((Br N).getLastD []) = 1 := by
    rw [lastBr_len_rp3 N hM hBrne]; omega
  have hBrlenP : (Br (Pred N)).length = (Br N).length - 1 := by
    rw [Br_Pred_core_nontrunk N hM hL1 htrne, if_pos (le_of_eq hlastsing)]
    simp
  have hidx : (Br (Pred N)).length - 1 = (Br N).length - 2 := by omega
  have hJpP : (Br N).length - 2 < (Br (Pred N)).length := by omega
  -- DTPS (Pred N)（monoT/RTPS: Pred N への a1_FN_lt 用）
  have hDN : DTPS N := (DTPS_iff N).mpr ⟨hR, hmono, hdesc⟩
  have hDQ : DTPS (Pred N) := descending_Br_Pred N hDN hBrne hLPgt
  obtain ⟨hRQ, hmonoQ, _hdescQ⟩ := (DTPS_iff (Pred N)).mp hDQ
  have hMQ : TPS (Pred N) := RTPS_TPS (Pred N) hRQ
  -- VEj1p (Pred N) = FirstNodes N ! (J₁-2)（前枝の左端）
  have hVEjP : VEj1p (Pred N) = (FirstNodes N).getD ((Br N).length - 2) 0 := by
    show (FirstNodes (Pred N)).getD ((Br (Pred N)).length - 1) 0
       = (FirstNodes N).getD ((Br N).length - 2) 0
    rw [hidx, FirstNodes_Pred_core N hM hL1 htrne ((Br N).length - 2) hJpP]
  -- 前枝左端 < Lng N - 1（`entry_Pred` 用）: a1_FN_lt を Pred N に適用
  have hjmltQ : (FirstNodes (Pred N)).getD ((Br (Pred N)).length - 1) 0 < Lng (Pred N) :=
    a1_FN_lt_rp3 (Pred N) ((Br (Pred N)).length - 1) hMQ hmonoQ (by omega)
  have hjmlt : (FirstNodes N).getD ((Br N).length - 2) 0 < Lng N - 1 := by
    rw [hidx, FirstNodes_Pred_core N hM hL1 htrne ((Br N).length - 2) hJpP, hLP] at hjmltQ
    exact hjmltQ
  -- run 前枝ガード（guard 半）
  obtain ⟨_hrp0, hrp1⟩ := run_prev_rp3 N hR hBrne hdesc hguard hrun
  -- JEQ（joint 半）
  have hjeq : (Joints N).getD ((Br N).length - 2) 0 = (Joints N).getD ((Br N).length - 1) 0 :=
    jeq_rp3 N hR hmono hBrne hdesc hguard hj0lt hrun
  have hjointP : (Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0
      = (Joints N).getD ((Br N).length - 1) 0 := by
    rw [hidx, Joints_Pred_core N hM hmono hL1 htrne ((Br N).length - 2) hJpP, hjeq]
  refine ⟨?_, ?_, ?_⟩
  · -- (1) guard on Pred N: entry_Pred 転送 → run 前枝ガード（枝成分表示）
    rw [hVEjP, entry_Pred N 1 _ hjmlt, entry_Pred N 0 _ hjmlt]
    have hc0 := entry_FirstNodes_eq_component_mr N ((Br N).length - 2) 0 hM (by omega)
    have hc1 := entry_FirstNodes_eq_component_mr N ((Br N).length - 2) 1 hM (by omega)
    rw [hc0, hc1]; exact hrp1
  · -- (2) joint 正
    rw [hjointP]; exact hj0pos
  · -- (3) joint < TrMax (Pred N)
    rw [hjointP, hTrP]; exact hj0lt

#print axioms stepRegPres_up_holds
#print axioms runStepGuardJoint_up_holds

end PSS
