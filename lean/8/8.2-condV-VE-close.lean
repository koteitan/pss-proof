import «8».«8.2-condV-VE-step»
import «8».«8.2-condV-VE-base2»
import «8».«8.2-strongmono-props»

/-!
# §8.2 値方程式 `VE` キャンペーンの締め: `RPj1eq` 残差の閉包

- 原文: `tmp/content.md` L3664 付近の補題（条件(V)下の終切片と `Trans` の関係）の
  証明中、原文が省略している後ろ剥がし帰納法（`vbax_VE_backpeel`, `VE_backpeel_TrMax`）の
  `j₁' = j₁` 体制遺伝ステップ（RPERS の稀な分岐）。
- 訂正: なし（Isabelle 側で無条件に証明済みの補題の逐語移植）。
- Isabelle (`isabelle/layerB/pss_wip.thy`):
  - `vjx_RPj1eq` (74726) → `rpj1eq_vc`（本ファイルで `RPj1eqResidual m` を **無条件で** 閉じる）。
  - `vcx_VE_all` (77076) の骨格 → `vcx_VE_all_modRPclosed`（`RPj1eq` を除去した front-facing 版）。
    Isabelle は同じ組み立てで、`BASE`/`STEP`/`RPERS` の残る三本も無条件に閉じている。
- 依存: `8.2-condV-VE-step`（`VEReg`/`VEeq`/`VEj1p` 語彙、残差 Props、`vsx_VE_all_modResidual`）、
  `8.2-condV-VE-base2`（`a0x_base_VE_vb2` による BASE 脚の分解）、
  `8.2-strongmono-props`（`descending_Br_Pred`／`Br_Pred_core_nontrunk`／`wf21_Br_eq_seg`／
  `FirstNodes_Pred_core`／`Joints_Pred_core`／`entry_Pred`／`FirstNodes_Joints_mono`／
  `reduced_coeff`／`RedCondA_apply`／`mono_hasParent_row0`／`cdomB_iff`／`descendingB_iff`／
  `entry_FirstNodes_eq_component_mr`／`RTPS_Pred`／`nonmulti_Pred` などの幾何補題を推移的に供給）。
- 方針: Isabelle `vjx_RPj1eq` と同じ。最終枝が単一列（`j₁' = j₁`）の regime では
  `Pred N` は最終列を落とすので枝数が一つ減る（`(Br (Pred N)).length = (Br N).length - 1`）。
  体制 `m`-条件を `JP = (Br (Pred N)).length - 1 = J₁ - 1` に輸送する。
  * `m < Joints N ! J₁` 枝: joint 単調性で `m < Joints (Pred N) ! JP`（左選言）。
  * `m = Joints N ! J₁ ∧ descending` 枝: `Joints ! JP = Joints ! J₁` の境界で
    対角性を squeeze（`condA` の joint+1 恒等式／`descending` の `cdom`／`reduced_coeff`／
    `entry_Pred` 輸送）して右選言。`descendingB (Br (Pred N))` は `descending_Br_Pred`。
- 状態: ⚠️ 部分（sorry 0、rc=0）。`RPj1eqResidual` と `BaseMLtTrMax` は
  **無条件で閉じた**。`vcx_VE_all` の完全無条件化に残るのは深部 surgery ブリック
  {BASE(=`BaseVEAdm0`/`BaseVEStrict`), `BpaxVEstep`, `VEj1eqResidual`,
  `BpaxRPERS`} の四本（いずれも `scb_decomp` surgery を要し、Lean 側に双子が無い）。
-/

namespace PSS

/-! ## 私的補助（suffix `_vc`） -/

/-- `leR M 0 a b` は両添字を `Lng M` 未満に閉じ込める。 -/
private theorem leR0_bounds_vc (M : PS) (a b : ℕ)
    (h : leR M 0 a b = true) : a < Lng M ∧ b < Lng M := by
  have h0 : le0 M a b = true := by simpa [leR] using h
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at h0
  exact ⟨h0.1.1, h0.1.2⟩

/-- Isabelle `wid_FN_Suc_lt` (`layerB/pss_wip.thy:36099`) の再導出: 枝成分は非空なので
`FirstNodes` は狭義単調。 -/
private theorem FN_Suc_lt_vc (M : PS) (hM : TPS M) (J : ℕ)
    (hSuc : J + 1 < (Br M).length) :
    (FirstNodes M).getD J 0 < (FirstNodes M).getD (J + 1) 0 := by
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    rw [show Br M = [] by simp [Br, heq]] at hSuc
    simp at hSuc
  have htb := TrMax_bound M hM
  have hBrseg : Br M = P (seg M (TrMax M + 1) (Lng M - 1)) := by simp [Br, hne]
  have hsegT : TPS (seg M (TrMax M + 1) (Lng M - 1)) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (seg M (TrMax M + 1) (Lng M - 1))
    rw [length_seg]; omega
  have hpos : 0 < Lng ((Br M).getD J []) := by
    rw [hBrseg]
    exact P_component_nonempty _ J hsegT (by rw [← hBrseg]; omega)
  have h1 := FirstNodes_getD M J (by omega)
  have h2 := FirstNodes_getD M (J + 1) hSuc
  have h3 := idxSum_diff (Br M) J (by omega)
  omega

/-! ## `RPj1eq` 残差の閉包（Isabelle `vjx_RPj1eq`, 74726） -/

/-- Isabelle `vjx_RPj1eq` (layerB 74726): `j₁' = j₁` の体制が `Pred N` に遺伝する。
本ファイルはこれを **無条件で** 証明し、残差 Prop `RPj1eqResidual m` を閉じる。 -/
theorem rpj1eq_vc (m : ℕ) : RPj1eqResidual m := by
  intro N reg eqj nonmin
  obtain ⟨hR, hmono, hBrne, hdisj⟩ := reg
  unfold VEj1p at eqj hdisj
  -- 基本量
  have hM : TPS N := RTPS_TPS N hR
  have hBrL : 0 < (Br N).length := List.length_pos_of_ne_nil hBrne
  have hJ1Br : (Br N).length - 1 < (Br N).length := by omega
  have hj1eq : (FirstNodes N).getD ((Br N).length - 1) 0 = Lng N - 1 := eqj
  have hne : TrMax N ≠ Lng N - 1 := fun heq => hBrne (by simp [Br, heq])
  have htb : TrMax N ≤ Lng N - 1 := TrMax_bound N hM
  have htrlt : TrMax N < Lng N - 1 := lt_of_le_of_ne htb hne
  have hL : 1 < Lng N := by omega
  have hLPN : Lng (Pred N) = Lng N - 1 := length_Pred N hL
  -- `1 ≤ J₁`（枝数 ≥ 2）
  have hJ1pos : 1 ≤ (Br N).length - 1 := by
    rcases Nat.eq_zero_or_pos ((Br N).length - 1) with hj10 | hpos
    · exfalso
      have hfn0 : (FirstNodes N).getD 0 0 = TrMax N + 1 := by
        rw [FirstNodes_getD N 0 (by omega)]
        have hs0 : (IdxSum (Br N)).getD 0 0 = 0 := by
          rw [idxSum_getD (Br N) 0 (Nat.zero_le _)]; simp
        omega
      rw [hj10, hfn0] at hj1eq
      omega
    · exact hpos
  have hL1ge2 : 2 ≤ (Br N).length := by omega
  -- (a) `Pred N ∈ RT_PS`
  have predNR : RTPS (Pred N) := RTPS_Pred N hR
  -- (b) `monoT (Pred N)`
  have hmultiN : multiT N = false := by simp [multiT, hmono]
  have hmultiP : multiT (Pred N) = false := nonmulti_Pred N hM hmultiN hL
  have hzP : zeroT (Pred N) = false := by
    have hne1 : Lng (Pred N) ≠ 1 := by rw [hLPN]; omega
    simp [zeroT, hne1]
  have hmonoP : monoT (Pred N) = true := by
    have h := hmultiP; simp [multiT, hzP] at h; exact h
  -- (c) 枝数: 最終列単項なので `(Br (Pred N)).length = (Br N).length - 1`
  have hcore := Br_Pred_core_nontrunk N hM hL hne
  have hlast1 : Lng ((Br N).getLastD []) = 1 := by
    rw [getLastD_eq_getD_last_68 (Br N) [] hBrne, wf21_Br_eq_seg N hM hBrne, length_seg, hj1eq]
    omega
  have hle1 : Lng ((Br N).getLastD []) ≤ 1 := by rw [hlast1]
  rw [if_pos hle1] at hcore
  have hBrP : Br (Pred N) = (Br N).dropLast := by rw [hcore]; simp
  have hBrPlen : (Br (Pred N)).length = (Br N).length - 1 := by
    rw [hBrP, List.length_dropLast]
  have hBrPne : Br (Pred N) ≠ [] := by
    have : 0 < (Br (Pred N)).length := by rw [hBrPlen]; omega
    exact List.ne_nil_of_length_pos this
  -- 添字 `JP = (Br (Pred N)).length - 1 = J₁ - 1`
  have hJBrP : (Br (Pred N)).length - 1 < (Br (Pred N)).length := by omega
  have hJPltN : (Br (Pred N)).length - 1 < (Br N).length := by omega
  have hJPltJ1 : (Br (Pred N)).length - 1 < (Br N).length - 1 := by omega
  have hSucJP : (Br (Pred N)).length - 1 + 1 = (Br N).length - 1 := by omega
  -- Pred 側の `FirstNodes`/`Joints` は `N` 側に一致
  have hFNP : (FirstNodes (Pred N)).getD ((Br (Pred N)).length - 1) 0
            = (FirstNodes N).getD ((Br (Pred N)).length - 1) 0 :=
    FirstNodes_Pred_core N hM hL hne _ hJBrP
  have hJNP : (Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0
            = (Joints N).getD ((Br (Pred N)).length - 1) 0 :=
    Joints_Pred_core N hM hmono hL hne _ hJBrP
  -- joint 単調性: `Joints ! J₁ ≤ Joints ! JP`
  have hmonoJ := FirstNodes_Joints_mono N ((Br (Pred N)).length - 1) ((Br N).length - 1)
      hM hmono hJPltJ1 hJ1Br
  have hJgeJ1 : (Joints N).getD ((Br N).length - 1) 0
              ≤ (Joints N).getD ((Br (Pred N)).length - 1) 0 := hmonoJ.2.1
  -- 条件(A): 各枝で `entry 0 (Joints!J) + 1 = entry 0 (FirstNodes!J)`
  have hA : RedCondA N = true := (RTPS_condAB N hR).1
  have condA_step : ∀ J, J < (Br N).length →
      entry N 0 ((Joints N).getD J 0) + 1 = entry N 0 ((FirstNodes N).getD J 0) := by
    intro J hJ
    have hnx := Joints_nextR_FirstNodes N J hM hmono hJ
    have hfL : (FirstNodes N).getD J 0 < Lng N :=
      (leR0_bounds_vc N _ _ (nextR_implies_row0 N 0 _ _ hnx).2).2
    have hFNpos : 0 < (FirstNodes N).getD J 0 := by
      rw [FirstNodes_getD N J hJ]; omega
    have hpar : (Joints N).getD J 0 = parent N 0 ((FirstNodes N).getD J 0) :=
      Joints_getD N J hJ
    have hp0 : hasParent N 0 ((FirstNodes N).getD J 0) = true :=
      mono_hasParent_row0 N hM hmono _ hFNpos hfL
    have hcondA := RedCondA_apply N hA 0 ((FirstNodes N).getD J 0) (by norm_num) hfL hp0
    rw [← hpar] at hcondA
    exact hcondA
  -- 目標: `VEReg m (Pred N)`
  refine ⟨predNR, hmonoP, hBrPne, ?_⟩
  simp only [VEj1p]
  rw [hFNP, hJNP]
  rcases hdisj with hlt | ⟨hmeq, hdiagj1, hdescB⟩
  · -- `m < Joints ! J₁`: 左選言
    exact Or.inl (lt_of_lt_of_le hlt hJgeJ1)
  · by_cases hlt2 : (Joints N).getD ((Br N).length - 1) 0
        < (Joints N).getD ((Br (Pred N)).length - 1) 0
    · -- `Joints ! J₁ < Joints ! JP`: 左選言
      exact Or.inl (by rw [hmeq]; exact hlt2)
    · -- `Joints ! JP = Joints ! J₁`: 境界 squeeze で右選言
      right
      have hJeqJP : (Joints N).getD ((Br (Pred N)).length - 1) 0
                  = (Joints N).getD ((Br N).length - 1) 0 :=
        le_antisymm (by omega) hJgeJ1
      refine ⟨by rw [hmeq]; exact hJeqJP.symm, ?_, ?_⟩
      · -- 対角性 `entry 0 (FN!JP) = entry 1 (FN!JP)` を Pred N へ輸送
        -- `e0eq : entry 0 (FN!JP) = entry 0 (FN!J₁)`
        have he0eq : entry N 0 ((FirstNodes N).getD ((Br (Pred N)).length - 1) 0)
                   = entry N 0 ((FirstNodes N).getD ((Br N).length - 1) 0) := by
          have hcJP := condA_step ((Br (Pred N)).length - 1) hJPltN
          have hcJ1 := condA_step ((Br N).length - 1) hJ1Br
          rw [← hcJP, ← hcJ1, hJeqJP]
        -- `FN!JP < Lng N - 1`
        have hFNstrict : (FirstNodes N).getD ((Br (Pred N)).length - 1) 0
                       < (FirstNodes N).getD ((Br (Pred N)).length - 1 + 1) 0 :=
          FN_Suc_lt_vc N hM ((Br (Pred N)).length - 1) (by rw [hSucJP]; exact hJ1Br)
        rw [hSucJP, hj1eq] at hFNstrict
        have hfnJPltLast : (FirstNodes N).getD ((Br (Pred N)).length - 1) 0 < Lng N - 1 :=
          hFNstrict
        -- `entry (Pred N) c (FN!JP) = entry N c (FN!JP)`
        have heA0 : entry (Pred N) 0 ((FirstNodes N).getD ((Br (Pred N)).length - 1) 0)
                  = entry N 0 ((FirstNodes N).getD ((Br (Pred N)).length - 1) 0) :=
          entry_Pred N 0 _ hfnJPltLast
        have heA1 : entry (Pred N) 1 ((FirstNodes N).getD ((Br (Pred N)).length - 1) 0)
                  = entry N 1 ((FirstNodes N).getD ((Br (Pred N)).length - 1) 0) :=
          entry_Pred N 1 _ hfnJPltLast
        -- 成分翻訳 `entry N i (FN!J) = entry (Br N ! J) i 0`
        have hcompP0 := entry_FirstNodes_eq_component_mr N ((Br (Pred N)).length - 1) 0 hM hJPltN
        have hcompP1 := entry_FirstNodes_eq_component_mr N ((Br (Pred N)).length - 1) 1 hM hJPltN
        have hcompJ10 := entry_FirstNodes_eq_component_mr N ((Br N).length - 1) 0 hM hJ1Br
        have hcompJ11 := entry_FirstNodes_eq_component_mr N ((Br N).length - 1) 1 hM hJ1Br
        -- `br0eq`
        have hbr0eq : entry ((Br N).getD ((Br (Pred N)).length - 1) []) 0 0
                    = entry ((Br N).getD ((Br N).length - 1) []) 0 0 := by
          rw [← hcompP0, ← hcompJ10]; exact he0eq
        -- descending の `cdom`
        have hcdomB : cdomB ((Br N).getD ((Br (Pred N)).length - 1) [])
                            ((Br N).getD ((Br N).length - 1) []) = true :=
          (descendingB_iff (Br N)).mp hdescB ((Br (Pred N)).length - 1) ((Br N).length - 1)
            (by omega) hJ1Br
        have hcdom := (cdomB_iff _ _).mp hcdomB
        -- `row1ge : entry 1 (FN!J₁) ≤ entry 1 (FN!JP)`
        have hrow1ge : entry N 1 ((FirstNodes N).getD ((Br N).length - 1) 0)
                     ≤ entry N 1 ((FirstNodes N).getD ((Br (Pred N)).length - 1) 0) := by
          rw [hcompJ11, hcompP1]; exact hcdom.2 hbr0eq
        -- `reduced coeff` と合わせて対角性
        have hrc : entry N 1 ((FirstNodes N).getD ((Br (Pred N)).length - 1) 0)
                 ≤ entry N 0 ((FirstNodes N).getD ((Br (Pred N)).length - 1) 0) :=
          reduced_coeff N hR _ (by omega)
        have hle : entry N 0 ((FirstNodes N).getD ((Br (Pred N)).length - 1) 0)
                 ≤ entry N 1 ((FirstNodes N).getD ((Br (Pred N)).length - 1) 0) := by
          rw [he0eq, hdiagj1]; exact hrow1ge
        have hdiagJP : entry N 0 ((FirstNodes N).getD ((Br (Pred N)).length - 1) 0)
                     = entry N 1 ((FirstNodes N).getD ((Br (Pred N)).length - 1) 0) :=
          le_antisymm hle hrc
        rw [heA0, heA1]; exact hdiagJP
      · -- `descendingB (Br (Pred N))`
        have hDTPS_N : DTPS N := (DTPS_iff N).mpr ⟨hR, hmono, hdescB⟩
        have hLpP : 1 < Lng (Pred N) := by rw [hLPN]; omega
        have hDTPS_P : DTPS (Pred N) := descending_Br_Pred N hDTPS_N hBrne hLpP
        exact ((DTPS_iff (Pred N)).mp hDTPS_P).2.2

/-! ## キャップストーン: `RPj1eq` を除去した `vcx_VE_all`（Isabelle `vcx_VE_all`, 77076） -/

/-- Isabelle `vcx_VE_all` (layerB 77076) の骨格から、`RPj1eqResidual` を本ファイルの
`rpj1eq_vc` で除去した front-facing 版。BASE 脚の幾何残差 `BaseMLtTrMax` も
`8.2-condV-VE-base2` で無条件に閉じた。残る残差は深部 surgery ブリック
{BASE 二本, `BpaxVEstep`, `VEj1eqResidual`, `BpaxRPERS`} のみ。 -/
theorem vcx_VE_all_modRPclosed (m : ℕ)
    (hAdm0 : BaseVEAdm0 m) (hStrict : BaseVEStrict m)
    (hstepBpax : BpaxVEstep m) (hstepJ1 : VEj1eqResidual m) (hrpBpax : BpaxRPERS m)
    (M : PS) (hM : VEReg m M) : VEeq m M :=
  vsx_VE_all_modResidual m
    (a0x_base_VE_vb2 m hAdm0 hStrict)
    hstepBpax hstepJ1 hrpBpax (rpj1eq_vc m) M hM

#print axioms rpj1eq_vc
#print axioms vcx_VE_all_modRPclosed

end PSS
