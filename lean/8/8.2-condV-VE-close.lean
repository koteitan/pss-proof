import «8».«8.2-condV-VE-step»
import «8».«8.2-condV-VE-base2»
import «8».«8.2-strongmono-props»
import «7».«7.4-Mark-order»

/-!
# §8.2 値方程式 `VE` キャンペーンの締め: RPERS / `BpaxVEstep` の閉包

- 原文: `tmp/content.md` L3664 付近の補題（条件(V)下の終切片と `Trans` の関係）の
  証明中、原文が省略している後ろ剥がし帰納法（`vbax_VE_backpeel`, `VE_backpeel_TrMax`）の
  `j₁' = j₁` 体制遺伝ステップ（RPERS の稀な分岐）。
- 訂正: なし（Isabelle 側で無条件に証明済みの補題の逐語移植）。
- Isabelle (`isabelle/layerB/pss_wip.thy`):
  - `vjx_RPj1eq` (74726) → `rpj1eq_vc`（本ファイルで `RPj1eqResidual m` を **無条件で** 閉じる）。
  - `bpax_RPERS` (65860) → `bpaxRPERS_holds`（`j₁' < j₁` の RPERS も無条件化）。
  - `bpax_VE_step` (65663) → `bpaxVEstep_holds`（`j₁' < j₁` の surgery STEP を無条件化）。
  - `vcx_VE_all` (77076) の骨格 → `vcx_VE_all_modJ1closed`（BASE / RPERS / `BpaxVEstep` を除去）。
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
- 状態: ✅ 完了（sorry 0、rc=0）。BASE、RPERS 両分岐、`BpaxVEstep`、
  `VEj1eqResidual` をすべて **無条件で閉じ**、`vcx_VE_all` を公開。
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

/-! ## `j₁' < j₁` の RPERS 残差の閉包（Isabelle `bpax_RPERS`, 65860） -/

/-- Isabelle `bpax_RPERS` (layerB 65860): 最終列が新しい枝を開く
`VEj1p N < Lng N - 1` の場合、最終枝は長さ 2 以上なので `Pred` 後も
枝数と最終枝の `FirstNodes` / `Joints` は不変。よって `VEReg` が遺伝する。 -/
theorem bpaxRPERS_holds (m : ℕ) : BpaxRPERS m := by
  intro N reg hj1lt
  obtain ⟨hR, hmono, hBrne, hdisj⟩ := reg
  have hM : TPS N := RTPS_TPS N hR
  have hBrpos : 0 < (Br N).length := List.length_pos_of_ne_nil hBrne
  have hJ : (Br N).length - 1 < (Br N).length := by omega
  have hgeom := FirstNodes_TrMax_Joints N ((Br N).length - 1) hM hmono hJ
  have hL3 : 2 < Lng N := by
    unfold VEj1p at hj1lt
    omega
  have hL : 1 < Lng N := by omega
  have hne : TrMax N ≠ Lng N - 1 := fun heq => hBrne (by simp [Br, heq])
  have hpredR : RTPS (Pred N) := RTPS_Pred N hR
  have hmonoP : monoT (Pred N) = true := monoT_Pred_long N hM hmono hL3
  -- `j₁' < j₁` なので最終枝は一列ではない。
  have hlastgt : 1 < Lng ((Br N).getLastD []) := by
    rw [getLastD_eq_getD_last_68 (Br N) [] hBrne, wf21_Br_eq_seg N hM hBrne,
      length_seg]
    unfold VEj1p at hj1lt
    omega
  have hcore := Br_Pred_core_nontrunk N hM hL hne
  rw [if_neg (by omega : ¬Lng ((Br N).getLastD []) ≤ 1)] at hcore
  have hBrPlen : (Br (Pred N)).length = (Br N).length := by
    rw [hcore]
    simp
    omega
  have hBrPne : Br (Pred N) ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hBrPlen]
    exact hBrpos
  have hJP : (Br N).length - 1 < (Br (Pred N)).length := by omega
  have hFNP : (FirstNodes (Pred N)).getD ((Br N).length - 1) 0 =
      (FirstNodes N).getD ((Br N).length - 1) 0 :=
    FirstNodes_Pred_core N hM hL hne _ hJP
  have hJNP : (Joints (Pred N)).getD ((Br N).length - 1) 0 =
      (Joints N).getD ((Br N).length - 1) 0 :=
    Joints_Pred_core N hM hmono hL hne _ hJP
  have hfnlt : (FirstNodes N).getD ((Br N).length - 1) 0 < Lng N - 1 := by
    simpa only [VEj1p] using hj1lt
  have he0 := entry_Pred N 0 _ hfnlt
  have he1 := entry_Pred N 1 _ hfnlt
  refine ⟨hpredR, hmonoP, hBrPne, ?_⟩
  simp only [VEj1p] at hdisj ⊢
  rw [hBrPlen, hFNP, hJNP]
  rcases hdisj with hlt | ⟨hmeq, hdiag, hdesc⟩
  · exact Or.inl hlt
  · right
    refine ⟨hmeq, ?_, ?_⟩
    · rw [he0, he1]
      exact hdiag
    · have hD : DTPS N := (DTPS_iff N).mpr ⟨hR, hmono, hdesc⟩
      have hLP : Lng (Pred N) = Lng N - 1 := length_Pred N hL
      have hLpP : 1 < Lng (Pred N) := by omega
      exact ((DTPS_iff (Pred N)).mp
        (descending_Br_Pred N hD hBrne hLpP)).2.2

/-! ## STEP 二分岐の共通幾何コア（Isabelle `six_regime_core`, 68112） -/

/-- 行 1 の幹ステップは `TrMax M` で破れる。 -/
private theorem nextR1_TrMax_fail_vc2 (M : PS) (hM : TPS M) :
    nextR M 1 (TrMax M) (TrMax M + 1) = false := by
  cases hst : nextR M 1 (TrMax M) (TrMax M + 1) with
  | false => rfl
  | true =>
      exfalso
      have hall : ∀ j, j < TrMax M + 1 → nextR M 1 j (j + 1) = true := by
        intro j hj
        rcases Nat.lt_or_ge j (TrMax M) with h | h
        · exact TrMax_trunk_step M j hM h
        · have hje : j = TrMax M := by omega
          rw [hje]
          exact hst
      have hle := le_TrMax_intro_wd M (TrMax M + 1) hM hall
      omega

/-- `TrMax M + 1` は `M` 許容。 -/
private theorem adm_TrMax_succ_vc2 (M : PS) (hM : TPS M) :
    adm M (TrMax M + 1) = true := by
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have htb : TrMax M ≤ Lng M - 1 := TrMax_bound M hM
  have hnostep := nextR1_TrMax_fail_vc2 M hM
  have hno : ¬Lng M < TrMax M + 1 := by omega
  simp [adm, nadm, hnostep, hno]

private theorem adm_IncrFirstN_vc2 (k : ℕ) (M : PS) (j : ℕ) :
    adm (IncrFirstN k M) j = adm M j := by
  simp [adm, nadm, nextR_IncrFirstN_ri]

private theorem Adm_IncrFirstN_vc2 (k : ℕ) (M : PS) (j : ℕ) :
    Adm (IncrFirstN k M) j = Adm M j := by
  simp [Adm, adm_IncrFirstN_vc2]

/-- `transJm1_Red_terminal_slice` の marked-basepoint 仮定を、実際に証明で
必要な anchor `m ≤ transJm1 M` に弱めた版。Isabelle `ctx_transJm1_shift`
(layerB 67731) に対応する。 -/
theorem transJm1RedTerminalSlice_of_anchor (M : PS) (m : ℕ)
    (hR : RTPS M) (hlt : m < Lng M - 2)
    (hanc : leR M 0 m (Lng M - 1) = true)
    (hp : hasParent M 0 (Lng M - 1) = true)
    (hmp : m ≤ parent M 0 (Lng M - 1))
    (hanchor : m ≤ transJm1 M) :
    transJm1 (Red (seg M m (Lng M - 1))) = transJm1 M - m := by
  let j1 := Lng M - 1
  let S := seg M m j1
  let N := Red S
  let k := entry M 0 m - entry M 1 m
  have hM : TPS M := RTPS_TPS M hR
  have hmj : m < j1 := by simp [j1]; omega
  have hfacts := ancestor_slice_Red_IncrFirst M m j1 hR hmj
    (by simp [j1]) (by simpa [j1] using hanc)
  have hread : S = IncrFirstN k N := by
    simpa [S, N, k] using hfacts.2.2
  have hJ0 : transJ0 N = transJ0 M - m := by
    simpa [N, S] using transJ0_Red_terminal_slice M m hR hlt hanc hp hmp
  have hAdmNS (q : ℕ) : Adm N q = Adm S q := by
    rw [hread, Adm_IncrFirstN_vc2]
  have hJ0lt : transJ0 M < j1 := by
    simpa [transJ0, lastParent, lastIdx, j1] using
      parent_lt_of_hasParent M 0 (Lng M - 1) hp
  have hAdmSlice : Adm S (transJ0 M - m) = Adm M (transJ0 M) - m := by
    simpa [S] using admof_slice M m (transJ0 M) j1 hM
      (by simpa [transJm1] using hanchor) hJ0lt (by simp [j1])
  calc
    transJm1 N = Adm N (transJ0 N) := by rfl
    _ = Adm N (transJ0 M - m) := by rw [hJ0]
    _ = Adm S (transJ0 M - m) := hAdmNS _
    _ = Adm M (transJ0 M) - m := hAdmSlice
    _ = transJm1 M - m := by rfl

/-- `m` 自身の admissibility を使わない terminal-slice の `Mark` シフト。
Isabelle `ctx_markShift` (layerB 65406) に対応する。 -/
theorem markPredRedTerminalSlice_shift_of_anchor (M : PS) (m : ℕ)
    (hR : RTPS M) (hmono : monoT M = true)
    (hlt : m < Lng M - 2) (hanc : leR M 0 m (Lng M - 1) = true)
    (hp : hasParent M 0 (Lng M - 1) = true)
    (hmp : m ≤ parent M 0 (Lng M - 1))
    (hanchor : m ≤ transJm1 M) :
    Mark (Pred (Red (seg M m (Lng M - 1)))) (transJm1 M - m) =
      Mark (Pred M) (transJm1 M) := by
  let N := Red (seg M m (Lng M - 1))
  let q := transJm1 M
  have hM : TPS M := RTPS_TPS M hR
  have hL : 1 < Lng M := by omega
  have hmj1 : m < Lng M - 1 := by omega
  have hsegT : TPS (seg M m (Lng M - 1)) := by
    intro hnil
    have hz : Lng (seg M m (Lng M - 1)) = 0 := by simp [hnil, Lng]
    rw [length_seg] at hz
    omega
  have hsegMono : monoT (seg M m (Lng M - 1)) = true :=
    mono_ancestor_slice M m (Lng M - 1) hM hmj1 hanc
  have hNR : RTPS N := by
    have hnm : multiT (seg M m (Lng M - 1)) = false := by
      simp [multiT, hsegMono]
    simpa [N] using Red_nonmulti_RTPS (seg M m (Lng M - 1)) hsegT hnm
  have hNmono : monoT N = true := by
    simpa [N] using Red_preserves_monoT_forward
      (seg M m (Lng M - 1)) hsegT hsegMono
  have hNlen : Lng N = Lng M - m := by
    simp only [N]
    rw [Lng_Red_invariance _ hsegT, length_seg]
    omega
  have hN3 : 2 < Lng N := by rw [hNlen]; omega
  have hpN : hasParent N 0 (Lng N - 1) = true :=
    mono_hasParent_row0 N (RTPS_TPS N hNR) hNmono (Lng N - 1)
      (by omega) (by omega)
  have hshift : transJm1 N = q - m := by
    simpa [N, q] using transJm1RedTerminalSlice_of_anchor M m hR hlt hanc hp hmp hanchor
  have hmarkedM : Marked (Pred M) q := by
    simpa [q, transJm1, transJ0, lastParent, lastIdx] using
      Marked_Pred_Adm M hM hL hp
  have hmarkedN : Marked (Pred N) (q - m) := by
    have hmarked : Marked (Pred N) (transJm1 N) := by
      simpa [transJm1, transJ0, lastParent, lastIdx] using
        Marked_Pred_Adm N (RTPS_TPS N hNR) (by omega) hpN
    simpa [hshift] using hmarked
  have hpredMR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredNR : RTPS (Pred N) := RTPS_Pred N hNR
  have hpredMlen : Lng (Pred M) = Lng M - 1 := length_Pred M hL
  have hpredNlen : Lng (Pred N) = Lng N - 1 := length_Pred N (by omega)
  have hqpar : q ≤ parent M 0 (Lng M - 1) := by
    simpa [q, transJm1, transJ0, lastParent, lastIdx] using Adm_le M (transJ0 M)
  have hparlt : parent M 0 (Lng M - 1) < Lng M - 1 :=
    parent_lt_of_hasParent M 0 (Lng M - 1) hp
  have hqle : q ≤ Lng M - 2 := by omega
  rcases Nat.lt_or_eq_of_le hqle with hqint | hqbnd
  · have hqPredM : q < Lng (Pred M) - 1 := by rw [hpredMlen]; omega
    have hqmPredN : q - m < Lng (Pred N) - 1 := by
      rw [hpredNlen, hNlen]
      omega
    have hreprM := Mark_Trans_repr (Pred M) q hmarkedM hpredMR hqPredM
    have hreprN := Mark_Trans_repr (Pred N) (q - m) hmarkedN hpredNR hqmPredN
    have hpredNeq : Pred N = Red (seg M m (Lng M - 2)) := by
      simpa [N] using Pred_Red_terminal_slice M m (Lng M - 1) hmj1
    have htransport := Trans_Pred_Red_slice_shift M m (q - m) hR hlt hanc (by
      rw [← hpredNeq]
      exact hqmPredN)
    have hsegM : seg (Pred M) q (Lng (Pred M) - 1) =
        seg M q (Lng M - 2) := by
      have hs := seg_Pred_eq M q (Lng M - 2) hL hqle (by omega)
      simpa [hpredMlen] using hs
    calc
      Mark (Pred N) (q - m) =
          Trans (seg (Pred N) (q - m) (Lng (Pred N) - 1)) := hreprN
      _ = Trans (seg M (m + (q - m)) (Lng M - 2)) := by
        simpa [N] using htransport
      _ = Trans (seg M q (Lng M - 2)) := by rw [show m + (q - m) = q by omega]
      _ = Trans (seg (Pred M) q (Lng (Pred M) - 1)) := by rw [hsegM]
      _ = Mark (Pred M) q := hreprM.symm
  · have hidxM : q = Lng (Pred M) - 1 := by rw [hpredMlen]; omega
    have hidxN : q - m = Lng (Pred N) - 1 := by
      rw [hpredNlen, hNlen]
      omega
    have hpredMmono : monoT (Pred M) = true := monoT_Pred_long M hM hmono (by omega)
    have hpredNmono : monoT (Pred N) = true :=
      monoT_Pred_long N (RTPS_TPS N hNR) hNmono hN3
    have hzM : zeroT (Pred M) = false := by
      have h := hpredMmono
      simp only [monoT, Bool.and_eq_true, Bool.not_eq_true'] at h
      exact h.1
    have hzN : zeroT (Pred N) = false := by
      have h := hpredNmono
      simp only [monoT, Bool.and_eq_true, Bool.not_eq_true'] at h
      exact h.1
    have hqmN : q - m < Lng N - 1 := by rw [hNlen]; omega
    have heN : entry (Pred N) 1 (q - m) = entry N 1 (q - m) :=
      entry_Pred N 1 (q - m) hqmN
    have heSlice := entry1_Red_terminal_slice M m (q - m) hR hlt hanc (by
      rw [hNlen]
      omega)
    have hqM : q < Lng M - 1 := by omega
    have heM : entry (Pred M) 1 q = entry M 1 q := entry_Pred M 1 q hqM
    have he : entry (Pred N) 1 (q - m) = entry (Pred M) 1 q := by
      rw [heN, heM, heSlice]
      congr 1
      omega
    calc
      Mark (Pred N) (q - m) = Mark (Pred N) (Lng (Pred N) - 1) :=
        congrArg (Mark (Pred N)) hidxN
      _ = Dprin (entry (Pred N) 1 (Lng (Pred N) - 1) : ℕ∞) BZero :=
        Mark_rightmost1_forward (Pred N) hpredNR hzN
      _ = Dprin (entry (Pred M) 1 (Lng (Pred M) - 1) : ℕ∞) BZero := by
        rw [← hidxN, ← hidxM, he]
      _ = Mark (Pred M) (Lng (Pred M) - 1) :=
        (Mark_rightmost1_forward (Pred M) hpredMR hzM).symm
      _ = Mark (Pred M) q := congrArg (Mark (Pred M)) hidxM.symm

/-- Isabelle `ctx_interior_id2` の `markShift` まで閉じた形。 -/
theorem transC1RedTerminalSlice_of_anchor (M : PS) (m : ℕ)
    (hR : RTPS M) (hmono : monoT M = true)
    (hlt : m < Lng M - 2) (hanc : leR M 0 m (Lng M - 1) = true)
    (hp : hasParent M 0 (Lng M - 1) = true)
    (hmp : m ≤ parent M 0 (Lng M - 1))
    (hanchor : m ≤ transJm1 M) :
    transC1 M = transC1 (Red (seg M m (Lng M - 1))) := by
  have hshift := transJm1RedTerminalSlice_of_anchor M m hR hlt hanc hp hmp hanchor
  have hmark := markPredRedTerminalSlice_shift_of_anchor M m hR hmono hlt hanc hp hmp hanchor
  simp only [transC1]
  rw [hshift, hmark]

private theorem admLastParentRedTerminalSlice_of_anchor (M : PS) (m : ℕ)
    (hR : RTPS M) (hlt : m < Lng M - 2)
    (hanc : leR M 0 m (Lng M - 1) = true)
    (hp : hasParent M 0 (Lng M - 1) = true)
    (hmp : m ≤ parent M 0 (Lng M - 1))
    (hanchor : m ≤ transJm1 M) :
    adm (Red (seg M m (Lng M - 1)))
        (lastParent (Red (seg M m (Lng M - 1)))) =
      adm M (lastParent M) := by
  let j1 := Lng M - 1
  let S := seg M m j1
  let N := Red S
  let k := entry M 0 m - entry M 1 m
  have hM : TPS M := RTPS_TPS M hR
  have hmj : m < j1 := by simp [j1]; omega
  have hfacts := ancestor_slice_Red_IncrFirst M m j1 hR hmj
    (by simp [j1]) (by simpa [j1] using hanc)
  have hread : S = IncrFirstN k N := by
    simpa [S, N, k] using hfacts.2.2
  have hJ0 : lastParent N = lastParent M - m := by
    simpa [N, S, transJ0] using
      transJ0_Red_terminal_slice M m hR hlt hanc hp hmp
  have hAdmNS : adm N (lastParent M - m) = adm S (lastParent M - m) := by
    rw [hread, adm_IncrFirstN_vc2]
  have hparLt : lastParent M < j1 := by
    simpa [lastParent, lastIdx, j1] using
      parent_lt_of_hasParent M 0 (Lng M - 1) hp
  have hslice := adm_slice M m (lastParent M) j1 hM
    (by simpa [lastParent, lastIdx] using hmp) hparLt.le (by simp [j1])
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hN
    have hS : adm S (lastParent M - m) = true := by
      rw [← hAdmNS, ← hJ0]
      simpa [N, S] using hN
    rcases hslice.mpr hS with hAdm | hleft | hright
    · exact hAdm
    · have hlow : lastParent M ≤ Adm M (lastParent M) := by
        have := hanchor
        simpa [hleft, transJm1, transJ0] using this
      have heq : Adm M (lastParent M) = lastParent M :=
        Nat.le_antisymm (Adm_le M (lastParent M)) hlow
      simpa [heq] using Adm_adm M (lastParent M)
    · exact (Nat.ne_of_lt hparLt hright).elim
  · intro hAdm
    have hS : adm S (lastParent M - m) = true := hslice.mp (Or.inl hAdm)
    rw [hJ0, hAdmNS]
    simpa [N, S] using hS

private theorem transC2_congr_vc2 (M N : PS)
    (hc1 : transC1 M = transC1 N)
    (he0 : entry N 1 (lastParent N) = entry M 1 (lastParent M))
    (he1 : entry N 1 (lastIdx N) = entry M 1 (lastIdx M))
    (hI : transCondI N = transCondI M)
    (hIII : transCondIII N = transCondIII M)
    (hV : transCondV N = transCondV M)
    (hVI : transCondVI N = transCondVI M) :
    transC2 M = transC2 N := by
  have hv : transV N = transV M := by simp [transV, hc1]
  have ht2 : transT2 N = transT2 M := by simp [transT2, hc1]
  unfold transC2 transC2Core
  simp only [hv, ht2, he0, he1, hI, hIII, hV, hVI]

/-- Isabelle `ctx_interior_id3`。`transC2` を構成する末端二セルと条件判定を
terminal slice へ輸送する、`m`-admissibility 不要の形。 -/
theorem transC2RedTerminalSlice_of_anchor (M : PS) (m : ℕ)
    (hR : RTPS M) (hmono : monoT M = true)
    (hlt : m < Lng M - 2) (hanc : leR M 0 m (Lng M - 1) = true)
    (hp : hasParent M 0 (Lng M - 1) = true)
    (hmp : m ≤ parent M 0 (Lng M - 1))
    (hanchor : m ≤ transJm1 M) :
    transC2 M = transC2 (Red (seg M m (Lng M - 1))) := by
  let S := seg M m (Lng M - 1)
  let N := Red S
  have hsegT : TPS S := by
    intro hnil
    have hz : Lng S = 0 := by simp [hnil, Lng]
    simp [S] at hz
    omega
  have hSlen : Lng S = Lng M - m := by simp [S]; omega
  have hNlen : Lng N = Lng S := by
    simpa [N] using Lng_Red_invariance S hsegT
  have hlast : lastIdx N = lastIdx M - m := by
    simp [lastIdx, hNlen, hSlen]
    omega
  have hpar : lastParent N = lastParent M - m := by
    simpa [N, S, transJ0] using
      transJ0_Red_terminal_slice M m hR hlt hanc hp hmp
  have hlastBound : lastIdx N < Lng N := by simp [lastIdx]; omega
  have hparBound : lastParent N < Lng N := by
    have hparMLt : lastParent M < lastIdx M := by
      simpa [lastParent, lastIdx] using
        parent_lt_of_hasParent M 0 (Lng M - 1) hp
    omega
  have hmLast : m ≤ lastIdx M := by simp [lastIdx]; omega
  have hmPar : m ≤ lastParent M := by
    simpa [lastParent, lastIdx] using hmp
  have hlastSum : m + lastIdx N = lastIdx M := by rw [hlast]; omega
  have hparSum : m + lastParent N = lastParent M := by rw [hpar]; omega
  have heLast : entry N 1 (lastIdx N) = entry M 1 (lastIdx M) := by
    have he := entry1_Red_terminal_slice M m (lastIdx N) hR hlt hanc
      (by simpa [N, S] using hlastBound)
    exact he.trans (by rw [hlastSum])
  have hePar : entry N 1 (lastParent N) = entry M 1 (lastParent M) := by
    have he := entry1_Red_terminal_slice M m (lastParent N) hR hlt hanc
      (by simpa [N, S] using hparBound)
    exact he.trans (by rw [hparSum])
  have hAdm : adm N (lastParent N) = adm M (lastParent M) := by
    simpa [N, S] using admLastParentRedTerminalSlice_of_anchor
      M m hR hlt hanc hp hmp hanchor
  have hltAr : (lastParent N + 1 < lastIdx N) ↔
      lastParent M + 1 < lastIdx M := by omega
  have heqAr : (lastParent N + 1 = lastIdx N) ↔
      lastParent M + 1 = lastIdx M := by omega
  have hI : transCondI N = transCondI M := by
    apply Bool.eq_iff_iff.mpr
    simp [transCondI, heLast, hAdm]
  have hIII : transCondIII N = transCondIII M := by
    apply Bool.eq_iff_iff.mpr
    simp [transCondIII, heLast, hePar, hAdm]
  have hV : transCondV N = transCondV M := by
    apply Bool.eq_iff_iff.mpr
    simp [transCondV, heLast, hePar, hltAr]
  have hVI : transCondVI N = transCondVI M := by
    apply Bool.eq_iff_iff.mpr
    simp [transCondVI, heLast, hePar, heqAr]
  have hc1 : transC1 M = transC1 N := by
    simpa [N, S] using
      transC1RedTerminalSlice_of_anchor M m hR hmono hlt hanc hp hmp hanchor
  exact transC2_congr_vc2 M N hc1 hePar heLast hI hIII hV hVI

/-- Isabelle `ctx_interior_ids` (layerB 65526)。 -/
theorem transCoreRedTerminalSlice_of_anchor (M : PS) (m : ℕ)
    (hR : RTPS M) (hmono : monoT M = true)
    (hlt : m < Lng M - 2) (hanc : leR M 0 m (Lng M - 1) = true)
    (hp : hasParent M 0 (Lng M - 1) = true)
    (hmp : m ≤ parent M 0 (Lng M - 1))
    (hanchor : m ≤ transJm1 M) :
    transC1 M = transC1 (Red (seg M m (Lng M - 1))) ∧
      transC2 M = transC2 (Red (seg M m (Lng M - 1))) :=
  ⟨transC1RedTerminalSlice_of_anchor M m hR hmono hlt hanc hp hmp hanchor,
    transC2RedTerminalSlice_of_anchor M m hR hmono hlt hanc hp hmp hanchor⟩

/-- Isabelle `six_scb_prefix_ne` (layerB 68081)。正の `transJm1` で選ばれた
marked principal は `Trans (Pred M)` 全体ではないので、その scb 分解の
左 context は空にならない。 -/
theorem scbPrefixNonempty_of_transJm1_pos (M : PS) (s b : List Sym)
    (hR : RTPS M) (hmono : monoT M = true)
    (hJ1pos : 0 < transJ1 M) (ht1 : transT1 M ≠ BZero)
    (hjm1pos : 0 < transJm1 M)
    (hd : scb_decomp (Trans (Pred M)) s (flatBT (transC1 M)) b) :
    s ≠ [] := by
  intro hs
  have hM : TPS M := RTPS_TPS M hR
  have hL : 1 < Lng M := by
    simpa [transJ1, lastIdx] using hJ1pos
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredT : TPS (Pred M) := RTPS_TPS (Pred M) hpredR
  have hjmMarked : Marked (Pred M) (transJm1 M) := by
    simpa [transJm1, transJ0, lastParent, lastIdx] using
      Marked_Pred_Adm M hM hL hp
  have hpredMono : monoT (Pred M) = true := by
    by_cases hPredOne : Lng (Pred M) = 1
    · have hzPred : zeroT (Pred M) = false := by
        apply Bool.eq_false_of_not_eq_true
        intro hz
        have hzTrans := (Trans_preserves_zeroT (Pred M) hpredT).1 hz
        exact ht1 (by simpa [transT1] using hzTrans)
      have hle : leR (Pred M) 0 0 (Lng (Pred M) - 1) = true := by
        simp [hPredOne, leR, le0, le0Aux]
      simp [monoT, hzPred, hle]
    · have hlong : 2 < Lng M := by
        rw [length_Pred M hL] at hPredOne
        omega
      exact monoT_Pred_long M hM hmono hlong
  have hpredMono' := hpredMono
  simp only [monoT, Bool.and_eq_true, Bool.not_eq_true'] at hpredMono'
  have hzeroMarked : Marked (Pred M) 0 :=
    ⟨hpredT, adm_zero (Pred M), hpredMono'.2⟩
  have hflat : flatBT (Trans (Pred M)) = flatBT (transC1 M) ++ b := by
    simpa [hs] using hd.1
  have hb : b = [] := flatBT_append_suffix_nil hflat
  have heq : Trans (Pred M) = transC1 M :=
    flatBT_injective (by simpa [hb] using hflat)
  exact (Mark0_ne_Mark (Pred M) (transJm1 M) hpredR hzeroMarked
    hjmMarked hjm1pos) (by simpa [transC1] using heq.symm)

/-- Isabelle `six_regime_core` (layerB 68112)。最終列が新しい枝を開く
STEP regime から、長さ・trunk 境界・親・許容化点・切片の祖先性と
`Trans (Pred Q)` の非零性を一括で取り出す。 -/
theorem veStepRegimeCore (m : ℕ) (Q : PS) (reg : VEReg m Q)
    (hj1lt : VEj1p Q < Lng Q - 1) :
    2 < Lng Q ∧
    m < Lng Q - 2 ∧
    m ≤ TrMax Q ∧
    TrMax Q < parent Q 0 (Lng Q - 1) ∧
    TrMax Q + 1 ≤ transJm1 Q ∧
    parent Q 0 (Lng Q - 1) < Lng Q - 1 ∧
    leR Q 0 m (Lng Q - 1) = true ∧
    transT1 Q ≠ BZero := by
  obtain ⟨hR, hmono, hBrne, hdisj⟩ := reg
  have hM : TPS Q := RTPS_TPS Q hR
  have hJ : (Br Q).length - 1 < (Br Q).length := by
    have := List.length_pos_of_ne_nil hBrne
    omega
  have hgeom := FirstNodes_TrMax_Joints Q ((Br Q).length - 1) hM hmono hJ
  have hmleJoint : m ≤ (Joints Q).getD ((Br Q).length - 1) 0 := by
    rcases hdisj with hlt | ⟨heq, -, -⟩
    · omega
    · omega
  have hL3 : 2 < Lng Q := by
    unfold VEj1p at hj1lt
    omega
  have hmint : m < Lng Q - 2 := by
    unfold VEj1p at hj1lt
    omega
  have hmTr : m ≤ TrMax Q := hmleJoint.trans hgeom.1
  have hL : 1 < Lng Q := by omega
  have hp : hasParent Q 0 (Lng Q - 1) = true :=
    mono_hasParent_row0 Q hM hmono (Lng Q - 1) (by omega) (by omega)
  have hparlt : parent Q 0 (Lng Q - 1) < Lng Q - 1 :=
    parent_lt_of_hasParent Q 0 (Lng Q - 1) hp
  have hTrpar : TrMax Q < parent Q 0 (Lng Q - 1) := by
    by_contra hnot
    have hparle : parent Q 0 (Lng Q - 1) ≤ TrMax Q := by omega
    have heq := lastbranch_eq_j1 Q hR hmono hBrne (by omega) hparle
    unfold VEj1p at hj1lt
    omega
  have hAdmTr : adm Q (TrMax Q + 1) = true := adm_TrMax_succ_vc2 Q hM
  have hTrAdm : TrMax Q + 1 ≤ transJm1 Q := by
    have hmax := Adm_max Q (TrMax Q + 1) (parent Q 0 (Lng Q - 1))
      hAdmTr (by omega)
    simpa [transJm1, transJ0, lastParent, lastIdx] using hmax
  have hmj1 : m < Lng Q - 1 := by omega
  have hmonoSeg : monoT (seg Q m (Lng Q - 1)) = true :=
    mono_slice Q m (Lng Q - 1) hM hmono hmj1 (le_refl _) hmleJoint
  have hle0 : le0 Q m (Lng Q - 1) = true :=
    le0_monoT_seg_into_list Q m (Lng Q - 1) (Lng Q - 1) hM hmonoSeg
      (by omega) (le_refl _) (by omega)
  have hleR : leR Q 0 m (Lng Q - 1) = true := by simpa [leR] using hle0
  have hpredR : RTPS (Pred Q) := RTPS_Pred Q hR
  have hLP : Lng (Pred Q) = Lng Q - 1 := length_Pred Q hL
  have hzP : zeroT (Pred Q) = false := by
    have hne1 : Lng (Pred Q) ≠ 1 := by omega
    simp [zeroT, hne1]
  have htP : Trans (Pred Q) ≠ BZero := by
    intro ht
    have hz := (Trans_preserves_zeroT (Pred Q) (RTPS_TPS (Pred Q) hpredR)).mpr ht
    rw [hzP] at hz
    contradiction
  refine ⟨hL3, hmint, hmTr, hTrpar, hTrAdm, hparlt, hleR, ?_⟩
  simpa [transT1] using htP

/-- Isabelle `six_tneR` (layerB 68200)。STEP regime では `transJm1 Q > 0`。
`trans_admpos_body_split` が `Trans (Pred Q)` の body に少なくとも一つ
principal が残る形を与えるため、その `bpHeadT` は非零。 -/
theorem veStepDeepTailNonzero (m : ℕ) (Q : PS) (reg : VEReg m Q)
    (hj1lt : VEj1p Q < Lng Q - 1) :
    bpHeadT (Trans (Pred Q)) ≠ BZero := by
  have hcore := veStepRegimeCore m Q reg hj1lt
  obtain ⟨hR, hmono, -, -⟩ := reg
  obtain ⟨hL3, -, -, -, hAdm, -, -, ht1⟩ := hcore
  have hAdmpos : 0 < transJm1 Q := by omega
  obtain ⟨pre, w, u2, _u3, hpred, _hhost⟩ :=
    trans_admpos_body_split scbOuterSurgerySplit_holds Q hR hmono
      (by omega) hAdmpos (by simpa [transT1] using ht1)
  rw [hpred]
  rcases pre with ⟨ps⟩
  simp [Dprin, addBT, BZero, bpHeadT]

/-- Isabelle `six_intMR` (layerB 68225)。STEP host の marked principal を
切り出す scb 分解には、必ず非空の左 context がある。 -/
theorem veStepHostPrefixNonempty (m : ℕ) (Q : PS) (s b : List Sym)
    (reg : VEReg m Q) (hj1lt : VEj1p Q < Lng Q - 1)
    (hd : scb_decomp (Trans (Pred Q)) s (flatBT (transC1 Q)) b) :
    s ≠ [] := by
  have hcore := veStepRegimeCore m Q reg hj1lt
  obtain ⟨hR, hmono, -, -⟩ := reg
  obtain ⟨hL3, -, -, -, hAdm, -, -, ht1⟩ := hcore
  apply scbPrefixNonempty_of_transJm1_pos Q s b hR hmono
  · simp [transJ1, lastIdx]
    omega
  · exact ht1
  · omega
  · exact hd

/-- Isabelle `six_lerR` (layerB 68371)。 -/
theorem veStepAncestry (m : ℕ) (Q : PS) (reg : VEReg m Q)
    (hj1lt : VEj1p Q < Lng Q - 1) :
    leR Q 0 m (Lng Q - 1) = true :=
  (veStepRegimeCore m Q reg hj1lt).2.2.2.2.2.2.1

/-- Isabelle `six_ids` / `six_id2R` / `six_id3R` (layerB 68376--68402)。 -/
theorem veStepCoreIdentities (m : ℕ) (Q : PS) (reg : VEReg m Q)
    (hj1lt : VEj1p Q < Lng Q - 1) :
    transC1 Q = transC1 (Red (seg Q m (Lng Q - 1))) ∧
      transC2 Q = transC2 (Red (seg Q m (Lng Q - 1))) := by
  have hcore := veStepRegimeCore m Q reg hj1lt
  obtain ⟨hR, hmono, -, -⟩ := reg
  obtain ⟨-, hmint, hmTr, hTrpar, hAdm, hparlt, hanc, -⟩ := hcore
  have hM : TPS Q := RTPS_TPS Q hR
  have hp : hasParent Q 0 (Lng Q - 1) = true :=
    mono_hasParent_row0 Q hM hmono (Lng Q - 1) (by omega) (by omega)
  apply transCoreRedTerminalSlice_of_anchor Q m hR hmono hmint hanc hp
  · omega
  · omega

/-- Isabelle `six_intNR` (layerB 68247)。STEP の reduced terminal slice 側でも
marked principal の scb 分解には非空の左 context がある。 -/
theorem veStepSlicePrefixNonempty (m : ℕ) (Q : PS) (s b : List Sym)
    (reg : VEReg m Q) (hj1lt : VEj1p Q < Lng Q - 1)
    (hd : scb_decomp
      (Trans (Pred (Red (seg Q m (Lng Q - 1))))) s
      (flatBT (transC1 (Red (seg Q m (Lng Q - 1))))) b) :
    s ≠ [] := by
  have hcore := veStepRegimeCore m Q reg hj1lt
  obtain ⟨hR, hmono, -, -⟩ := reg
  obtain ⟨hL3, hmint, hmTr, hTrpar, hAdm, -, hanc, -⟩ := hcore
  have hM : TPS Q := RTPS_TPS Q hR
  have hL : 1 < Lng Q := by omega
  have hmj1 : m < Lng Q - 1 := by omega
  have hp : hasParent Q 0 (Lng Q - 1) = true :=
    mono_hasParent_row0 Q hM hmono (Lng Q - 1) (by omega) (by omega)
  have hmp : m ≤ parent Q 0 (Lng Q - 1) := by omega
  have hmJm1 : m < transJm1 Q := by omega
  let N := Red (seg Q m (Lng Q - 1))
  have hsegT : TPS (seg Q m (Lng Q - 1)) := by
    intro hnil
    have hz : Lng (seg Q m (Lng Q - 1)) = 0 := by simp [hnil, Lng]
    rw [length_seg] at hz
    omega
  have hsegMono : monoT (seg Q m (Lng Q - 1)) = true :=
    mono_ancestor_slice Q m (Lng Q - 1) hM hmj1 hanc
  have hsegNonmulti : multiT (seg Q m (Lng Q - 1)) = false := by
    simp [multiT, hsegMono]
  have hNR : RTPS N := by
    simpa [N] using Red_nonmulti_RTPS (seg Q m (Lng Q - 1)) hsegT hsegNonmulti
  have hNmono : monoT N = true := by
    simpa [N] using Red_preserves_monoT_forward
      (seg Q m (Lng Q - 1)) hsegT hsegMono
  have hNlen : Lng N = Lng Q - m := by
    simp only [N]
    rw [Lng_Red_invariance _ hsegT, length_seg]
    omega
  have hJm1N : transJm1 N = transJm1 Q - m := by
    simpa [N] using transJm1RedTerminalSlice_of_anchor Q m hR hmint hanc hp hmp
      (le_of_lt hmJm1)
  have hJm1Npos : 0 < transJm1 N := by omega
  have hNT : TPS N := RTPS_TPS N hNR
  have hN3 : 2 < Lng N := by rw [hNlen]; omega
  have hpredNmono : monoT (Pred N) = true := monoT_Pred_long N hNT hNmono hN3
  have hpredNmono' := hpredNmono
  simp only [monoT, Bool.and_eq_true, Bool.not_eq_true'] at hpredNmono'
  have hpredNR : RTPS (Pred N) := RTPS_Pred N hNR
  have ht1N : transT1 N ≠ BZero := by
    intro ht
    have hz := (Trans_preserves_zeroT (Pred N) (RTPS_TPS (Pred N) hpredNR)).mpr
      (by simpa [transT1] using ht)
    rw [hpredNmono'.1] at hz
    contradiction
  apply scbPrefixNonempty_of_transJm1_pos N s b hNR hNmono
  · simp [transJ1, lastIdx, hNlen]
    omega
  · exact ht1N
  · exact hJm1Npos
  · simpa [N] using hd

/-! ## `BpaxVEstep` の scb surgery heart -/

/-- 先頭の principal 指標だけが異なる同一 flat body は、同じ `bpHeadT` を持つ。
`unflatBT` の実行可能 parser を直接正規化したもの。 -/
private theorem bpHeadT_unflat_dsym_eq_vc (a b : ℕ∞) (q : List Sym) :
    bpHeadT (unflatBT (.dsym a :: q)) =
      bpHeadT (unflatBT (.dsym b :: q)) := by
  generalize hp : parseBTAux (q.length + 1) q = r
  cases r with
  | none => simp [unflatBT, parseBTAux, hp]
  | some x =>
      rcases x with ⟨t, rest⟩
      cases rest <;> simp [unflatBT, parseBTAux, hp, Dprin, bpHeadT]

/-- Isabelle `cfcx_scb_principal_peel` (layerB 63384)。非空 prefix を持つ
principal 項の scb 分解から、外側の `D` を剥がす。 -/
private theorem scbPrincipalPeel_vc {a : ℕ∞} {t : BT}
    {s c b : List Sym} (hd : scb_decomp (Dprin a t) s c b)
    (hs : s ≠ []) :
    ∃ s', s = .dsym a :: s' ∧ scb_decomp t s' c b := by
  cases s with
  | nil => exact (hs rfl).elim
  | cons x s' =>
    rcases hd with ⟨hflat, hptb, hrp⟩
    change .dsym a :: flatBT t = (x :: s') ++ c ++ b at hflat
    have hflat' : .dsym a :: flatBT t = x :: (s' ++ c ++ b) := by
      simpa only [List.cons_append, List.append_assoc] using hflat
    have hx : x = .dsym a := (List.cons.inj hflat').1.symm
    have hbody : flatBT t = s' ++ c ++ b := (List.cons.inj hflat').2
    subst x
    refine ⟨s', rfl, hbody, ?_, hrp⟩
    intro _
    exact hptb (by simp [Dprin, BZero])

/-- Isabelle `cfcx_VE_step_abstract` の surgery heart。二つの predecessor
translation が外側の principal 指標を除いて同じ body を持ち、同一の interior
principal を同じ項へ置換するなら、置換後の `bpHeadT` は一致する。

Lean 側の scb 分解一意性は zero 仮定なしで使えるため、Isabelle 版の
`t ≠ 0` / principal-image 補助仮定は不要。 -/
private theorem veSurgeryBpHeadEq_vc
    {TM TN TPM TPN c1 c2 t : BT} {a b : ℕ∞}
    {sM sN bM bN : List Sym}
    (dM : scb_decomp TM sM (flatBT c2) bM)
    (dN : scb_decomp TN sN (flatBT c2) bN)
    (dPM : scb_decomp TPM sM (flatBT c1) bM)
    (dPN : scb_decomp TPN sN (flatBT c1) bN)
    (pPM : TPM = Dprin a t) (pPN : TPN = Dprin b t)
    (sMne : sM ≠ []) (sNne : sN ≠ []) :
    bpHeadT TM = bpHeadT TN := by
  have dPM' : scb_decomp (Dprin a t) sM (flatBT c1) bM := by
    simpa [pPM] using dPM
  have dPN' : scb_decomp (Dprin b t) sN (flatBT c1) bN := by
    simpa [pPN] using dPN
  obtain ⟨sM', hsM, dMt⟩ := scbPrincipalPeel_vc dPM' sMne
  obtain ⟨sN', hsN, dNt⟩ := scbPrincipalPeel_vc dPN' sNne
  obtain ⟨hs, hb⟩ :=
    scb_unique_decomp_unconditional t sM' sN' (flatBT c1) bM bN dMt dNt
  have fM : flatBT TM = .dsym a :: (sM' ++ flatBT c2 ++ bM) := by
    rw [dM.1, hsM]
    simp [List.append_assoc]
  have fN : flatBT TN = .dsym b :: (sM' ++ flatBT c2 ++ bM) := by
    rw [dN.1, hsN, ← hs, ← hb]
    simp [List.append_assoc]
  rw [← unflatBT_flat TM, ← unflatBT_flat TN, fM, fN]
  exact bpHeadT_unflat_dsym_eq_vc a b _

/-- Isabelle `s84c2_Trans_c2_decomp`。mono host の `Trans (Pred M)` 内の
`c₁` と `Trans M` 内の `c₂` に、同じ scb context を選べる。 -/
private theorem transC1C2SharedScb_vc (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) (hlen : 1 < Lng M)
    (ht₁ : Trans (Pred M) ≠ BZero) :
    ∃ s b : List Sym,
      scb_decomp (Trans (Pred M)) s (flatBT (transC1 M)) b ∧
      scb_decomp (Trans M) s (flatBT (transC2 M)) b := by
  have hM : TPS M := RTPS_TPS M hR
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hmarked : Marked (Pred M) (Adm M (parent M 0 (Lng M - 1))) :=
    Marked_Pred_Adm M hM hlen hp
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have ht₁TB : Trans (Pred M) ∈ T_B := Trans_mem_T_B (Pred M) hpredR
  have hc₁TB : transC1 M ∈ T_B := by
    simpa [transC1, transJm1, transJ0, lastParent] using
      Mark_mem_T_B (Pred M) _ hpredR hmarked
  have ht₁c₁ : (Trans (Pred M), transC1 M) ∈ MarkedB := by
    simpa [transC1, transJm1, transJ0, lastParent] using
      Trans_Mark_mem_MarkedB (Pred M) _ hpredR hmarked
  have hc₁P : ∃ p, transC1 M = .trm [p] :=
    marked_component_principal ht₁ ht₁c₁
  have hc₂facts := transC2Core_properties M (transC1 M) hc₁TB hc₁P
  have hc₂TB : transC2 M ∈ T_B := by
    simpa [transC2, transV, transT2] using hc₂facts.1
  have hc₂P : ∃ p, transC2 M = .trm [p] := by
    simpa [transC2, transV, transT2] using hc₂facts.2
  have hTrans :
      Trans M = replaceScb (Trans (Pred M)) (transC1 M) (transC2 M) := by
    simpa [ht₁, transC1, transC2, transV, transT2, transJm1, transJ0,
      lastParent] using (Trans_Mark_mono_equations M hR hlen hmono).1
  obtain ⟨s, b, hd, _hout, hd2⟩ :=
    replaceScb_spec ht₁TB hc₁TB hc₁P hc₂TB hc₂P ht₁c₁
  exact ⟨s, b, hd, by rw [hTrans]; exact hd2⟩

/-- `m < transJm1 M` の interior 領域における共通 surgery engine。
`VEj1p` の大小に依存せず、終切片の到達性と親アンカーのみを受け取る。 -/
private theorem veSurgeryStepData_vc (m : ℕ) (M : PS)
    (hR : RTPS M) (hmono : monoT M = true)
    (hmint : m < Lng M - 2)
    (hanc : leR M 0 m (Lng M - 1) = true)
    (hp : hasParent M 0 (Lng M - 1) = true)
    (hmp : m ≤ parent M 0 (Lng M - 1))
    (hstr : m < transJm1 M) (IH : VEeq m (Pred M)) :
    VEeq m M := by
  have hM : TPS M := RTPS_TPS M hR
  have hL3 : 2 < Lng M := by omega
  have hL : 1 < Lng M := by omega
  have hmLast : m < Lng M - 1 := by omega
  have hJ1pos : 0 < transJ1 M := by simp [transJ1, lastIdx]; omega
  have hJmpos : 0 < transJm1 M := by omega
  have hpredMR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredMmono : monoT (Pred M) = true :=
    monoT_Pred_long M hM hmono hL3

  let N := Red (seg M m (Lng M - 1))
  have hsegT : TPS (seg M m (Lng M - 1)) := by
    intro hnil
    have hz : Lng (seg M m (Lng M - 1)) = 0 := by simp [hnil, Lng]
    rw [length_seg] at hz
    omega
  have hsegMono : monoT (seg M m (Lng M - 1)) = true :=
    mono_ancestor_slice M m (Lng M - 1) hM hmLast hanc
  have hsegNonmulti : multiT (seg M m (Lng M - 1)) = false := by
    simp [multiT, hsegMono]
  have hNR : RTPS N := by
    simpa [N] using
      Red_nonmulti_RTPS (seg M m (Lng M - 1)) hsegT hsegNonmulti
  have hNmono : monoT N = true := by
    simpa [N] using Red_preserves_monoT_forward
      (seg M m (Lng M - 1)) hsegT hsegMono
  have hNlen : Lng N = Lng M - m := by
    simp only [N]
    rw [Lng_Red_invariance _ hsegT, length_seg]
    omega
  have hN3 : 2 < Lng N := by rw [hNlen]; omega
  have hNT : TPS N := RTPS_TPS N hNR
  have hpredNR : RTPS (Pred N) := RTPS_Pred N hNR
  have hpredNmono : monoT (Pred N) = true :=
    monoT_Pred_long N hNT hNmono hN3
  have hJmN : transJm1 N = transJm1 M - m := by
    simpa [N] using transJm1RedTerminalSlice_of_anchor M m hR hmint hanc hp hmp hstr.le
  have hJmNpos : 0 < transJm1 N := by rw [hJmN]; omega
  have hJ1Npos : 0 < transJ1 N := by simp [transJ1, lastIdx]; omega

  -- Bridge the recursive VE equation to equality of predecessor bodies.
  change bpHeadT (Trans (seg (Pred M) m (Lng (Pred M) - 1))) =
    bpHeadT (Trans (Pred M)) at IH
  have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M hL
  have hsegPred :
      seg (Pred M) m (Lng (Pred M) - 1) = seg M m (Lng M - 2) := by
    simpa [hLP] using
      seg_Pred_eq M m (Lng M - 2) hL (by omega) (by omega)
  have hIHbody :
      bpHeadT (Trans (Pred M)) = bpHeadT (Trans (Pred N)) := by
    have h := IH.symm
    rw [hsegPred, ← Trans_Pred_Red_terminal_slice M m hmint] at h
    simpa [N] using h

  let t := bpHeadT (Trans (Pred M))
  have pPM : Trans (Pred M) =
      Dprin (entry (Pred M) 1 0 : ℕ∞) t := by
    simpa [t] using Trans_principal_head (Pred M) hpredMR hpredMmono
  have pPN0 := Trans_principal_head (Pred N) hpredNR hpredNmono
  have pPN : Trans (Pred N) =
      Dprin (entry (Pred N) 1 0 : ℕ∞) t := by
    calc
      Trans (Pred N) = Dprin (entry (Pred N) 1 0 : ℕ∞)
          (bpHeadT (Trans (Pred N))) := pPN0
      _ = Dprin (entry (Pred N) 1 0 : ℕ∞) t := by rw [← hIHbody]
  have htPM : Trans (Pred M) ≠ BZero := by rw [pPM]; simp [Dprin, BZero]
  have htPN : Trans (Pred N) ≠ BZero := by rw [pPN]; simp [Dprin, BZero]

  obtain ⟨sM, bM, dPM, dM⟩ :=
    transC1C2SharedScb_vc M hR hmono hL htPM
  obtain ⟨sN, bN, dPN0, dN0⟩ :=
    transC1C2SharedScb_vc N hNR hNmono (by omega) htPN
  obtain ⟨hc₁, hc₂⟩ := transCoreRedTerminalSlice_of_anchor
    M m hR hmono hmint hanc hp hmp hstr.le
  have dPN : scb_decomp (Trans (Pred N)) sN (flatBT (transC1 M)) bN := by
    simpa [N, hc₁] using dPN0
  have dN : scb_decomp (Trans N) sN (flatBT (transC2 M)) bN := by
    simpa [N, hc₂] using dN0
  have hsM : sM ≠ [] :=
    scbPrefixNonempty_of_transJm1_pos M sM bM hR hmono hJ1pos htPM hJmpos dPM
  have hsN : sN ≠ [] :=
    scbPrefixNonempty_of_transJm1_pos N sN bN hNR hNmono hJ1Npos htPN hJmNpos dPN0
  have hMN : bpHeadT (Trans M) = bpHeadT (Trans N) :=
    veSurgeryBpHeadEq_vc dM dN dPM dPN pPM pPN hsM hsN
  unfold VEeq
  have hRed : Trans (seg M m (Lng M - 1)) = Trans N := by
    simpa [N] using Trans_Red (seg M m (Lng M - 1)) hsegT
  rw [hRed]
  exact hMN.symm

/-- Isabelle `vjx_VEj1eq_deepen` (layerB 74938)。`j₁' = j₁` 分岐でも
`m < transJm1 Q` なら marked principal は interior なので、共通 surgery
engine で VE を閉じられる。 -/
theorem veJ1eqDeepen_vc (m : ℕ) (Q : PS)
    (reg : VEReg m Q) (heq : VEj1p Q = Lng Q - 1)
    (hnonmin : TrMax Q + 2 < Lng Q)
    (hstr : m < transJm1 Q) (IH : VEeq m (Pred Q)) :
    VEeq m Q := by
  have regKeep := reg
  obtain ⟨hR, hmono, hBrne, hdisj⟩ := regKeep
  have hM : TPS Q := RTPS_TPS Q hR
  have hJ : (Br Q).length - 1 < (Br Q).length := by
    have := List.length_pos_of_ne_nil hBrne
    omega
  have hgeom := FirstNodes_TrMax_Joints Q ((Br Q).length - 1) hM hmono hJ
  have hmleJoint : m ≤ (Joints Q).getD ((Br Q).length - 1) 0 := by
    rcases hdisj with hlt | ⟨he, -, -⟩ <;> omega
  have hmTr : m ≤ TrMax Q := hmleJoint.trans hgeom.1
  have hmint : m < Lng Q - 2 := by omega
  have hL : 1 < Lng Q := by omega
  have hp : hasParent Q 0 (Lng Q - 1) = true :=
    mono_hasParent_row0 Q hM hmono (Lng Q - 1) (by omega) (by omega)
  have hjoint : (Joints Q).getD ((Br Q).length - 1) 0 =
      parent Q 0 ((FirstNodes Q).getD ((Br Q).length - 1) 0) :=
    Joints_getD Q _ hJ
  have hmp : m ≤ parent Q 0 (Lng Q - 1) := by
    unfold VEj1p at heq
    rw [heq] at hjoint
    rw [← hjoint]
    exact hmleJoint
  have hmLast : m < Lng Q - 1 := by omega
  have hmonoSeg : monoT (seg Q m (Lng Q - 1)) = true :=
    mono_slice Q m (Lng Q - 1) hM hmono hmLast (le_refl _) hmleJoint
  have hle0 : le0 Q m (Lng Q - 1) = true :=
    le0_monoT_seg_into_list Q m (Lng Q - 1) (Lng Q - 1) hM hmonoSeg
      (by omega) (le_refl _) (by omega)
  have hanc : leR Q 0 m (Lng Q - 1) = true := by simpa [leR] using hle0
  exact veSurgeryStepData_vc m Q hR hmono hmint hanc hp hmp hstr IH

/-! ## `j₁' = j₁` の Adm0 collapse 準備 -/

/-- `VEReg` の offset は trunk maximum より左にある。Isabelle
`bihx_base_m_lt_TrMax` (71267) の実質的に BASE 仮定を使わない形。 -/
private theorem veReg_m_lt_TrMax_vc (m : ℕ) (M : PS) (reg : VEReg m M) :
    m < TrMax M := by
  obtain ⟨hR, hmono, hBrne, hcases⟩ := reg
  have hM : TPS M := RTPS_TPS M hR
  have hJ : (Br M).length - 1 < (Br M).length := by
    have := List.length_pos_of_ne_nil hBrne
    omega
  have hgeom : (Joints M).getD ((Br M).length - 1) 0 ≤ TrMax M :=
    (FirstNodes_TrMax_Joints M ((Br M).length - 1) hM hmono hJ).1
  rcases hcases with hlt | ⟨hmeq, hdiag, hdesc⟩
  · omega
  · have hD : DTPS M := (DTPS_iff M).mpr ⟨hR, hmono, hdesc⟩
    simp only [VEj1p] at hdiag
    have he1j := joint_row1_eq M ((Br M).length - 1) hD hJ
    have he0f := entry_FirstNodes_eq_component_mr M ((Br M).length - 1) 0 hM hJ
    have hc0 := branch_col0_val M ((Br M).length - 1) hD hJ
    have hdet : entry M 1 ((Joints M).getD ((Br M).length - 1) 0) <
        entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) := by
      omega
    have hjlt := det_imp_joint_lt_TrMax M hD hBrne hdet
    omega

private theorem admTrunkInteriorFalse_vc (M : PS) (j : ℕ) (hM : TPS M)
    (hjpos : 0 < j) (hjlt : j < TrMax M) : adm M j = false := by
  have hs1 : nextR M 1 (j - 1) (j - 1 + 1) = true :=
    TrMax_trunk_step M (j - 1) hM (by omega)
  have hs2 : nextR M 1 j (j + 1) = true := TrMax_trunk_step M j hM hjlt
  have hkeq : j - 1 + 1 = j := by omega
  rw [hkeq] at hs1
  simp [adm, nadm, hs1, hs2]

private theorem admLeTrMaxCases_vc (M : PS) (j : ℕ) (hM : TPS M)
    (ha : adm M j = true) (hjle : j ≤ TrMax M) :
    j = 0 ∨ j = TrMax M := by
  by_contra hnot
  have hj0 : j ≠ 0 := fun h => hnot (Or.inl h)
  have hjT : j ≠ TrMax M := fun h => hnot (Or.inr h)
  have hbad := admTrunkInteriorFalse_vc M j hM (Nat.pos_of_ne_zero hj0)
    (lt_of_le_of_ne hjle hjT)
  rw [hbad] at ha
  exact Bool.false_ne_true ha

/-- Isabelle `Trans_eq_transC2_Adm0` の Lean 短縮形。同時に
predecessor translation の principal 表示も返す。 -/
private theorem adm0Setup_vc (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) (hAdm0 : transJm1 M = 0) :
    Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) (transT2 M) ∧
    Trans M = transC2 M := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hPredT : TPS (Pred M) := RTPS_TPS (Pred M) hpredR
  have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hzPred : zeroT (Pred M) = false := by
    have hne : Lng (Pred M) ≠ 1 := by omega
    simp [zeroT, hne]
  have ht1 : Trans (Pred M) ≠ BZero := by
    intro h0
    have hz := (Trans_preserves_zeroT (Pred M) hPredT).mpr h0
    rw [hzPred] at hz
    simp at hz
  have hleR00 : leR M 0 0 (Lng M - 1) = true := by
    have hh := hmono
    simp only [monoT, Bool.and_eq_true] at hh
    exact hh.2
  have hMk0 : Marked M 0 := ⟨hM, adm_zero M, hleR00⟩
  have hMzT : Mark M 0 = Trans M := Mark_zero_eq_Trans M hR hMk0
  have hMc2 : Mark M (transJm1 M) = transC2 M :=
    Mark_transJm1_eq_transC2 M hR hmono hlen ht1
  rw [hAdm0] at hMc2
  have hTc2 : Trans M = transC2 M := by rw [← hMzT, hMc2]
  have hMkP0 : Marked (Pred M) 0 := Marked_Pred M 0 hM hlen hMk0 (by omega)
  have hc1 : transC1 M = Trans (Pred M) := by
    show Mark (Pred M) (transJm1 M) = Trans (Pred M)
    rw [hAdm0]
    exact Mark_zero_eq_Trans (Pred M) hpredR hMkP0
  have hmonoP : monoT (Pred M) = true := by
    simp [monoT, hzPred, hMkP0.2.2]
  obtain ⟨t, ht⟩ : ∃ t, Trans (Pred M) =
      Dprin (entry (Pred M) 1 0 : ℕ∞) t := by
    rcases Trans_mono_leftend_form (Pred M) hpredR hmonoP with h0 | h
    · exact absurd h0 ht1
    · exact h
  have hEPred : entry (Pred M) 1 0 = entry M 1 0 := entry_Pred_zero M 1 hlen
  have hV : transV M = (entry M 1 0 : ℕ∞) := by
    show bpHeadV (transC1 M) = (entry M 1 0 : ℕ∞)
    rw [hc1, ht, hEPred]
    simp [bpHeadV, Dprin]
  have pc1 : (PB (transC1 M)).length = 1 :=
    transC1_single_principal M hR hmono (by simp [transJ1, lastIdx]; omega)
      (by simpa [transT1] using ht1)
  have hc1D : transC1 M = Dprin (transV M) (transT2 M) :=
    principal_reconstruct pc1
  have hTPeq : Trans (Pred M) =
      Dprin (entry M 1 0 : ℕ∞) (transT2 M) := by
    rw [← hc1, hc1D, hV]
  exact ⟨hTPeq, hTc2⟩

/-- `bpHeadT (transC2 M)` は outer `transV` に依存せず、条件分岐、
`transT2`、末尾と親の行1値のみで決まる。 -/
private theorem bpHeadTTransC2Transport_vc (M N : PS)
    (h123 : (transCondI M || transCondIII M || transCondV M) =
      (transCondI N || transCondIII N || transCondV N))
    (hVI : transCondVI M = transCondVI N)
    (ht2 : transT2 M = transT2 N)
    (hLast : entry M 1 (lastIdx M) = entry N 1 (lastIdx N))
    (hPar : entry M 1 (lastParent M) = entry N 1 (lastParent N)) :
    bpHeadT (transC2 M) = bpHeadT (transC2 N) := by
  simp only [transC2, transC2Core]
  rw [h123, hVI, ht2, hLast, hPar]
  cases hA : (transCondI N || transCondIII N || transCondV N) <;>
    cases hB : transCondVI N <;>
    cases hZ : (transT2 N == BZero) <;>
    simp [hA, hB, hZ, Dprin, bpHeadT]

private theorem admFalseBelowAdmZero_vc (M : PS) (j k : ℕ)
    (hA0 : Adm M j = 0) (hkpos : 0 < k) (hkle : k ≤ j) :
    adm M k = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hk
  have hmax := Adm_max M k j hk hkle
  rw [hA0] at hmax
  omega

/-- Isabelle `vcx_bnd_strict` (layerB 76757)。regime の joint 境界が最終列の
親と一致するとき、親から末尾へ行1値も狭義に増加する。 -/
private theorem veBoundaryStrict_vc (m : ℕ) (Q : PS)
    (reg : VEReg m Q) (heq : VEj1p Q = Lng Q - 1)
    (hbnd : m = parent Q 0 (Lng Q - 1)) :
    entry Q 1 (parent Q 0 (Lng Q - 1)) < entry Q 1 (Lng Q - 1) ∧
      0 < entry Q 1 (Lng Q - 1) := by
  have regKeep := reg
  obtain ⟨hR, hmono, hBrne, hdisj⟩ := regKeep
  have hM : TPS Q := RTPS_TPS Q hR
  have hJ : (Br Q).length - 1 < (Br Q).length := by
    have := List.length_pos_of_ne_nil hBrne
    omega
  have hjoint : (Joints Q).getD ((Br Q).length - 1) 0 =
      parent Q 0 ((FirstNodes Q).getD ((Br Q).length - 1) 0) :=
    Joints_getD Q _ hJ
  have heq' := heq
  unfold VEj1p at heq'
  rw [heq'] at hjoint
  have hmJoint : m = (Joints Q).getD ((Br Q).length - 1) 0 := by
    rw [hjoint, hbnd]
  have hnlt : ¬m < (Joints Q).getD ((Br Q).length - 1) 0 := by omega
  have hdiag : entry Q 0 (Lng Q - 1) = entry Q 1 (Lng Q - 1) := by
    rcases hdisj with hlt | ⟨-, hd, -⟩
    · exact absurd hlt hnlt
    · rw [heq] at hd
      exact hd
  have hL : 1 < Lng Q := by
    have htb := TrMax_bound Q hM
    have hne : TrMax Q ≠ Lng Q - 1 := fun ht => hBrne (by simp [Br, ht])
    omega
  have hp : hasParent Q 0 (Lng Q - 1) = true :=
    mono_hasParent_row0 Q hM hmono (Lng Q - 1) (by omega) (by omega)
  have hnx : nextR Q 0 (parent Q 0 (Lng Q - 1)) (Lng Q - 1) = true :=
    hasParent_next_fseq Q 0 (Lng Q - 1) hp
  have hnx0 : nextrel0 Q (parent Q 0 (Lng Q - 1)) (Lng Q - 1) = true := by
    simpa [nextR] using hnx
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hnx0
  have hcoeff : entry Q 1 (parent Q 0 (Lng Q - 1)) ≤
      entry Q 0 (parent Q 0 (Lng Q - 1)) :=
    reduced_coeff Q hR _ (by omega)
  constructor <;> omega

/-- Host の `transJm1 = 0` は、正の offset で切った reduced terminal
slice の `transJm1` も `0` にする。Isabelle `vcx_collapse_VE` 内の
`tjm1slice` ブロック。 -/
private theorem transJm1RedTerminalSliceZero_vc (M : PS) (m : ℕ)
    (hR : RTPS M) (hmint : m < Lng M - 2)
    (hanc : leR M 0 m (Lng M - 1) = true)
    (hp : hasParent M 0 (Lng M - 1) = true)
    (hmp : m ≤ parent M 0 (Lng M - 1))
    (hmpos : 0 < m) (hAdm0 : transJm1 M = 0) :
    transJm1 (Red (seg M m (Lng M - 1))) = 0 := by
  have hM : TPS M := RTPS_TPS M hR
  have hmLast : m < Lng M - 1 := by omega
  let S := seg M m (Lng M - 1)
  let N := Red S
  have hsegT : TPS S := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng S
    simp [S]
    omega
  have hNlen : Lng N = Lng M - m := by
    simp only [N]
    rw [Lng_Red_invariance S hsegT]
    simp [S]
    omega
  have hJ0N : transJ0 N = transJ0 M - m := by
    simpa [N, S] using
      transJ0_Red_terminal_slice M m hR hmint hanc hp hmp
  have hfacts := ancestor_slice_Red_IncrFirst M m (Lng M - 1) hR hmLast
    (le_refl _) hanc
  have hread : S = IncrFirstN (entry M 0 m - entry M 1 m) N := by
    simpa [S, N] using hfacts.2.2
  have hA0 : Adm M (transJ0 M) = 0 := by
    simpa [transJm1] using hAdm0
  change Adm N (transJ0 N) = 0
  rw [hJ0N]
  by_cases hq0 : transJ0 M - m = 0
  · rw [hq0]
    simp [Adm, adm_zero]
  · have hall : ∀ k, 0 < k → k ≤ transJ0 M - m → adm N k = false := by
      intro k hkpos hkle
      have hmk : m + k ≤ transJ0 M := by omega
      have hhost : adm M (m + k) = false :=
        admFalseBelowAdmZero_vc M (transJ0 M) (m + k) hA0 (by omega) hmk
      have hj0lt : transJ0 M < Lng M - 1 := by
        simpa [transJ0, lastParent, lastIdx] using
          parent_lt_of_hasParent M 0 (Lng M - 1) hp
      have hsiff := adm_slice M m (m + k) (Lng M - 1) hM
        (by omega) (by omega) (le_refl _)
      have hSfalse : adm S k = false := by
        apply Bool.eq_false_of_not_eq_true
        intro hsTrue
        have hleft := hsiff.mpr (by simpa [S] using hsTrue)
        rcases hleft with ha | heq | heq
        · rw [hhost] at ha
          contradiction
        · omega
        · omega
      have hSN : adm S k = adm N k := by
        rw [hread, adm_IncrFirstN_vc2]
      rw [← hSN]
      exact hSfalse
    have hadm := Adm_adm N (transJ0 M - m)
    have hle := Adm_le N (transJ0 M - m)
    by_contra hne0
    have hpos : 0 < Adm N (transJ0 M - m) := Nat.pos_of_ne_zero hne0
    have hfalse := hall (Adm N (transJ0 M - m)) hpos hle
    rw [hfalse] at hadm
    contradiction

/-- Isabelle `vcx_collapse_VE` (layerB 76819)。`j₁' = j₁` かつ
`m ≮ transJm1 Q` の分岐を Adm0 の `transC2` 値化で閉じる。 -/
theorem veJ1eqCollapse_vc (m : ℕ) (Q : PS)
    (reg : VEReg m Q) (heq : VEj1p Q = Lng Q - 1)
    (hnonmin : TrMax Q + 2 < Lng Q)
    (IH : VEeq m (Pred Q)) (hmpos : 0 < m)
    (hnstr : ¬m < transJm1 Q) : VEeq m Q := by
  have regKeep := reg
  obtain ⟨hR, hmono, hBrne, hcases⟩ := regKeep
  have hM : TPS Q := RTPS_TPS Q hR
  have hmTr : m < TrMax Q := veReg_m_lt_TrMax_vc m Q reg
  have hJmLe : transJm1 Q ≤ m := by omega
  have hJmTr : transJm1 Q < TrMax Q := by omega
  have hAdmJ : adm Q (transJm1 Q) = true := by
    unfold transJm1
    exact Adm_adm Q (transJ0 Q)
  have hcasesJ := admLeTrMaxCases_vc Q (transJm1 Q) hM hAdmJ (by omega)
  have hAdm0 : transJm1 Q = 0 := by rcases hcasesJ with h | h <;> omega
  have hmint : m < Lng Q - 2 := by omega
  have hL3 : 2 < Lng Q := by omega
  have hL : 1 < Lng Q := by omega
  have hmLast : m < Lng Q - 1 := by omega
  have hp : hasParent Q 0 (Lng Q - 1) = true :=
    mono_hasParent_row0 Q hM hmono (Lng Q - 1) (by omega) (by omega)
  have hJ : (Br Q).length - 1 < (Br Q).length := by
    have := List.length_pos_of_ne_nil hBrne
    omega
  have hmleJoint : m ≤ (Joints Q).getD ((Br Q).length - 1) 0 := by
    rcases hcases with hlt | ⟨he, -, -⟩ <;> omega
  have hjoint : (Joints Q).getD ((Br Q).length - 1) 0 =
      parent Q 0 ((FirstNodes Q).getD ((Br Q).length - 1) 0) :=
    Joints_getD Q _ hJ
  have heq' := heq
  unfold VEj1p at heq'
  rw [heq'] at hjoint
  have hmp : m ≤ parent Q 0 (Lng Q - 1) := by
    rw [← hjoint]
    exact hmleJoint
  have hmonoSeg : monoT (seg Q m (Lng Q - 1)) = true :=
    mono_slice Q m (Lng Q - 1) hM hmono hmLast (le_refl _) hmleJoint
  have hle0 : le0 Q m (Lng Q - 1) = true :=
    le0_monoT_seg_into_list Q m (Lng Q - 1) (Lng Q - 1) hM hmonoSeg
      (by omega) (le_refl _) (by omega)
  have hanc : leR Q 0 m (Lng Q - 1) = true := by simpa [leR] using hle0

  let S := seg Q m (Lng Q - 1)
  let N := Red S
  have hsegT : TPS S := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng S
    simp [S]
    omega
  have hsegNonmulti : multiT S = false := by
    simpa [S, multiT] using (show multiT (seg Q m (Lng Q - 1)) = false by
      simp [multiT, hmonoSeg])
  have hNR : RTPS N := by
    simpa [N] using Red_nonmulti_RTPS S hsegT hsegNonmulti
  have hNmono : monoT N = true := by
    simpa [N, S] using Red_preserves_monoT_forward
      (seg Q m (Lng Q - 1)) (by simpa [S] using hsegT) hmonoSeg
  have hNlen : Lng N = Lng Q - m := by
    simp only [N]
    rw [Lng_Red_invariance S hsegT]
    simp [S]
    omega
  have hN3 : 2 < Lng N := by rw [hNlen]; omega
  have hNAdm0 : transJm1 N = 0 := by
    simpa [N, S] using transJm1RedTerminalSliceZero_vc
      Q m hR hmint hanc hp hmp hmpos hAdm0

  -- Endpoint / parent shifts and row-1 entry transport.
  have hlast : lastIdx N = lastIdx Q - m := by
    simp [lastIdx, hNlen]
    omega
  have hpar : lastParent N = lastParent Q - m := by
    simpa [N, S, transJ0] using
      transJ0_Red_terminal_slice Q m hR hmint hanc hp hmp
  have hlastBound : lastIdx N < Lng N := by simp [lastIdx]; omega
  have hparBound : lastParent N < Lng N := by
    have hparQLt : lastParent Q < lastIdx Q := by
      simpa [lastParent, lastIdx] using
        parent_lt_of_hasParent Q 0 (Lng Q - 1) hp
    omega
  have hmLastIdx : m ≤ lastIdx Q := by simp [lastIdx]; omega
  have hmLastPar : m ≤ lastParent Q := by
    simpa [lastParent, lastIdx] using hmp
  have hlastSum : m + lastIdx N = lastIdx Q := by rw [hlast]; omega
  have hparSum : m + lastParent N = lastParent Q := by rw [hpar]; omega
  have heLast : entry N 1 (lastIdx N) = entry Q 1 (lastIdx Q) := by
    have he := entry1_Red_terminal_slice Q m (lastIdx N) hR hmint hanc
      (by simpa [N, S] using hlastBound)
    exact he.trans (by rw [hlastSum])
  have hePar : entry N 1 (lastParent N) = entry Q 1 (lastParent Q) := by
    have he := entry1_Red_terminal_slice Q m (lastParent N) hR hmint hanc
      (by simpa [N, S] using hparBound)
    exact he.trans (by rw [hparSum])
  have hltAr : (lastParent N + 1 < lastIdx N) ↔
      lastParent Q + 1 < lastIdx Q := by omega
  have heqAr : (lastParent N + 1 = lastIdx N) ↔
      lastParent Q + 1 = lastIdx Q := by omega
  have hV : transCondV N = transCondV Q := by
    apply Bool.eq_iff_iff.mpr
    simp [transCondV, heLast, hePar, hltAr]
  have hVI : transCondVI N = transCondVI Q := by
    apply Bool.eq_iff_iff.mpr
    simp [transCondVI, heLast, hePar, heqAr]

  -- Conditions I/III are false on both sides. At the boundary use strict row-1 growth.
  have hA0par : Adm Q (lastParent Q) = 0 := by
    simpa [transJm1, transJ0] using hAdm0
  have hparQpos : 0 < lastParent Q := by
    simpa [lastParent, lastIdx] using (lt_of_lt_of_le hmpos hmp)
  have hadmQpar : adm Q (lastParent Q) = false :=
    admFalseBelowAdmZero_vc Q (lastParent Q) (lastParent Q) hA0par hparQpos (le_refl _)
  have hIQ : transCondI Q = false := by simp [transCondI, hadmQpar]
  have hIIIQ : transCondIII Q = false := by simp [transCondIII, hadmQpar]
  have hIN : transCondI N = false := by
    by_cases hbnd : m = parent Q 0 (Lng Q - 1)
    · have hs := veBoundaryStrict_vc m Q reg heq hbnd
      have hpos : 0 < entry N 1 (lastIdx N) := by rw [heLast]; exact hs.2
      simp [transCondI, hpos.ne']
    · have hparNpos : 0 < lastParent N := by
        simp [lastParent, lastIdx] at hbnd hpar ⊢
        omega
      have hA0N : Adm N (lastParent N) = 0 := by
        simpa [transJm1, transJ0] using hNAdm0
      have hadmN : adm N (lastParent N) = false :=
        admFalseBelowAdmZero_vc N (lastParent N) (lastParent N)
          hA0N hparNpos (le_refl _)
      simp [transCondI, hadmN]
  have hIIIN : transCondIII N = false := by
    by_cases hbnd : m = parent Q 0 (Lng Q - 1)
    · have hs := veBoundaryStrict_vc m Q reg heq hbnd
      have hlt : entry N 1 (lastParent N) < entry N 1 (lastIdx N) := by
        rw [hePar, heLast]
        simpa [lastParent, lastIdx] using hs.1
      have hnle : ¬entry N 1 (lastIdx N) ≤ entry N 1 (lastParent N) := by omega
      simp [transCondIII, hnle]
    · have hparNpos : 0 < lastParent N := by
        simp [lastParent, lastIdx] at hbnd hpar ⊢
        omega
      have hA0N : Adm N (lastParent N) = 0 := by
        simpa [transJm1, transJ0] using hNAdm0
      have hadmN : adm N (lastParent N) = false :=
        admFalseBelowAdmZero_vc N (lastParent N) (lastParent N)
          hA0N hparNpos (le_refl _)
      simp [transCondIII, hadmN]
  have h123 : (transCondI Q || transCondIII Q || transCondV Q) =
      (transCondI N || transCondIII N || transCondV N) := by
    rw [hIQ, hIIIQ, hIN, hIIIN, hV]

  -- The recursive VE hypothesis identifies the two `transT2` bodies.
  obtain ⟨hPredQ, hTransQ⟩ := adm0Setup_vc Q hR hmono (by omega) hAdm0
  obtain ⟨hPredN, hTransN⟩ := adm0Setup_vc N hNR hNmono (by omega) hNAdm0
  change bpHeadT (Trans (seg (Pred Q) m (Lng (Pred Q) - 1))) =
    bpHeadT (Trans (Pred Q)) at IH
  have hLP : Lng (Pred Q) = Lng Q - 1 := length_Pred Q hL
  have hsegPred : seg (Pred Q) m (Lng (Pred Q) - 1) =
      seg Q m (Lng Q - 2) := by
    simpa [hLP] using seg_Pred_eq Q m (Lng Q - 2) hL (by omega) (by omega)
  have hIHbody : bpHeadT (Trans (Pred Q)) = bpHeadT (Trans (Pred N)) := by
    have h := IH.symm
    rw [hsegPred, ← Trans_Pred_Red_terminal_slice Q m hmint] at h
    simpa [N, S] using h
  have ht2Q : bpHeadT (Trans (Pred Q)) = transT2 Q := by
    rw [hPredQ]
    simp [Dprin, bpHeadT]
  have ht2N : bpHeadT (Trans (Pred N)) = transT2 N := by
    rw [hPredN]
    simp [Dprin, bpHeadT]
  have ht2 : transT2 Q = transT2 N := ht2Q.symm.trans (hIHbody.trans ht2N)
  have htransport : bpHeadT (transC2 Q) = bpHeadT (transC2 N) :=
    bpHeadTTransC2Transport_vc Q N h123 hVI.symm ht2 heLast.symm hePar.symm

  unfold VEeq
  have hRed : Trans (seg Q m (Lng Q - 1)) = Trans N := by
    simpa [N, S] using Trans_Red (seg Q m (Lng Q - 1)) (by simpa [S] using hsegT)
  calc
    bpHeadT (Trans (seg Q m (Lng Q - 1))) = bpHeadT (Trans N) := by rw [hRed]
    _ = bpHeadT (transC2 N) := by rw [hTransN]
    _ = bpHeadT (transC2 Q) := htransport.symm
    _ = bpHeadT (Trans Q) := by rw [hTransQ]

/-- Isabelle `vcx_VEj1eq` (layerB 77061)。`j₁' = j₁` の VE step を
interior surgery と Adm0 collapse の二分岐で無条件化する。 -/
theorem veJ1eqResidual_holds (m : ℕ) : VEj1eqResidual m := by
  intro Q reg heq hnonmin _regP IH hmpos
  by_cases hstr : m < transJm1 Q
  · exact veJ1eqDeepen_vc m Q reg heq hnonmin hstr IH
  · exact veJ1eqCollapse_vc m Q reg heq hnonmin IH hmpos hstr

/-- Isabelle `bpax_VE_step` (layerB 65663)。`j₁' < j₁` の再帰領域における
VE の predecessor step。六つの slice/surgery 条件を上の無条件補題で閉じる。 -/
theorem bpaxVEstep_holds (m : ℕ) : BpaxVEstep m := by
  intro M reg hj₁lt regP IH
  have regKeep := reg
  obtain ⟨hR, hmono, -, -⟩ := regKeep
  have hcore := veStepRegimeCore m M reg hj₁lt
  obtain ⟨hL3, hmint, hmTr, hTrpar, -, hparlt, hanc, ht₁⟩ := hcore
  have hM : TPS M := RTPS_TPS M hR
  have hmLast : m < Lng M - 1 := by omega

  let N := Red (seg M m (Lng M - 1))
  have hsegT : TPS (seg M m (Lng M - 1)) := by
    intro hnil
    have hz : Lng (seg M m (Lng M - 1)) = 0 := by simp [hnil, Lng]
    rw [length_seg] at hz
    omega
  have hsegMono : monoT (seg M m (Lng M - 1)) = true :=
    mono_ancestor_slice M m (Lng M - 1) hM hmLast hanc
  have hsegNonmulti : multiT (seg M m (Lng M - 1)) = false := by
    simp [multiT, hsegMono]
  have hNR : RTPS N := by
    simpa [N] using
      Red_nonmulti_RTPS (seg M m (Lng M - 1)) hsegT hsegNonmulti
  have hNmono : monoT N = true := by
    simpa [N] using Red_preserves_monoT_forward
      (seg M m (Lng M - 1)) hsegT hsegMono
  have hNlen : Lng N = Lng M - m := by
    simp only [N]
    rw [Lng_Red_invariance _ hsegT, length_seg]
    omega
  have hN3 : 2 < Lng N := by
    rw [hNlen]
    omega
  have hNT : TPS N := RTPS_TPS N hNR
  have hpredNR : RTPS (Pred N) := RTPS_Pred N hNR
  have hpredNmono : monoT (Pred N) = true :=
    monoT_Pred_long N hNT hNmono hN3

  -- The recursive VE hypothesis is exactly equality of the two predecessor bodies.
  change bpHeadT (Trans (seg (Pred M) m (Lng (Pred M) - 1))) =
    bpHeadT (Trans (Pred M)) at IH
  have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M (by omega)
  have hsegPred :
      seg (Pred M) m (Lng (Pred M) - 1) = seg M m (Lng M - 2) := by
    simpa [hLP] using
      seg_Pred_eq M m (Lng M - 2) (by omega) (by omega) (by omega)
  have hIHbody :
      bpHeadT (Trans (Pred M)) = bpHeadT (Trans (Pred N)) := by
    have h := IH.symm
    rw [hsegPred, ← Trans_Pred_Red_terminal_slice M m hmint] at h
    simpa [N] using h

  -- Both predecessor translations are principal with the shared body from `IH`.
  let t := bpHeadT (Trans (Pred M))
  have pPM : Trans (Pred M) =
      Dprin (entry (Pred M) 1 0 : ℕ∞) t := by
    simpa [t] using Trans_principal_head (Pred M) regP.1 regP.2.1
  have pPN0 := Trans_principal_head (Pred N) hpredNR hpredNmono
  have pPN : Trans (Pred N) =
      Dprin (entry (Pred N) 1 0 : ℕ∞) t := by
    calc
      Trans (Pred N) = Dprin (entry (Pred N) 1 0 : ℕ∞)
          (bpHeadT (Trans (Pred N))) := pPN0
      _ = Dprin (entry (Pred N) 1 0 : ℕ∞) t := by rw [← hIHbody]
  have htPN : Trans (Pred N) ≠ BZero := by
    rw [pPN]
    simp [Dprin, BZero]

  -- Shared `c₁ ↦ c₂` surgery contexts on the host and its reduced slice.
  obtain ⟨sM, bM, dPM, dM⟩ :=
    transC1C2SharedScb_vc M hR hmono (by omega)
      (by simpa [transT1] using ht₁)
  obtain ⟨sN, bN, dPN0, dN0⟩ :=
    transC1C2SharedScb_vc N hNR hNmono (by omega) htPN
  obtain ⟨hc₁, hc₂⟩ := veStepCoreIdentities m M reg hj₁lt
  have dPN : scb_decomp (Trans (Pred N)) sN (flatBT (transC1 M)) bN := by
    simpa [hc₁] using dPN0
  have dN : scb_decomp (Trans N) sN (flatBT (transC2 M)) bN := by
    simpa [hc₂] using dN0
  have hsM : sM ≠ [] := veStepHostPrefixNonempty m M sM bM reg hj₁lt dPM
  have hsN : sN ≠ [] := by
    apply veStepSlicePrefixNonempty m M sN bN reg hj₁lt
    simpa [N] using dPN0
  have hMN : bpHeadT (Trans M) = bpHeadT (Trans N) :=
    veSurgeryBpHeadEq_vc dM dN dPM dPN pPM pPN hsM hsN

  unfold VEeq
  have hRed : Trans (seg M m (Lng M - 1)) = Trans N := by
    simpa [N] using Trans_Red (seg M m (Lng M - 1)) hsegT
  rw [hRed]
  exact hMN.symm

/-! ## キャップストーン（Isabelle `vcx_VE_all`, 77076） -/

/-- Isabelle `vcx_VE_all` (layerB 77076) の骨格から、二つの RPERS 分岐を
`rpj1eq_vc` / `bpaxRPERS_holds` で除去した front-facing 版。BASE 脚は
`8.2-condV-VE-base2` で全体を無条件に閉じたため、
この中間定理の残差は {`BpaxVEstep`, `VEj1eqResidual`}。 -/
theorem vcx_VE_all_modRPclosed (m : ℕ)
    (hstepBpax : BpaxVEstep m) (hstepJ1 : VEj1eqResidual m)
    (M : PS) (hM : VEReg m M) : VEeq m M :=
  vsx_VE_all_modResidual m
    (a0x_base_VE_vb2 m)
    hstepBpax hstepJ1 (bpaxRPERS_holds m) (rpj1eq_vc m) M hM

/-- BASE / RPERS / `BpaxVEstep` を無条件で閉じた front-facing 版。
残る明示的残差は `j₁' = j₁` 分岐の `VEj1eqResidual` のみ。 -/
theorem vcx_VE_all_modJ1closed (m : ℕ) (hstepJ1 : VEj1eqResidual m)
    (M : PS) (hM : VEReg m M) : VEeq m M :=
  vcx_VE_all_modRPclosed m (bpaxVEstep_holds m) hstepJ1 M hM

/-- Isabelle `vcx_VE_all` (layerB 77076): §8.2 terminal-slice value equation VE
の無条件 capstone。 -/
theorem vcx_VE_all (m : ℕ) (M : PS) (hM : VEReg m M) : VEeq m M :=
  vcx_VE_all_modJ1closed m (veJ1eqResidual_holds m) M hM

#print axioms rpj1eq_vc
#print axioms bpaxRPERS_holds
#print axioms veStepRegimeCore
#print axioms veStepDeepTailNonzero
#print axioms scbPrefixNonempty_of_transJm1_pos
#print axioms veStepHostPrefixNonempty
#print axioms veStepAncestry
#print axioms veStepCoreIdentities
#print axioms transJm1RedTerminalSlice_of_anchor
#print axioms markPredRedTerminalSlice_shift_of_anchor
#print axioms transC1RedTerminalSlice_of_anchor
#print axioms transC2RedTerminalSlice_of_anchor
#print axioms transCoreRedTerminalSlice_of_anchor
#print axioms veStepSlicePrefixNonempty
#print axioms veJ1eqDeepen_vc
#print axioms veJ1eqCollapse_vc
#print axioms veJ1eqResidual_holds
#print axioms bpaxVEstep_holds
#print axioms vcx_VE_all_modRPclosed
#print axioms vcx_VE_all_modJ1closed
#print axioms vcx_VE_all

end PSS
