import «8».«8.2-condIIIV-deep5»

/-!
# §8.2 条件(II)/(IV) VE34 deep4 残差の底（VE2 前置幾何 `vg2x_prefix_*` の無条件討伐）

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）の
  証明のうち、原文が `j₁ - TrMax M` に関する数学的帰納法で示すと述べている部分。
  `8.2-condIIIV-deep5` の `condIIIVterminalSlice_of_deep4` は `condIIIVts` フィールド
  （`CondIIIVterminalSlice`）を **六つの残差** `{VE2PrefixLastJoint, VE2PrefixEqdiag,
  VE3Base, VE3Step, VE4Base, VE4Step}` に還元した。本ファイルは筆頭の前置幾何残差
  `VE2PrefixLastJoint`（Isabelle `vg2x_prefix_LngBr` + `vg2x_prefix_joints`）を
  **無条件で討伐**し、`VE2PrefixEqdiag`（Isabelle `vg2x_eqdiag_M`, `ROW10` 依存）を
  N 依存の深い形から M レベルの sharp な単一残差 `EqdiagMlevel` に還元する。
- 訂正: なし（Isabelle 側で証明済みの補題の逐語移植、または名前付き Prop 骨格）。
- Isabelle（`isabelle/layerB/pss_wip.thy`, 92559–93055）:
  - `vg2x_prefix_geom` (92559): 前置辞 `N = seg M 0 (FirstNodes M ! K - 1)` の枝は
    `Br N = take K (Br M)`、幹は不変 `TrMax N = TrMax M`、境界 `TrMax M < K-th first node - 1
    < Lng M`。証明は幹以降の切片 `Y = seg M (TrMax M+1) (Lng M-1)` の `P`-prefix 安定性
    `P_take_at_boundary`（境界での成分 prefix 安定）に帰着。
  - `vg2x_prefix_fn`/`vg2x_prefix_joints`/`vg2x_prefix_entry`: 枝左端・joint・entry の移送。
    `Br N = take K (Br M)` から `IdxSum` を移送し、`Joints N ! J = Joints M ! J` を
    parent 一意性（`parent_eq_of_nextR0`）＋ offset-0 seg 保存（`nextR_seg_adm`）で導く。
  - `vg2x_eqdiag_M` (92870, `ROW10` 依存): 等 joint の下で最終枝頭が対角。`ROW10`
    （枝頭 row1 ≤ row0）を名前付き仮説で運ぶ。本ファイルでは M レベルの単一残差
    `EqdiagMlevel` に露出（`ROW10`＋`LastStep`=Min 特徴付けを吸収）。
- 帰結: `condIIIVts` フィールドを **五つの残差** `{EqdiagMlevel, VE3Base, VE3Step,
  VE4Base, VE4Step}` へ絞る（`condIIIVterminalSlice_of_deep3`）。VE2PrefixLastJoint は
  無条件討伐、VE2PrefixEqdiag は前置 entry 移送で M レベル残差へ還元。
- 依存 module: `8.2-condIIIV-deep5`（`VE2PrefixLastJoint`／`VE2PrefixEqdiag`／
  `condIIIVterminalSlice_of_deep4`／`condII_masterCF_of_deep4`／`VE3Base`/…／
  `strongmono_slice`／`LastStep`／`Br`/`Joints`/`FirstNodes`/`TrMax`/`entry`/`seg` を推移的に）。
- 状態: ⚠️ 部分（sorry 0、rc=0）。`VE2PrefixLastJoint` 無条件討伐、`VE2PrefixEqdiag` を
  `EqdiagMlevel` へ還元。残差は `{EqdiagMlevel, VE3Base, VE3Step, VE4Base, VE4Step}`。
- Private suffix: `_d4v`。
-/

namespace PSS

/-! ## 私的補助（suffix `_d4v`）

`8.2-strongmono-slice` の private 補題（`seg_take_sms`/`P_eq_single_sms`/
`P_take_at_boundary_sms`/`TrMax_seg_ancestor_sms`）の再掲。いずれも公開 §6 補題のみに
依存する（`P_multi_step`/`Pcut_props`/`P_concat`/`idxSum_getD`/`P_nonempty`/
`le_TrMax_intro_wd`/`TrMax_trunk_step`/`nextR1_seg_adm`/`TrMax_stop_uncond`）。 -/

/-- `(seg M a b).take c = seg M a (a + c - 1)`（Isabelle `take_seg`）。 -/
private theorem seg_take_d4v (M : PS) (a b c : ℕ) (_hc : 0 < c) (hcb : c ≤ b + 1 - a) :
    (seg M a b).take c = seg M a (a + c - 1) := by
  have h1 : a + c - 1 + 1 - a = c := by omega
  unfold seg
  rw [h1, ← List.map_take, List.range'_eq_map_range, ← List.map_take,
    List.take_range, Nat.min_eq_left hcb, List.range'_eq_map_range]

/-- 非 multi 段では `P M = [M]`。 -/
private theorem P_eq_single_d4v (M : PS)
    (hcond : (multiT M && decide (1 < Lng M)) = false) :
    P M = [M] := by
  unfold P
  cases hL : Lng M with
  | zero => rfl
  | succ f =>
      show PAux (f + 1) M = [M]
      simp only [PAux, hcond]
      simp

/-- 境界での P-prefix 安定性: 成分左端 `b = IdxSum(P M) ! K` で切ると
`P (take b M) = take K (P M)`（Isabelle `P_take_at_boundary`）。 -/
private theorem P_take_at_boundary_d4v (M : PS) (K : ℕ) (hM : TPS M)
    (hK1 : 1 ≤ K) (hKL : K ≤ (P M).length) :
    P (M.take ((IdxSum (P M)).getD K 0)) = (P M).take K := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M K with
  | h n ih =>
      by_cases hcond : (multiT M && decide (1 < Lng M)) = true
      · have hm : multiT M = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          exact hcond.1
        have hlen : 1 < Lng M := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          exact hcond.2
        have hstep := P_multi_step M hm hlen
        have hpc := Pcut_props M hlen
        have hpcL : Pcut M < Lng M := by omega
        have hFlen : Lng (M.take (Pcut M)) = Pcut M := by
          simp [Nat.min_eq_left hpcL.le]
        have hFT : TPS (M.take (Pcut M)) := by
          apply List.ne_nil_of_length_pos
          change 0 < Lng (M.take (Pcut M))
          omega
        have hlenP : (P M).length = (P (M.take (Pcut M))).length + 1 := by
          rw [hstep]
          simp
        have hFtotal : (((P (M.take (Pcut M))).map Lng).sum) = Pcut M := by
          have hcat := P_concat (M.take (Pcut M))
          calc ((P (M.take (Pcut M))).map Lng).sum
              = Lng ((P (M.take (Pcut M))).flatten) := by
                simp [List.length_flatten]
            _ = Pcut M := by rw [hcat]; exact hFlen
        rcases Nat.lt_or_ge K ((P M).length) with hKlt | hKge
        · have hKF : K ≤ (P (M.take (Pcut M))).length := by omega
          have hb : (IdxSum (P M)).getD K 0
              = (IdxSum (P (M.take (Pcut M)))).getD K 0 := by
            rw [idxSum_getD (P M) K hKL,
              idxSum_getD (P (M.take (Pcut M))) K hKF, hstep,
              List.take_append_of_le_length hKF]
          have hble : (IdxSum (P (M.take (Pcut M)))).getD K 0 ≤ Pcut M := by
            rw [idxSum_getD (P (M.take (Pcut M))) K hKF]
            calc ((((P (M.take (Pcut M))).take K).map Lng).sum)
                ≤ (((P (M.take (Pcut M))).map Lng).sum) := by
                  conv_rhs => rw [← List.take_append_drop K (P (M.take (Pcut M)))]
                  rw [List.map_append, List.sum_append]
                  exact Nat.le_add_right _ _
              _ = Pcut M := hFtotal
          have htk : M.take ((IdxSum (P (M.take (Pcut M)))).getD K 0)
              = (M.take (Pcut M)).take ((IdxSum (P (M.take (Pcut M)))).getD K 0) := by
            rw [List.take_take, Nat.min_eq_left hble]
          have hIH := ih (Lng (M.take (Pcut M))) (by omega)
            (M.take (Pcut M)) K hFT hK1 hKF rfl
          rw [hb, htk, hIH, hstep, List.take_append_of_le_length hKF]
        · have hKeq : K = (P M).length := by omega
          have hball : (IdxSum (P M)).getD K 0 = Lng M := by
            rw [hKeq, idxSum_getD (P M) (P M).length (le_refl _), List.take_length]
            have hcat := P_concat M
            calc ((P M).map Lng).sum
                = Lng ((P M).flatten) := by simp [List.length_flatten]
              _ = Lng M := by rw [hcat]
          rw [hball, List.take_length, hKeq, List.take_length]
      · have hone := P_eq_single_d4v M (by simpa using hcond)
        have hK : K = 1 := by
          rw [hone] at hKL
          simp at hKL
          omega
        have hb : (IdxSum (P M)).getD K 0 = Lng M := by
          rw [hK, idxSum_getD (P M) 1 (by rw [hone]; simp), hone]
          simp
        rw [hb, List.take_length, hK, hone]
        simp

/-- `leR M 0 a b` は両添字を `Lng M` 未満に閉じ込める（入口 `leR0_bounds_d5` の再掲）。 -/
private theorem leR0_bounds_d4v (M : PS) (a b : ℕ)
    (h : leR M 0 a b = true) : a < Lng M ∧ b < Lng M := by
  have h0 : le0 M a b = true := by simpa [leR] using h
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at h0
  exact ⟨h0.1.1, h0.1.2⟩

/-- 枝の左端は `Lng` 未満（Isabelle `a1_FN_lt`, `FN_lt_d5` の再掲）。 -/
private theorem FN_lt_d4v (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) : (FirstNodes M).getD J 0 < Lng M :=
  (leR0_bounds_d4v M _ _
    (nextR_implies_row0 M 0 _ _ (Joints_nextR_FirstNodes M J hM hmono hJ)).2).2

/-- 幹根切片の幹の整列（Isabelle `TrMax_seg_ancestor`）:
`j₀' ≤ TrMax M < j₁' < Lng M` なら `TrMax (seg M j₀' j₁') = TrMax M - j₀'`。 -/
private theorem TrMax_seg_ancestor_d4v (M : PS) (j₀' j₁' : ℕ) (hM : TPS M)
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

/-! ## 前置枝の幾何（Isabelle `vg2x_prefix_geom`, 92559）

前置辞 `N = seg M 0 (FirstNodes M ! K - 1)` の枝は `Br N = take K (Br M)`、幹は不変
`TrMax N = TrMax M`、境界は `TrMax M < FirstNodes M ! K - 1 < Lng M`。証明は幹以降の
切片 `Y = seg M (TrMax M+1) (Lng M-1)` の P-prefix 安定性 `P_take_at_boundary_d4v` に帰着。 -/

/-- **Isabelle `vg2x_prefix_geom` (layerB 92559) の Br 連言＋幹不変＋境界（無条件）**。 -/
private theorem prefix_geom_d4v (M : PS) (K : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hK : 0 < K) (hKL : K < (Br M).length) :
    Br (seg M 0 ((FirstNodes M).getD K 0 - 1)) = (Br M).take K
      ∧ TrMax (seg M 0 ((FirstNodes M).getD K 0 - 1)) = TrMax M
      ∧ TrMax M < (FirstNodes M).getD K 0 - 1
      ∧ (FirstNodes M).getD K 0 - 1 < Lng M := by
  have hBrne : Br M ≠ [] := by
    intro h; rw [h] at hKL; simp at hKL
  have hne : TrMax M ≠ Lng M - 1 := fun heq => hBrne (by simp [Br, heq])
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hTrb : TrMax M ≤ Lng M - 1 := TrMax_bound M hM
  have hTrlt : TrMax M < Lng M - 1 := by omega
  set Y := seg M (TrMax M + 1) (Lng M - 1) with hYdef
  have hBrM : Br M = P Y := by simp [Br, hne, hYdef]
  have hYlen : Lng Y = Lng M - 1 - TrMax M := by rw [hYdef, length_seg]; omega
  have hYT : TPS Y := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng Y; rw [hYlen]; omega
  have hfn : (FirstNodes M).getD K 0 = TrMax M + 1 + (IdxSum (Br M)).getD K 0 :=
    FirstNodes_getD M K hKL
  have hidx1 : 1 ≤ (IdxSum (Br M)).getD K 0 := by
    have hle1K : (IdxSum (Br M)).getD 1 0 ≤ (IdxSum (Br M)).getD K 0 :=
      idxSum_mono (Br M) 1 K hK hKL.le
    have hPYpos : 0 < (P Y).length := List.length_pos_of_ne_nil (P_nonempty Y)
    have hc0 : 0 < Lng ((P Y).getD 0 []) := P_component_nonempty Y 0 hYT hPYpos
    have h1v : (IdxSum (Br M)).getD 1 0 = Lng ((Br M).getD 0 []) := by
      rw [idxSum_getD (Br M) 1 (by omega)]
      have hcons : (Br M).take 1 = [(Br M).getD 0 []] := by
        cases hB : Br M with
        | nil => exact absurd hB hBrne
        | cons x xs => simp
      rw [hcons]; simp
    rw [← hBrM] at hc0
    omega
  set b := (FirstNodes M).getD K 0 - 1 with hbdef
  have hbval : b = TrMax M + (IdxSum (Br M)).getD K 0 := by rw [hbdef, hfn]; omega
  have hbgt : TrMax M < b := by omega
  have hblt : b < Lng M := by
    have := FN_lt_d4v M K hM hmono hKL; omega
  have hTrN : TrMax (seg M 0 b) = TrMax M := by
    have := TrMax_seg_ancestor_d4v M 0 b hM (Nat.zero_le _) hbgt hblt; simpa using this
  refine ⟨?_, hTrN, hbgt, hblt⟩
  have htrneN : TrMax (seg M 0 b) ≠ Lng (seg M 0 b) - 1 := by
    rw [hTrN, length_seg]; omega
  have hBrN : Br (seg M 0 b) = P (seg M (TrMax M + 1) b) := by
    rw [Br_seg_reshape_68 M 0 b (by omega) hblt htrneN, hTrN, Nat.zero_add]
  have hsegY : seg M (TrMax M + 1) b = Y.take ((IdxSum (Br M)).getD K 0) := by
    have hh := seg_take_d4v M (TrMax M + 1) (Lng M - 1) (b - TrMax M) (by omega) (by omega)
    have hc : b - TrMax M = (IdxSum (Br M)).getD K 0 := by omega
    rw [hc] at hh
    have harr : TrMax M + 1 + (IdxSum (Br M)).getD K 0 - 1 = b := by omega
    rw [harr] at hh
    rw [hYdef]; exact hh.symm
  have hKPY : K ≤ (P Y).length := by rw [← hBrM]; exact hKL.le
  have hboundary : P (Y.take ((IdxSum (P Y)).getD K 0)) = (P Y).take K :=
    P_take_at_boundary_d4v Y K hYT hK hKPY
  have hidxeq : (IdxSum (P Y)).getD K 0 = (IdxSum (Br M)).getD K 0 := by rw [hBrM]
  rw [hBrN, hsegY, ← hidxeq, hboundary, ← hBrM]

/-! ## 枝左端・joint・entry の移送（Isabelle `vg2x_prefix_fn`/`_joints`/`_entry`）

`Br N = take K (Br M)` から先頭 `K` 枝の `FirstNodes`／`Joints`／`entry` が `M` と一致する。 -/

/-- **Isabelle `vg2x_prefix_fn` (layerB 92710) の逐語移植**: 先頭 `K` 枝の左端一致。 -/
private theorem prefix_fn_d4v (M : PS) (K J : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hK : 0 < K) (hKL : K < (Br M).length) (hJK : J < K) :
    (FirstNodes (seg M 0 ((FirstNodes M).getD K 0 - 1))).getD J 0
      = (FirstNodes M).getD J 0 := by
  obtain ⟨hBrN, hTrN, _, _⟩ := prefix_geom_d4v M K hM hmono hK hKL
  set N := seg M 0 ((FirstNodes M).getD K 0 - 1) with hNdef
  have hBrNlen : (Br N).length = K := by rw [hBrN, List.length_take]; omega
  have hJBrN : J < (Br N).length := by rw [hBrNlen]; exact hJK
  have hJBrM : J < (Br M).length := lt_trans hJK hKL
  have hfnN : (FirstNodes N).getD J 0 = TrMax N + 1 + (IdxSum (Br N)).getD J 0 :=
    FirstNodes_getD N J hJBrN
  have hfnM : (FirstNodes M).getD J 0 = TrMax M + 1 + (IdxSum (Br M)).getD J 0 :=
    FirstNodes_getD M J hJBrM
  have hidxeq : (IdxSum (Br N)).getD J 0 = (IdxSum (Br M)).getD J 0 := by
    rw [hBrN,
      idxSum_getD ((Br M).take K) J (by rw [List.length_take]; omega),
      idxSum_getD (Br M) J hJBrM.le, List.take_take, Nat.min_eq_left hJK.le]
  rw [hfnN, hTrN, hidxeq, ← hfnM]

/-- **Isabelle `vg2x_prefix_joints` (layerB 92780) の移植**: 先頭 `K` 枝の joint 一致。
offset-0 seg 保存 `nextR_seg_adm` ＋ parent 一意性 `parent_eq_of_nextR0`。 -/
private theorem prefix_joints_d4v (M : PS) (K J : ℕ) (hMD : DTPS M)
    (hK : 0 < K) (hKL : K < (Br M).length) (hJK : J < K) :
    (Joints (seg M 0 ((FirstNodes M).getD K 0 - 1))).getD J 0
      = (Joints M).getD J 0 := by
  obtain ⟨hR, hmono, _⟩ := (DTPS_iff M).mp hMD
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨hBrN, hTrN, hbgt, hblt⟩ := prefix_geom_d4v M K hM hmono hK hKL
  set N := seg M 0 ((FirstNodes M).getD K 0 - 1) with hNdef
  have hBrNlen : (Br N).length = K := by rw [hBrN, List.length_take]; omega
  have hJBrN : J < (Br N).length := by rw [hBrNlen]; exact hJK
  have hJBrM : J < (Br M).length := lt_trans hJK hKL
  have hb0 : 0 < (FirstNodes M).getD K 0 - 1 := by omega
  have hbLe : (FirstNodes M).getD K 0 - 1 ≤ Lng M - 1 := by omega
  have hND : DTPS N := strongmono_slice M 0 _ hMD hb0 hbLe (Nat.zero_le _)
  obtain ⟨hNR, hNmono, _⟩ := (DTPS_iff _).mp hND
  have hNT : TPS N := RTPS_TPS N hNR
  have hfnNeq : (FirstNodes N).getD J 0 = (FirstNodes M).getD J 0 :=
    prefix_fn_d4v M K J hM hmono hK hKL hJK
  have hFNNlt : (FirstNodes N).getD J 0 < Lng N := FN_lt_d4v N J hNT hNmono hJBrN
  have hLngN : Lng N = (FirstNodes M).getD K 0 - 1 + 1 := by rw [hNdef, length_seg]; omega
  have hfnMlt : (FirstNodes M).getD J 0 < Lng N := by rw [← hfnNeq]; exact hFNNlt
  have hJMle : (Joints M).getD J 0 ≤ TrMax M := (FirstNodes_TrMax_Joints M J hM hmono hJBrM).1
  have hJMlt : (Joints M).getD J 0 < Lng N := by rw [hLngN]; omega
  have hnxM : nextR M 0 ((Joints M).getD J 0) ((FirstNodes M).getD J 0) = true :=
    Joints_nextR_FirstNodes M J hM hmono hJBrM
  have hnxN : nextR N 0 ((Joints M).getD J 0) ((FirstNodes M).getD J 0) = true := by
    have h := nextR_seg_adm M 0 ((FirstNodes M).getD K 0 - 1) 0
      ((Joints M).getD J 0) ((FirstNodes M).getD J 0) (Nat.zero_le _) hblt
      (by simpa [hNdef] using hJMlt) (by simpa [hNdef] using hfnMlt)
    rw [hNdef, h]; simpa using hnxM
  have hpar : parent N 0 ((FirstNodes M).getD J 0) = (Joints M).getD J 0 :=
    parent_eq_of_nextR0 N ((Joints M).getD J 0) ((FirstNodes M).getD J 0) hnxN
  rw [Joints_getD N J hJBrN, hfnNeq, hpar]

/-- **Isabelle `vg2x_prefix_entry` (layerB 92744) の移植**: 先頭 `K` 枝左端での entry 一致。 -/
private theorem prefix_entry_d4v (M : PS) (K J i : ℕ) (hMD : DTPS M)
    (hK : 0 < K) (hKL : K < (Br M).length) (hJK : J < K) :
    entry (seg M 0 ((FirstNodes M).getD K 0 - 1)) i
        ((FirstNodes (seg M 0 ((FirstNodes M).getD K 0 - 1))).getD J 0)
      = entry M i ((FirstNodes M).getD J 0) := by
  obtain ⟨hR, hmono, _⟩ := (DTPS_iff M).mp hMD
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨hBrN, hTrN, hbgt, hblt⟩ := prefix_geom_d4v M K hM hmono hK hKL
  set N := seg M 0 ((FirstNodes M).getD K 0 - 1) with hNdef
  have hBrNlen : (Br N).length = K := by rw [hBrN, List.length_take]; omega
  have hJBrN : J < (Br N).length := by rw [hBrNlen]; exact hJK
  have hfnNeq : (FirstNodes N).getD J 0 = (FirstNodes M).getD J 0 :=
    prefix_fn_d4v M K J hM hmono hK hKL hJK
  have hb0 : 0 < (FirstNodes M).getD K 0 - 1 := by omega
  have hbLe : (FirstNodes M).getD K 0 - 1 ≤ Lng M - 1 := by omega
  have hND : DTPS N := strongmono_slice M 0 _ hMD hb0 hbLe (Nat.zero_le _)
  obtain ⟨hNR, hNmono, _⟩ := (DTPS_iff _).mp hND
  have hNT : TPS N := RTPS_TPS N hNR
  have hFNNlt : (FirstNodes N).getD J 0 < Lng N := FN_lt_d4v N J hNT hNmono hJBrN
  have hbnd : (FirstNodes M).getD J 0 < Lng (seg M 0 ((FirstNodes M).getD K 0 - 1)) := by
    have h := hFNNlt; rw [hfnNeq, hNdef] at h; exact h
  rw [hfnNeq, hNdef, entry_seg M 0 ((FirstNodes M).getD K 0 - 1) i
    ((FirstNodes M).getD J 0) hbnd]
  simp

/-! ## `VE2PrefixLastJoint` の無条件討伐（Isabelle `vg2x_prefix_LngBr` + `vg2x_prefix_joints`）

前置辞 `N = seg M 0 (FirstNodes M ! LastStep - 1)` の枝は非空（`Lng(Br N) = LastStep > 0`）で、
その最終 joint は `M` の `LastStep-1` 番目の joint に一致する（joint 移送 at `J = LastStep-1`）。 -/

/-- **前置枝・最終 joint 残差の無条件討伐**（deep5 `VE2PrefixLastJoint`）。 -/
theorem VE2PrefixLastJoint_holds : VE2PrefixLastJoint := by
  intro M hMD hBrne hLS0
  obtain ⟨hR, hmono, _⟩ := (DTPS_iff M).mp hMD
  have hM : TPS M := RTPS_TPS M hR
  have hKL : LastStep M < (Br M).length := LastStep_lt_Lng_Br M hBrne
  obtain ⟨hBrN, _, _, _⟩ := prefix_geom_d4v M (LastStep M) hM hmono hLS0 hKL
  have hBrNlen : (Br (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1))).length = LastStep M := by
    rw [hBrN, List.length_take]; omega
  refine ⟨List.ne_nil_of_length_pos (by rw [hBrNlen]; exact hLS0), ?_⟩
  have hidx : (Br (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1))).length - 1 = LastStep M - 1 := by
    rw [hBrNlen]
  rw [hidx]
  exact prefix_joints_d4v M (LastStep M) (LastStep M - 1) hMD hLS0 hKL (by omega)

/-! ## `VE2PrefixEqdiag` を M レベル残差 `EqdiagMlevel` に還元（Isabelle `vg2x_eqdiag_M`）

前置対角化残差 `VE2PrefixEqdiag`（N 依存）は、前置 entry 移送 `prefix_entry_d4v` により
M レベルの単一残差 `EqdiagMlevel`（`vg2x_eqdiag_M` の結論、`ROW10`＋`LastStep`=Min 特徴付けを
吸収）に還元される。 -/

/-- **M レベル対角化残差**（Isabelle `vg2x_eqdiag_M` 92870 の結論、`ROW10` modulo）:
`0 < LastStep M` の非幹脚で、最終枝ガード（行1 < 行0）と等 joint
`Joints M ! (LastStep-1) = Joints M ! (Br.length-1)` の下で、`M` の `LastStep-1` 番目の
枝頭は対角（行0 = 行1）。`ROW10`（枝頭 row1 ≤ row0）と `LastStep`=Min 特徴付けを吸収。 -/
def EqdiagMlevel : Prop :=
  ∀ M : PS, DTPS M → Br M ≠ [] → 0 < LastStep M →
    entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
      < entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) →
    (Joints M).getD (LastStep M - 1) 0 = (Joints M).getD ((Br M).length - 1) 0 →
    entry M 0 ((FirstNodes M).getD (LastStep M - 1) 0)
      = entry M 1 ((FirstNodes M).getD (LastStep M - 1) 0)

/-- **前置対角化残差の M レベル還元**（`prefix_entry_d4v` 移送）: `EqdiagMlevel` から
deep5 `VE2PrefixEqdiag` を放出する。 -/
theorem VE2PrefixEqdiag_of_Mlevel (hEq : EqdiagMlevel) : VE2PrefixEqdiag := by
  intro M hMD hBrne hLS0 hguard heqJ
  obtain ⟨hR, hmono, _⟩ := (DTPS_iff M).mp hMD
  have hM : TPS M := RTPS_TPS M hR
  have hKL : LastStep M < (Br M).length := LastStep_lt_Lng_Br M hBrne
  obtain ⟨hBrN, _, _, _⟩ := prefix_geom_d4v M (LastStep M) hM hmono hLS0 hKL
  have hBrNlen : (Br (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1))).length = LastStep M := by
    rw [hBrN, List.length_take]; omega
  have hidx : (Br (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1))).length - 1 = LastStep M - 1 := by
    rw [hBrNlen]
  have hJK : LastStep M - 1 < LastStep M := by omega
  have hMeqdiag := hEq M hMD hBrne hLS0 hguard heqJ
  have hT0 := prefix_entry_d4v M (LastStep M) (LastStep M - 1) 0 hMD hLS0 hKL hJK
  have hT1 := prefix_entry_d4v M (LastStep M) (LastStep M - 1) 1 hMD hLS0 hKL hJK
  rw [hidx, hT0, hT1, hMeqdiag]

/-! ## 五残差版キャップストーン

`VE2PrefixLastJoint` を無条件討伐、`VE2PrefixEqdiag` を `EqdiagMlevel` へ還元し、
`8.2-condIIIV-deep5` の六残差版 `condIIIVterminalSlice_of_deep4` に差し込む。これで
`condIIIVts` フィールドの無条件形 `CondIIIVterminalSlice` を**五つの残差**
`{EqdiagMlevel, VE3Base, VE3Step, VE4Base, VE4Step}` ちょうどに絞る。 -/

/-- **五残差版キャップストーン**: `condIIIVts` フィールドを
`{EqdiagMlevel, VE3Base, VE3Step, VE4Base, VE4Step}` から供給する。 -/
theorem condIIIVterminalSlice_of_deep3
    (hEqM : EqdiagMlevel)
    (hV3b : VE3Base) (hV3s : VE3Step) (hV4b : VE4Base) (hV4s : VE4Step) :
    CondIIIVterminalSlice :=
  condIIIVterminalSlice_of_deep4
    VE2PrefixLastJoint_holds (VE2PrefixEqdiag_of_Mlevel hEqM) hV3b hV3s hV4b hV4s

/-- 五残差から condII 停止性フィールド `CondII_masterCF`（`8.3-TransCondII-engine`）を
供給する（`8.2-condIIIV-deep5` の `condII_masterCF_of_deep4` へ橋渡し）。 -/
theorem condII_masterCF_of_deep3
    (hEqM : EqdiagMlevel)
    (hV3b : VE3Base) (hV3s : VE3Step) (hV4b : VE4Base) (hV4s : VE4Step) :
    CondII_masterCF :=
  condII_masterCF_of_deep4
    VE2PrefixLastJoint_holds (VE2PrefixEqdiag_of_Mlevel hEqM) hV3b hV3s hV4b hV4s

/-! ## 転記の数値検証（前置幾何討伐の量化域が非空）

witness `M = (0,0)(1,1)(2,2)(1,1)(2,2)(1,1)(2,2)` は `DT_PS`・`Br ≠ []`・`0 < LastStep`
（deep5 と共通の非幹脚ホスト）に属し、`VE2PrefixLastJoint_holds`／`EqdiagMlevel` の
量化域が非空であることを保証する。 -/

#guard decide (DTPS [(0,0),(1,1),(2,2),(1,1),(2,2),(1,1),(2,2)] ∧
  Br [(0,0),(1,1),(2,2),(1,1),(2,2),(1,1),(2,2)] ≠ [] ∧
  0 < LastStep [(0,0),(1,1),(2,2),(1,1),(2,2),(1,1),(2,2)]) = true

#print axioms VE2PrefixLastJoint_holds
#print axioms VE2PrefixEqdiag_of_Mlevel
#print axioms condIIIVterminalSlice_of_deep3
#print axioms condII_masterCF_of_deep3

end PSS
