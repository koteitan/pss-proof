import «8».«8.2-standard-slice-Red-strongmono»
import «6».«6.4-mono-slice»
import «6».«6.4-FirstNodes-TrMax-Joints»
import «6».«6.4-P-IdxSum-characterization»
import «6».«6.4-P-leftend-mono»
import «6».«6.4-P-IdxSum»
import «6».«6.6-ancestor-slice-Red-IncrFirst»
import «6».«6.6-reduced-leftend»
import «6».«6.6-reduced-iff-condAB»
import «6».«6.5-Red-le-core»
import «6».«6.5-Red-welldefined»
import «6».«6.3-adm-slice»
import «6».«6.2-P-additivity»
import «6».«6.2-mono-ancestor-slice»
import «6».«6.8-standard-slice-Br-descending»

/-!
# §8.2 補題（強単項性の切片への遺伝性）

- 原文: `tmp/content.md` 3328 付近
- 訂正: なし
- Isabelle: `p_8_2_strongmono_slice` (isabelle/pss_paper.thy:1509) の証明は
             `m_8_2_strongmono_slice` (isabelle/layerB/pss_wip.thy:27757、
             mono+reduced 部は `m_8_2_strongmono_slice_mono_reduced` 27395)
- 依存: `8.2-standard-slice-Red-strongmono`（`DTPS`/`descendingB` の定義と展開 API）、
  §6.2/6.4/6.5/6.6 の公開補題群（本文参照）
- 状態: ✅ 証明済（sorry 0）

`M ∈ DT_PS` の幹根切片 `M' = (M_j)_{j=j₀'}^{j₁'}`（`j₀' ≤ Joints(M)_{J₁}`）は
`DT_PS`。mono は `mono_slice`、reduced は幹対角性（簡約形の幹は対角）で
`IncrFirst` 指数が 0 になること、`Br` の降順性は **P-take 境界対応**で `M` から
輸送する: `Br M' = P (take c Y)`、`Br M = P Y`（`Y` = 幹以降の切片）で、成分左端
（= 左最小値位置、`P_IdxSum_char`）は `take` で不変なので先頭 `len(Br M')` 成分の
頭が一致する。鍵は `P (take (IdxSum(P M)!K) M) = take K (P M)`（境界での
P-prefix 安定性、Isabelle `P_take_at_boundary`/`P_take_prefix_eq` の Lean 版）。
-/

namespace PSS

/-! ## seg の take 表示 -/

private theorem seg_take_sms (M : PS) (a b c : ℕ) (_hc : 0 < c) (hcb : c ≤ b + 1 - a) :
    (seg M a b).take c = seg M a (a + c - 1) := by
  have h1 : a + c - 1 + 1 - a = c := by omega
  unfold seg
  rw [h1, ← List.map_take, List.range'_eq_map_range, ← List.map_take,
    List.take_range, Nat.min_eq_left hcb, List.range'_eq_map_range]

/-! ## `P` の単成分ケースと境界での take 安定性 -/

private theorem P_eq_single_sms (M : PS)
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
private theorem P_take_at_boundary_sms (M : PS) (K : ℕ) (hM : TPS M)
    (hK1 : 1 ≤ K) (hKL : K ≤ (P M).length) :
    P (M.take ((IdxSum (P M)).getD K 0)) = (P M).take K := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M K with
  | h n ih =>
      by_cases hcond : (multiT M && decide (1 < Lng M)) = true
      · -- multi 段: P M = P (take pc M) ++ [drop pc M]
        have hm : multiT M = true := by
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
        -- 前半成分の総長 = Pcut M
        have hFtotal : (((P (M.take (Pcut M))).map Lng).sum) = Pcut M := by
          have hcat := P_concat (M.take (Pcut M))
          calc ((P (M.take (Pcut M))).map Lng).sum
              = Lng ((P (M.take (Pcut M))).flatten) := by
                simp [List.length_flatten]
            _ = Pcut M := by rw [hcat]; exact hFlen
        rcases Nat.lt_or_ge K ((P M).length) with hKlt | hKge
        · -- K ≤ 前半成分数
          have hKF : K ≤ (P (M.take (Pcut M))).length := by omega
          -- b = IdxSum (P M) ! K = 前半の IdxSum ! K
          have hb : (IdxSum (P M)).getD K 0
              = (IdxSum (P (M.take (Pcut M)))).getD K 0 := by
            rw [idxSum_getD (P M) K hKL,
              idxSum_getD (P (M.take (Pcut M))) K hKF, hstep,
              List.take_append_of_le_length hKF]
          -- b ≤ Pcut M
          have hble : (IdxSum (P (M.take (Pcut M)))).getD K 0 ≤ Pcut M := by
            rw [idxSum_getD (P (M.take (Pcut M))) K hKF]
            calc ((((P (M.take (Pcut M))).take K).map Lng).sum)
                ≤ (((P (M.take (Pcut M))).map Lng).sum) := by
                  conv_rhs => rw [← List.take_append_drop K (P (M.take (Pcut M)))]
                  rw [List.map_append, List.sum_append]
                  exact Nat.le_add_right _ _
              _ = Pcut M := hFtotal
          -- take b M = take b (take pc M)
          have htk : M.take ((IdxSum (P (M.take (Pcut M)))).getD K 0)
              = (M.take (Pcut M)).take ((IdxSum (P (M.take (Pcut M)))).getD K 0) := by
            rw [List.take_take, Nat.min_eq_left hble]
          have hIH := ih (Lng (M.take (Pcut M))) (by omega)
            (M.take (Pcut M)) K hFT hK1 hKF rfl
          rw [hb, htk, hIH, hstep, List.take_append_of_le_length hKF]
        · -- K = 全成分数: b = Lng M、両辺とも P M
          have hKeq : K = (P M).length := by omega
          have hball : (IdxSum (P M)).getD K 0 = Lng M := by
            rw [hKeq, idxSum_getD (P M) (P M).length (le_refl _), List.take_length]
            have hcat := P_concat M
            calc ((P M).map Lng).sum
                = Lng ((P M).flatten) := by simp [List.length_flatten]
              _ = Lng M := by rw [hcat]
          rw [hball, List.take_length, hKeq, List.take_length]
      · -- 非 multi 段: P M = [M]、K = 1 のみ
        have hone := P_eq_single_sms M (by simpa using hcond)
        have hK : K = 1 := by
          rw [hone] at hKL
          simp at hKL
          omega
        have hb : (IdxSum (P M)).getD K 0 = Lng M := by
          rw [hK, idxSum_getD (P M) 1 (by rw [hone]; simp), hone]
          simp
        rw [hb, List.take_length, hK, hone]
        simp

/-- 一般カット `c` での P-prefix 安定性（Isabelle `P_take_prefix_eq`）:
`J < len(P (take c Y))` なら先頭 `J` 成分は `P Y` と一致し、`J` は `P Y` の
成分数未満。 -/
private theorem P_take_prefix_eq_sms (Y : PS) (c J : ℕ) (hYT : TPS Y)
    (hc0 : 0 < c) (hcY : c ≤ Lng Y)
    (hJ : J < (P (Y.take c)).length) :
    (P (Y.take c)).take J = (P Y).take J ∧ J < (P Y).length := by
  have hYpos : 0 < Lng Y := List.length_pos_of_ne_nil hYT
  have hcT : TPS (Y.take c) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (Y.take c)
    simp [Nat.min_eq_left hcY]
    omega
  have hclen : Lng (Y.take c) = c := by simp [Nat.min_eq_left hcY]
  rcases Nat.eq_zero_or_pos J with hJ0 | hJ1
  · subst hJ0
    exact ⟨by simp, List.length_pos_of_ne_nil (P_nonempty Y)⟩
  · -- b := take-側の J 番成分左端。左最小値なので Y の成分左端でもある
    have hJle : J ≤ (P (Y.take c)).length := hJ.le
    have hlmin := P_leftend_lmin (Y.take c) J hcT hJ
    have hblt : (IdxSum (P (Y.take c))).getD J 0 < c := by
      have h1 := hlmin.1
      rw [hclen] at h1
      omega
    have hbY : (IdxSum (P (Y.take c))).getD J 0 ≤ Lng Y - 1 := by omega
    have hlminY : ∀ j, j < (IdxSum (P (Y.take c))).getD J 0 →
        entry Y 0 ((IdxSum (P (Y.take c))).getD J 0) ≤ entry Y 0 j := by
      intro j hj
      have := hlmin.2 j hj
      rwa [entry_take Y c 0 j (by omega),
        entry_take Y c 0 _ (by omega)] at this
    obtain ⟨K', hK'L, hK'eq⟩ :=
      P_lmin_leftend Y ((IdxSum (P (Y.take c))).getD J 0) hYT hbY hlminY
    -- b > 0（J ≥ 1 で成分 0 が非空）
    have hbpos : 0 < (IdxSum (P (Y.take c))).getD J 0 := by
      have h1le : (IdxSum (P (Y.take c))).getD 1 0
          ≤ (IdxSum (P (Y.take c))).getD J 0 :=
        idxSum_mono (P (Y.take c)) 1 J hJ1 hJle
      have hc0nonempty : 0 < Lng ((P (Y.take c)).getD 0 []) :=
        P_component_nonempty (Y.take c) 0 hcT (by omega)
      have h1v : (IdxSum (P (Y.take c))).getD 1 0
          = Lng ((P (Y.take c)).getD 0 []) := by
        rw [idxSum_getD (P (Y.take c)) 1 (by omega)]
        have : (P (Y.take c)).take 1 = [(P (Y.take c)).getD 0 []] := by
          cases hP : P (Y.take c) with
          | nil => exact absurd hP (P_nonempty _)
          | cons x xs => simp
        rw [this]
        simp
      omega
    have hK'1 : 1 ≤ K' := by
      by_contra hnot
      have hK0 : K' = 0 := by omega
      rw [hK0, idxSum_getD (P Y) 0 (Nat.zero_le _)] at hK'eq
      simp only [List.take_zero, List.map_nil, List.sum_nil] at hK'eq
      omega
    -- 両側を境界で切る
    have heqA := P_take_at_boundary_sms (Y.take c) J hcT hJ1 hJle
    have heqB := P_take_at_boundary_sms Y K' hYT hK'1 hK'L.le
    have htkb : (Y.take c).take ((IdxSum (P (Y.take c))).getD J 0)
        = Y.take ((IdxSum (P (Y.take c))).getD J 0) := by
      rw [List.take_take, Nat.min_eq_left hblt.le]
    rw [htkb] at heqA
    rw [hK'eq] at heqB
    have hchain : (P (Y.take c)).take J = (P Y).take K' := by
      rw [← heqA, heqB]
    have hJK : J = K' := by
      have l1 : ((P (Y.take c)).take J).length = J := by
        rw [List.length_take]
        omega
      have l2 : ((P Y).take K').length = K' := by
        rw [List.length_take]
        omega
      rw [hchain] at l1
      omega
    subst hJK
    exact ⟨hchain, hK'L⟩

/-- 左端位置の対応: `IdxSum` の `getD` も一致する。 -/
private theorem P_take_idx_eq_sms (Y : PS) (c J : ℕ) (hYT : TPS Y)
    (hc0 : 0 < c) (hcY : c ≤ Lng Y)
    (hJ : J < (P (Y.take c)).length) :
    (IdxSum (P (Y.take c))).getD J 0 = (IdxSum (P Y)).getD J 0
      ∧ J < (P Y).length := by
  obtain ⟨htake, hlt⟩ := P_take_prefix_eq_sms Y c J hYT hc0 hcY hJ
  refine ⟨?_, hlt⟩
  rw [idxSum_getD (P (Y.take c)) J hJ.le, idxSum_getD (P Y) J hlt.le, htake]

/-! ## 成分頭の読み出し（行一般版）と幹の整列 -/

private theorem P_component_leftend_i_sms (M : PS) (J i : ℕ) (hM : TPS M)
    (hJ : J < (P M).length) :
    entry ((P M).getD J []) i 0 =
      entry M i ((IdxSum (P M)).getD J 0) := by
  have hcomp := P_IdxSum M J hM (by omega)
  have hpos := P_component_nonempty M J hM hJ
  have hsegpos : 0 < Lng (seg M ((IdxSum (P M)).getD J 0)
      ((IdxSum (P M)).getD (J + 1) 0 - 1)) := by
    rw [← hcomp]
    exact hpos
  rw [hcomp]
  have := entry_seg M ((IdxSum (P M)).getD J 0)
    ((IdxSum (P M)).getD (J + 1) 0 - 1) i 0 hsegpos
  simpa using this

/-- 幹根切片の幹の整列（Isabelle `TrMax_seg_ancestor`）:
`j₀' ≤ TrMax M < j₁' < Lng M` なら `TrMax (seg M j₀' j₁') = TrMax M - j₀'`。 -/
private theorem TrMax_seg_ancestor_sms (M : PS) (j₀' j₁' : ℕ) (hM : TPS M)
    (hj₀ : j₀' ≤ TrMax M) (hTr : TrMax M < j₁') (hj₁ : j₁' < Lng M) :
    TrMax (seg M j₀' j₁') = TrMax M - j₀' := by
  have hlt : j₀' < j₁' := by omega
  have hLS : Lng (seg M j₀' j₁') = j₁' + 1 - j₀' := by simp [seg]
  have hST : TPS (seg M j₀' j₁') := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (seg M j₀' j₁')
    omega
  -- ≥: 幹の各段は切片に移送される
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
  -- ≤: 停止段が移送されるので超えられない
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

/-! ## 主結果 -/

/-- 補題（強単項性の切片への遺伝性）: `M ∈ DT_PS` の幹根切片は `DT_PS`。 -/
theorem strongmono_slice (M : PS) (j₀' j₁' : ℕ)
    (hM : DTPS M) (hlt : j₀' < j₁') (hj₁L : j₁' ≤ Lng M - 1)
    (hj₀ : j₀' ≤ (Joints M).getD ((Br M).length - 1) 0) :
    DTPS (seg M j₀' j₁') := by
  obtain ⟨hMR, hmono, hdesc⟩ := (DTPS_iff M).mp hM
  have hMT : TPS M := RTPS_TPS M hMR
  have hLpos : 0 < Lng M := List.length_pos_of_ne_nil hMT
  have hj₁ : j₁' < Lng M := by omega
  have hLS : Lng (seg M j₀' j₁') = j₁' + 1 - j₀' := by simp [seg]
  have hST : TPS (seg M j₀' j₁') := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (seg M j₀' j₁')
    omega
  -- (a) mono
  have hmonoS : monoT (seg M j₀' j₁') = true :=
    mono_slice M j₀' j₁' hMT hmono hlt hj₁L hj₀
  -- (b) 直系先祖性 `(0,j₀') ≤ (0,j₁')`
  have hanc : leR M 0 j₀' j₁' = true := by
    by_cases hBr : Br M = []
    · have htr : TrMax M = Lng M - 1 := by
        by_contra hne
        have hP : Br M = P (seg M (TrMax M + 1) (Lng M - 1)) := by
          simp [Br, hne]
        rw [hBr] at hP
        exact P_nonempty _ hP.symm
      exact trunk_le0 M j₀' j₁' hMT hlt.le (by omega)
    · exact slice_le0_to_index M j₀' j₁' hMT hmono hBr hj₀ hlt hj₁L
  -- (c) `j₀' ≤ TrMax M`
  have hj₀Tr : j₀' ≤ TrMax M := by
    by_cases hBr : Br M = []
    · have htr : TrMax M = Lng M - 1 := by
        by_contra hne
        have hP : Br M = P (seg M (TrMax M + 1) (Lng M - 1)) := by
          simp [Br, hne]
        rw [hBr] at hP
        exact P_nonempty _ hP.symm
      omega
    · have hJ1 : (Br M).length - 1 < (Br M).length := by
        have := List.length_pos_of_ne_nil hBr
        omega
      have := (FirstNodes_TrMax_Joints M ((Br M).length - 1) hMT hmono hJ1).1
      omega
  -- (d) reduced: 簡約形の幹は対角なので `IncrFirst` 指数 0
  have hcondA : RedCondA M = true := (RTPS_condAB M hMR).1
  have hroot : entry M 0 0 = entry M 1 0 := RTPS_mono_head_eq M hMR hmono
  have hoffs := trunk_entries_offset M hMT hcondA j₀' hj₀Tr
  have hSN : seg M j₀' j₁'
      = IncrFirstN (entry M 0 j₀' - entry M 1 j₀') (Red (seg M j₀' j₁')) :=
    (ancestor_slice_Red_IncrFirst M j₀' j₁' hMR hlt hj₁L hanc).2.2
  have hk0 : entry M 0 j₀' - entry M 1 j₀' = 0 := by omega
  rw [hk0] at hSN
  have hSRed : seg M j₀' j₁' = Red (seg M j₀' j₁') := by
    simpa [IncrFirstN] using hSN
  have hSR : RTPS (seg M j₀' j₁') := by
    show reduced (seg M j₀' j₁') = true
    have hSne : seg M j₀' j₁' ≠ [] := hST
    have hne : (seg M j₀' j₁').isEmpty = false := by
      simp [hSne]
    simp [reduced, hne, ← hSRed]
  -- (e) descending (Br S): P-take 境界対応で M から輸送
  have hdescS : descendingB (Br (seg M j₀' j₁')) = true := by
    by_cases hBrS : Br (seg M j₀' j₁') = []
    · rw [hBrS]
      rfl
    · have hTrS_ne : TrMax (seg M j₀' j₁') ≠ Lng (seg M j₀' j₁') - 1 := by
        intro heq
        have : Br (seg M j₀' j₁') = [] := by simp [Br, heq]
        exact hBrS this
      -- 枝が非空 → 切片は幹を突き抜ける
      have hTrlt : TrMax M < j₁' := by
        by_contra hnot
        have hall : ∀ j, j < Lng (seg M j₀' j₁') - 1 →
            nextR (seg M j₀' j₁') 1 j (j + 1) = true := by
          intro j hj
          have ha : j < Lng (seg M j₀' j₁') := by omega
          have hb : j + 1 < Lng (seg M j₀' j₁') := by omega
          rw [nextR1_seg_adm M j₀' j₁' j (j + 1) hlt.le hj₁ ha hb]
          have hstep := TrMax_trunk_step M (j₀' + j) hMT (by omega)
          have harr : j₀' + (j + 1) = j₀' + j + 1 := by omega
          rw [harr]
          exact hstep
        have hle := le_TrMax_intro_wd (seg M j₀' j₁')
          (Lng (seg M j₀' j₁') - 1) hST hall
        have hge := TrMax_bound (seg M j₀' j₁') hST
        exact hTrS_ne (by omega)
      have hTrM_ne : TrMax M ≠ Lng M - 1 := by omega
      have hTrS : TrMax (seg M j₀' j₁') = TrMax M - j₀' :=
        TrMax_seg_ancestor_sms M j₀' j₁' hMT hj₀Tr hTrlt hj₁
      -- Br S = P (take c Y)、Br M = P Y
      have hBrS_eq : Br (seg M j₀' j₁') = P (seg M (TrMax M + 1) j₁') := by
        rw [Br_seg_reshape_68 M j₀' j₁' hlt hj₁ hTrS_ne]
        have harr : j₀' + TrMax (seg M j₀' j₁') + 1 = TrMax M + 1 := by omega
        rw [harr]
      have hBrM_eq : Br M = P (seg M (TrMax M + 1) (Lng M - 1)) := by
        simp [Br, hTrM_ne]
      have hsegTake : seg M (TrMax M + 1) j₁'
          = (seg M (TrMax M + 1) (Lng M - 1)).take (j₁' - TrMax M) := by
        have hh := seg_take_sms M (TrMax M + 1) (Lng M - 1) (j₁' - TrMax M)
          (by omega) (by omega)
        have harr : TrMax M + 1 + (j₁' - TrMax M) - 1 = j₁' := by omega
        rw [harr] at hh
        exact hh.symm
      have hYT : TPS (seg M (TrMax M + 1) (Lng M - 1)) := by
        apply List.ne_nil_of_length_pos
        change 0 < Lng (seg M (TrMax M + 1) (Lng M - 1))
        simp [seg]
        omega
      have hYlen : Lng (seg M (TrMax M + 1) (Lng M - 1)) = Lng M - 1 - TrMax M := by
        show (seg M (TrMax M + 1) (Lng M - 1)).length = Lng M - 1 - TrMax M
        unfold seg
        rw [List.length_map, List.length_range']
        omega
      have hcY : j₁' - TrMax M ≤ Lng (seg M (TrMax M + 1) (Lng M - 1)) := by
        rw [hYlen]
        omega
      have hc0 : 0 < j₁' - TrMax M := by omega
      have hcT : TPS ((seg M (TrMax M + 1) (Lng M - 1)).take (j₁' - TrMax M)) := by
        apply List.ne_nil_of_length_pos
        rw [List.length_take]
        have h2 : (seg M (TrMax M + 1) (Lng M - 1)).length
            = Lng M - 1 - TrMax M := hYlen
        rw [h2]
        omega
      -- 成分頭の一致（先頭 len(Br S) 個）
      have hheads : ∀ i J, J < (Br (seg M j₀' j₁')).length →
          entry ((Br (seg M j₀' j₁')).getD J []) i 0
            = entry ((Br M).getD J []) i 0 ∧ J < (Br M).length := by
        intro i J hJ
        have hJc : J < (P ((seg M (TrMax M + 1) (Lng M - 1)).take
            (j₁' - TrMax M))).length := by
          rw [← hsegTake, ← hBrS_eq]
          exact hJ
        obtain ⟨hidx, hJY⟩ := P_take_idx_eq_sms
          (seg M (TrMax M + 1) (Lng M - 1)) (j₁' - TrMax M) J hYT hc0 hcY hJc
        have hblt : (IdxSum (P ((seg M (TrMax M + 1) (Lng M - 1)).take
            (j₁' - TrMax M)))).getD J 0 < j₁' - TrMax M := by
          have hlm := P_leftend_lmin _ J hcT hJc
          have hclen : Lng ((seg M (TrMax M + 1) (Lng M - 1)).take
              (j₁' - TrMax M)) = j₁' - TrMax M := by
            show ((seg M (TrMax M + 1) (Lng M - 1)).take
              (j₁' - TrMax M)).length = j₁' - TrMax M
            rw [List.length_take]
            exact Nat.min_eq_left hcY
          omega
        constructor
        · rw [hBrS_eq, hsegTake, hBrM_eq,
            P_component_leftend_i_sms _ J i hcT hJc,
            P_component_leftend_i_sms _ J i hYT hJY,
            entry_take _ _ i _ hblt, hidx]
        · rw [hBrM_eq]
          exact hJY
      -- descendingB を頭の一致で輸送
      rw [descendingB_iff]
      intro J₀ J₁ h01 hJ₁len
      have hJ₀len : J₀ < (Br (seg M j₀' j₁')).length := by omega
      obtain ⟨h00, hJ₀M⟩ := hheads 0 J₀ hJ₀len
      obtain ⟨h01', hJ₁M⟩ := hheads 0 J₁ hJ₁len
      obtain ⟨h10, _⟩ := hheads 1 J₀ hJ₀len
      obtain ⟨h11, _⟩ := hheads 1 J₁ hJ₁len
      have hMside := (descendingB_iff (Br M)).mp hdesc J₀ J₁ h01 hJ₁M
      unfold cdomB
      unfold cdomB at hMside
      rw [h00, h01', h10, h11]
      exact hMside
  exact (DTPS_iff _).mpr ⟨hSR, hmonoS, hdescS⟩

/-! ## 回帰ベクトル -/

private def cexSMS : PS := [(0,0),(1,1),(2,2),(3,1),(3,1)]

#guard strongMono cexSMS
#guard decide (1 ≤ (Joints cexSMS).getD ((Br cexSMS).length - 1) 0)
-- 幹根切片 (1,3), (0,4), (1,4) はいずれも強単項
#guard strongMono (seg cexSMS 1 3)
#guard strongMono (seg cexSMS 0 4)
#guard strongMono (seg cexSMS 1 4)

#print axioms strongmono_slice

end PSS
