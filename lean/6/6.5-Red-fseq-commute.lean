import «6».«6.7-standard-reduced»

/-!
# §6.5 命題（`Red` と基本列の可換性）

- 原文: `isabelle/pss_paper.thy` の `p_6_5_Red_oper`
- 訂正: A4（`anchoredSlice` 上に制限）
- Isabelle: `m_6_5_Red_oper_final`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem oper_rebaseRow0_commute_rf (M : PS) (d n : ℕ)
    (hM : TPS M) (hmono : monoT M = true) :
    oper (rebaseRow0 (entry M 0 0) d M) n =
      rebaseRow0 (entry M 0 0) d (oper M n) := by
  let c := entry M 0 0
  let Y := rebaseRow0 c d M
  let f : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 - c + d, p.2)
  have hfloor : ∀ j < Lng M, c ≤ entry M 0 j := by
    intro j hj
    exact mono_row0_min_mr M hM hmono j hj
  have hYL : Lng Y = Lng M := by simp [Y]
  have hnext : nextR Y = nextR M := by
    simpa [Y] using nextR_rebaseRow0 c d M hfloor
  have hparents (i j : ℕ) : parents Y i j = parents M i j := by
    simp [parents, hnext, hYL]
  have hhas (i j : ℕ) : hasParent Y i j = hasParent M i j := by
    simp [hasParent, hparents]
  have hparent (i j : ℕ) : parent Y i j = parent M i j := by
    simp [parent, hparents]
  by_cases hL : Lng M = 1
  · simp [oper, hL, rebaseRow0]
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hlen : 1 < Lng M := by omega
  let j₁ := Lng M - 1
  have hj₁pos : 0 < j₁ := by simp [j₁]; omega
  have hj₁ne : j₁ ≠ 0 := by omega
  have hj₁L : j₁ < Lng M := by simp [j₁]; omega
  have hfull : leR M 0 0 j₁ = true := by
    have hh := hmono
    simp only [monoT, Bool.and_eq_true] at hh
    simpa [j₁] using hh.2
  have hlastStrict : c < entry M 0 j₁ := by
    exact ancestor_basic_1 M 0 j₁ j₁ hM hj₁pos (le_refl _) hfull
  have hlastM : entry M 0 j₁ ≠ 0 := by omega
  have hlastYpos : 0 < entry Y 0 j₁ := by
    rw [show entry Y 0 j₁ = entry M 0 j₁ - c + d by
      simpa [Y] using entry_rebaseRow0_zero c d M j₁ hj₁L]
    omega
  have hlastY : entry Y 0 j₁ ≠ 0 := by omega
  have hidx : idx1 Y j₁ = idx1 M j₁ := by
    simp [idx1, Y, entry_rebaseRow0_one]
  let i₁ := idx1 M j₁
  have hi₁ : i₁ ≤ 1 := by simpa [i₁] using idx1_le_one_rf M j₁
  by_cases hp : hasParent M i₁ j₁ = true
  · have hpY : hasParent Y (idx1 Y j₁) j₁ = true := by
      rw [hidx, hhas]
      simpa [i₁] using hp
    let j₀ := parent M i₁ j₁
    have hnextTop : nextR M i₁ j₀ j₁ = true := by
      exact hasParent_next_fseq M i₁ j₁ hp
    have hj₀lt : j₀ < j₁ :=
      (nextR_implies_row0 M i₁ j₀ j₁ hnextTop).1
    have hj₀L : j₀ < Lng M := hj₀lt.trans hj₁L
    have hrowReach : leR M 0 j₀ j₁ = true :=
      (nextR_implies_row0 M i₁ j₀ j₁ hnextTop).2
    have hrowStrict : entry M 0 j₀ < entry M 0 j₁ :=
      ancestor_basic_1 M j₀ j₁ j₁ hM hj₀lt (le_refl _) hrowReach
    have hj₀Y : parent Y (idx1 Y j₁) j₁ = j₀ := by
      simp [hidx, i₁, j₀, hparent]
    have hd₀ :
        (if 0 < idx1 Y j₁ then
          entry Y 0 j₁ - entry Y 0 (parent Y (idx1 Y j₁) j₁) else 0) =
        (if 0 < i₁ then entry M 0 j₁ - entry M 0 j₀ else 0) := by
      by_cases hi : 0 < i₁
      · rw [if_pos hi, if_pos (by simpa [hidx, i₁] using hi), hj₀Y,
          show entry Y 0 j₁ = entry M 0 j₁ - c + d by
            simpa [Y] using entry_rebaseRow0_zero c d M j₁ hj₁L,
          show entry Y 0 j₀ = entry M 0 j₀ - c + d by
            simpa [Y] using entry_rebaseRow0_zero c d M j₀ hj₀L]
        have hc₀ := hfloor j₀ hj₀L
        omega
      · rw [if_neg hi, if_neg (by simpa [hidx, i₁] using hi)]
    have hd₁ :
        (if 1 < idx1 Y j₁ then
          entry Y 1 j₁ - entry Y 1 (parent Y (idx1 Y j₁) j₁) else 0) =
        (if 1 < i₁ then entry M 1 j₁ - entry M 1 j₀ else 0) := by
      have hnot : ¬1 < i₁ := by omega
      simp [hnot, hidx, i₁]
    let d₀ := if 0 < i₁ then entry M 0 j₁ - entry M 0 j₀ else 0
    let d₁ := if 1 < i₁ then entry M 1 j₁ - entry M 1 j₀ else 0
    have hd₀' :
        (if 0 < i₁ then entry Y 0 j₁ - entry Y 0 j₀ else 0) = d₀ := by
      have hparY : parent Y (idx1 M j₁) j₁ = j₀ := by
        simpa [i₁, j₀] using hparent (idx1 M j₁) j₁
      rw [hidx, hparY] at hd₀
      simpa [i₁, d₀] using hd₀
    have hd₁' :
        (if 1 < i₁ then entry Y 1 j₁ - entry Y 1 j₀ else 0) = d₁ := by
      have hparY : parent Y (idx1 M j₁) j₁ = j₀ := by
        simpa [i₁, j₀] using hparent (idx1 M j₁) j₁
      rw [hidx, hparY] at hd₁
      simpa [i₁, d₁] using hd₁
    have hzeroM : ¬(entry M 0 (Lng M - 1) = 0 ∧
        entry M 1 (Lng M - 1) = 0) := by
      simpa [j₁] using (not_and_or.mpr (Or.inl hlastM))
    have hzeroY : ¬(entry Y 0 (Lng Y - 1) = 0 ∧
        entry Y 1 (Lng Y - 1) = 0) := by
      rw [hYL]
      simpa [j₁] using (not_and_or.mpr (Or.inl hlastY))
    have hexpM := oper_tiling_expand M n hlen hzeroM (by simpa [j₁, i₁] using hp)
    have hexpY := oper_tiling_expand Y n (by simpa [hYL] using hlen)
      hzeroY (by simpa [hYL, j₁] using hpY)
    have htake : Y.take j₀ = (M.take j₀).map f := by
      simp [Y, f, rebaseRow0]
    have hblocks (k : ℕ) :
        (List.range' j₀ (j₁ - j₀)).map (fun j =>
          (entry Y 0 j + k * d₀, entry Y 1 j + k * d₁)) =
        ((List.range' j₀ (j₁ - j₀)).map (fun j =>
          (entry M 0 j + k * d₀, entry M 1 j + k * d₁))).map f := by
      apply List.ext_getElem
      · simp
      · intro q hqL hqR
        have hq : q < j₁ - j₀ := by simpa using hqL
        have hj : j₀ + q < Lng M := by omega
        simp only [List.getElem_map, List.getElem_range']
        simp only [one_mul]
        rw [show entry Y 0 (j₀ + q) = entry M 0 (j₀ + q) - c + d by
          simpa [Y] using entry_rebaseRow0_zero c d M (j₀ + q) hj,
          show entry Y 1 (j₀ + q) = entry M 1 (j₀ + q) by
            simpa [Y] using entry_rebaseRow0_one c d M (j₀ + q)]
        apply Prod.ext
        · simp [f]
          have hcf := hfloor (j₀ + q) hj
          omega
        · simp [f]
    rw [hexpY, hexpM]
    dsimp only
    rw [show Lng Y - 1 = j₁ by rw [hYL], hidx,
      show parent Y (idx1 M j₁) j₁ = j₀ by
        simp [i₁, j₀, hparent], hd₀', hd₁']
    change Y.take j₀ ++ (List.range n).flatMap (fun k =>
        (List.range' j₀ (j₁ - j₀)).map (fun j =>
          (entry Y 0 j + k * d₀, entry Y 1 j + k * d₁))) =
      rebaseRow0 c d (M.take j₀ ++ (List.range n).flatMap (fun k =>
        (List.range' j₀ (j₁ - j₀)).map (fun j =>
          (entry M 0 j + k * d₀, entry M 1 j + k * d₁))))
    rw [htake]
    simp only [rebaseRow0, List.map_append, List.map_flatMap]
    congr 1
    apply List.flatMap_congr
    intro k hk
    exact hblocks k
  · have hpfalse : hasParent M i₁ j₁ = false :=
      Bool.eq_false_of_not_eq_true hp
    have hpYfalse : hasParent Y (idx1 Y j₁) j₁ = false := by
      rw [hidx, hhas]
      simpa [i₁] using hpfalse
    have hpred : Pred Y = rebaseRow0 c d (Pred M) := by
      have hnotleM : ¬Lng M ≤ 1 := by omega
      have hnotleY : ¬Lng Y ≤ 1 := by omega
      simp only [Pred, if_neg hnotleM, if_neg hnotleY]
      simp [Y, rebaseRow0, List.map_dropLast]
    have hopM : oper M n = Pred M := by
      simp [oper, j₁, hj₁ne, hlastM, i₁, hpfalse]
    have hopY : oper Y n = Pred Y := by
      have hjYne : Lng Y - 1 ≠ 0 := by rw [hYL]; exact hj₁ne
      have hzY : (decide (entry Y 0 (Lng Y - 1) = 0) &&
          decide (entry Y 1 (Lng Y - 1) = 0)) = false := by
        simp [hYL, j₁, hlastY]
      have hpYfalse' :
          hasParent Y (idx1 Y (Lng Y - 1)) (Lng Y - 1) = false := by
        simpa [hYL, j₁] using hpYfalse
      simp [oper, hjYne, hzY, hpYfalse']
    change oper Y n = rebaseRow0 c d (oper M n)
    rw [hopY, hopM, hpred]

private theorem anchoredSlice_RedCondA_rf (M : PS)
    (hM : anchoredSlice M) : RedCondA M = true := by
  rcases hM with ⟨S, a, b, hsource, hab, hbL, hanc, rfl⟩
  have hR : RTPS S := by
    rcases hsource with hST | hRT
    · exact STPS_RTPS S hST
    · exact hRT.1
  exact RedCondA_seg S a b hab hbL (RTPS_condAB S hR).1

private theorem RedCondA_oper_rf (M : PS) (n : ℕ) (hM : TPS M)
    (hA : RedCondA M = true) (hn : 1 ≤ n) :
    RedCondA (oper M n) = true := by
  by_cases hnontile :
      Lng M - 1 = 0 ∨
      (entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) ∨
      hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = false
  · exact RedCondA_oper_nontiling M n hM hA hnontile
  · have hlast : 1 < Lng M := by
      have : Lng M - 1 ≠ 0 := by
        intro h
        exact hnontile (Or.inl h)
      omega
    have hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
        entry M 1 (Lng M - 1) = 0) := by
      intro h
      exact hnontile (Or.inr (Or.inl h))
    have hp : hasParent M (idx1 M (Lng M - 1))
        (Lng M - 1) = true := by
      by_contra h
      exact hnontile (Or.inr (Or.inr (Bool.eq_false_of_not_eq_true h)))
    exact RedCondA_oper_tiling M n hM hA hn hlast hzero hp

/-- On the corrected A4 domain, reduction commutes with every positive
fundamental-sequence step. -/
theorem Red_oper (M : PS) (n : ℕ) (hM : anchoredSlice M) (hn : 1 ≤ n) :
    oper (Red M) n = Red (oper M n) := by
  have hMT : TPS M := anchoredSlice_TPS M hM
  have hnm : multiT M = false := anchoredSlice_nonmulti M hM
  have hA : RedCondA M = true := anchoredSlice_RedCondA_rf M hM
  by_cases hz : zeroT M = true
  · have hL : Lng M = 1 := by
      have hh := hz
      simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
      exact hh.1
    have hred : Red M = [(0, 0)] := Red_zero_mr M hz
    simp [oper, hL, hred]
  · have hz' : zeroT M = false := Bool.eq_false_of_not_eq_true hz
    have hmono : monoT M = true := by
      have hh := hnm
      simp [multiT, hz'] at hh
      exact hh
    by_cases hL : Lng M = 1
    · have hRL : Lng (Red M) = 1 := by
        rw [Lng_Red_invariance M hMT, hL]
      simp [oper, hL, hRL]
    have hlen : 1 < Lng M := by
      have hMne : M ≠ [] := by simpa [TPS] using hMT
      have hpos : 0 < Lng M := List.length_pos_of_ne_nil hMne
      by_contra h
      have hle : Lng M ≤ 1 := Nat.le_of_not_gt h
      have heq : Lng M = 1 := by omega
      exact hL heq
    let c := entry M 0 0
    let d := entry M 1 0
    let R := Red M
    let N := oper M n
    let RN := oper R n
    change RN = Red N
    have hred : R = rebaseRow0 c d M := by
      simpa [R, c, d] using Red_rebase_nonmulti M hMT hA hnm
    have hcomm : RN = rebaseRow0 c d N := by
      calc
        RN = oper (rebaseRow0 c d M) n :=
          congrArg (fun X => oper X n) hred
        _ = rebaseRow0 c d (oper M n) := by
          simpa [c] using oper_rebaseRow0_commute_rf M d n hMT hmono
        _ = rebaseRow0 c d N := by rfl
    have hRT : RTPS R := by
      simpa [R] using Red_nonmulti_RTPS M hMT hnm
    have hRTT : TPS R := RTPS_TPS R hRT
    have hRnm : multiT R = false := by
      simpa [R] using Red_preserves_nonmulti M hMT hnm
    have hRNRT : RTPS RN := by
      simpa [RN] using RTPS_oper R n hRT hn
    have hRNL : Lng R = Lng M := by
      simpa [R] using Lng_Red_invariance M hMT
    have hfloor : ∀ j < Lng M, c ≤ entry M 0 j := by
      intro j hj
      exact mono_row0_min_mr M hMT hmono j hj
    have hnextR : nextR R = nextR M := by
      rw [hred]
      exact nextR_rebaseRow0 c d M hfloor
    have hrow1R (j : ℕ) : entry R 1 j = entry M 1 j := by
      rw [hred]
      exact entry_rebaseRow0_one c d M j
    have hNT : TPS N := by simpa [N] using oper_TPS M n hMT hn
    have hNA : RedCondA N = true := by
      simpa [N] using RedCondA_oper_rf M n hMT hA hn
    by_cases hs : nextR M 0 0 (Lng M - 1) = true ∧
        entry M 1 (Lng M - 1) = 0
    · have hPN : P N = List.replicate n (Pred M) := by
        simpa [N] using nonmulti_fseq_1 M n hMT hn hnm hs.1 hs.2
      have hsRnext : nextR R 0 0 (Lng R - 1) = true := by
        rw [hRNL, hnextR]
        exact hs.1
      have hsRentry : entry R 1 (Lng R - 1) = 0 := by
        rw [hRNL, hrow1R]
        exact hs.2
      have hPRN : P RN = List.replicate n (Pred R) := by
        simpa [RN] using
          nonmulti_fseq_1 R n hRTT hn hRnm hsRnext hsRentry
      have hfixRN : Red RN = RN := RTPS_Red_eq RN hRNRT
      have hfixPredR : Red (Pred R) = Pred R :=
        RTPS_Red_eq (Pred R) (RTPS_Pred R hRT)
      have hpredComm : Red (Pred M) = Pred R := by
        simpa [R] using Red_Pred M hMT
      have hrep : ∀ k,
          (List.replicate k (Pred R)).flatMap Red =
            (List.replicate k (Pred M)).flatMap Red := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
            simp only [List.replicate_succ, List.flatMap_cons]
            rw [hfixPredR, hpredComm, ih]
      rw [← hfixRN, Red_eq_flatMap_P RN (RTPS_TPS RN hRNRT),
        Red_eq_flatMap_P N hNT, hPRN, hPN]
      exact hrep n
    · have hcond : nextR M 0 0 (Lng M - 1) = false ∨
          0 < entry M 1 (Lng M - 1) := by
        by_cases hnext : nextR M 0 0 (Lng M - 1) = true
        · right
          by_contra he
          have heq : entry M 1 (Lng M - 1) = 0 := by omega
          exact hs ⟨hnext, heq⟩
        · exact Or.inl (Bool.eq_false_of_not_eq_true hnext)
      have hPN : P N = [N] := by
        simpa [N] using nonmulti_fseq_2 M n hMT hn hnm hcond
      have hNnm : multiT N = false := by
        by_contra hne
        have hmu : multiT N = true := Bool.eq_true_of_not_eq_false hne
        have hlong := (P_components_multi_iff N hNT).mp hmu
        rw [hPN] at hlong
        simp at hlong
      have hhead := oper_head_fseq M n hMT hlen hn
      have hN0 : entry N 0 0 = c := by
        simp only [N, c, entry]
        rw [hhead]
      have hN1 : entry N 1 0 = d := by
        simp only [N, d, entry]
        rw [hhead]
      have hRedN := Red_rebase_nonmulti N hNT hNA hNnm
      rw [hN0, hN1] at hRedN
      exact hcomm.trans hRedN.symm

#print axioms Red_oper

end PSS
