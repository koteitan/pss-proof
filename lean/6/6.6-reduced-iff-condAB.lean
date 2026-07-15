import «6».«6.6-P-condAB»

/-!
# §6.6 命題（簡約性と係数の関係）

- 原文: `tmp/content.md` の「命題（簡約性と係数の関係）」
- 訂正: なし
- Isabelle: `p_6_6_reduced_iff_cond`, `kst_reduced_imp_condAB_uncond`
- 依存: §6.5 `Red_rebase_nonmulti`, §6.2
- 状態: 🚨 証明作業中
-/

namespace PSS

theorem RTPS_TPS (M : PS) (hM : RTPS M) : TPS M := by
  have hh := hM
  simp only [RTPS, reduced, Bool.and_eq_true, beq_iff_eq] at hh
  simpa [TPS] using hh.1

theorem RTPS_Red_eq (M : PS) (hM : RTPS M) : Red M = M := by
  have hh := hM
  simp only [RTPS, reduced, Bool.and_eq_true, beq_iff_eq] at hh
  exact hh.2

theorem no_parent_zero (M : PS) (i : ℕ) : hasParent M i 0 = false := by
  apply Bool.eq_false_iff.mpr
  intro hp
  have hn := hasParent_next_fseq M i 0 hp
  by_cases hi : i = 0
  · simp [nextR, hi, nextrel0] at hn
  · simp [nextR, hi, nextrel1] at hn

theorem RedCondB_apply (M : PS) (hM : TPS M)
    (hB : RedCondB M = true) (j : ℕ) (hj : j < Lng M)
    (hnp : hasParent M 0 j = false) :
    entry M 0 j = entry M 1 j := by
  have hh := hB
  simp only [RedCondB, List.all_eq_true, List.mem_range] at hh
  have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hj' : j < Lng M - 1 + 1 := by omega
  have hjB := hh j hj'
  simpa [hnp] using hjB

theorem RedCondB_head_eq (M : PS) (hM : TPS M)
    (hB : RedCondB M = true) :
    entry M 0 0 = entry M 1 0 := by
  exact RedCondB_apply M hM hB 0 (List.length_pos_of_ne_nil hM)
    (no_parent_zero M 0)

theorem rebaseRow0_self_of_head_eq_nonmulti (M : PS) (hM : TPS M)
    (hnm : multiT M = false)
    (hhead : entry M 0 0 = entry M 1 0) :
    rebaseRow0 (entry M 0 0) (entry M 1 0) M = M := by
  have hfloor : ∀ j < Lng M, entry M 0 0 ≤ entry M 0 j := by
    by_cases hz : zeroT M = true
    · have hL : Lng M = 1 := by
        have hh := hz
        simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
        exact hh.1
      intro j hj
      have : j = 0 := by omega
      subst j
      exact le_rfl
    · have hz' : zeroT M = false := Bool.eq_false_of_not_eq_true hz
      have hmono : monoT M = true := by
        have hh := hnm
        simp [multiT, hz'] at hh
        exact hh
      intro j hj
      exact mono_row0_min_mr M hM hmono j hj
  apply List.ext_getElem
  · simp [rebaseRow0]
  · intro j hjR hjM
    have hj : j < Lng M := by simpa using hjM
    have hMj : M[j] = (entry M 0 j, entry M 1 j) := by
      apply Prod.ext
      · exact (entry0_eq_fst_getElem_mr M j hj).symm
      · simpa [entry, List.getElem?_eq_getElem hj]
    simp only [rebaseRow0, List.getElem_map]
    rw [hMj, hhead]
    apply Prod.ext
    · simp only [Prod.fst]
      exact Nat.sub_add_cancel (by rw [← hhead]; exact hfloor j hj)
    · simp

/-- The non-multi half of the backward implication in
`reduced ↔ RedCondA ∧ RedCondB`. -/
theorem RTPS_of_condAB_nonmulti (M : PS) (hM : TPS M)
    (hA : RedCondA M = true) (hB : RedCondB M = true)
    (hnm : multiT M = false) : RTPS M := by
  have hred := Red_rebase_nonmulti M hM hA hnm
  have hhead := RedCondB_head_eq M hM hB
  have hid := rebaseRow0_self_of_head_eq_nonmulti M hM hnm hhead
  have hfix : Red M = M := hred.trans hid
  have hne : M ≠ [] := hM
  simp [RTPS, reduced, hne, hfix]

private theorem redPositiveOut_head_diag (M N : PS)
    (hmj : entry M 1 0 ≤ Lng N - 1)
    (hmono : monoT (seg N (entry M 1 0) (Lng N - 1)) = true) :
    entry (redPositiveOut_ri M N) 0 0 =
      entry (redPositiveOut_ri M N) 1 0 := by
  let m := entry M 1 0
  let jN := Lng N - 1
  unfold redPositiveOut_ri
  dsimp only
  rw [if_pos (by simp [hmj, hmono])]
  have hlen : 0 < jN + 1 - m := by
    dsimp [m, jN]
    omega
  let R := (List.range' m (jN + 1 - m)).map (fun j =>
    (entry N 0 j - entry N 0 m + entry N 1 m, entry N 1 j))
  change entry R 0 0 = entry R 1 0
  have hRpos : 0 < Lng R := by simp [R, hlen]
  have hget : R[0] = (entry N 1 m, entry N 1 m) := by
    simp [R, List.getElem_map, List.getElem_range']
  simp [entry, List.getElem?_eq_getElem hRpos, hget]

/-- The first column of every reduced mono sequence is diagonal. -/
theorem RTPS_mono_head_eq (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) :
    entry M 0 0 = entry M 1 0 := by
  have hM := RTPS_TPS M hR
  have hfix := RTPS_Red_eq M hR
  have hnm : multiT M = false := by simp [multiT, hmono]
  by_cases hm : entry M 1 0 = 0
  · by_cases hc0 : entry M 0 0 = 0
    · omega
    · let C := coreReduce M
      have hnoncore : ¬(entry M 0 0 = 0 ∧ entry M 1 0 = 0) := by
        simp [hc0]
      have hred : Red M = Red C := by
        simpa [C, hm] using Red_noncore_ri M hM hmono hnoncore
      have hCT : TPS C := by simpa [C] using coreReduce_TPS M hM
      have hCcore : entry C 0 0 = 0 ∧ entry C 1 0 = 0 := by
        simpa [C] using coreReduce_core M hM
      have hCnm : multiT C = false := by
        simpa [C] using coreReduce_multi_false M hM hmono
      have hRedC0 : entry (Red C) 0 0 = 0 := by
        by_cases hzC : zeroT C = true
        · rw [Red_zero_mr C hzC]
          simp [entry]
        · have hzC' : zeroT C = false := Bool.eq_false_of_not_eq_true hzC
          have hmonoC : monoT C = true := by
            have hh := hCnm
            simp [multiT, hzC'] at hh
            exact hh
          exact Red_core_prefix_diag C hmonoC hCcore 0 0 (Nat.zero_le _)
      have hc0z : entry M 0 0 = 0 := by
        calc
          entry M 0 0 = entry (Red M) 0 0 := by rw [hfix]
          _ = entry (Red C) 0 0 := by rw [hred]
          _ = 0 := hRedC0
      exact False.elim (hc0 hc0z)
  · have hpos : 0 < entry M 1 0 := by omega
    have hnoncore : ¬(entry M 0 0 = 0 ∧ entry M 1 0 = 0) := by
      intro h
      exact hm h.2
    let C := coreReduce M
    let N := Red C
    let m := entry M 1 0
    have hCT : TPS C := by simpa [C] using coreReduce_TPS M hM
    have hCL : Lng C = m + Lng M := by
      simp [C, m, coreReduce, hm, diagSeq, IncrFirstN_eq_map]
      omega
    have hNL : Lng N = m + Lng M := by
      calc
        Lng N = Lng C := Lng_Red_invariance C hCT
        _ = m + Lng M := hCL
    have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
    have hmj : m ≤ Lng N - 1 := by rw [hNL]; omega
    have hmonoS : monoT (seg N m (Lng N - 1)) = true := by
      simpa [N, C, m] using (monoT_Red_m10pos M hM hmono hpos).2
    have hdiag : entry (redPositiveOut_ri M N) 0 0 =
        entry (redPositiveOut_ri M N) 1 0 := by
      apply redPositiveOut_head_diag M N
      · simpa [m] using hmj
      · simpa [m] using hmonoS
    have hred : Red M = redPositiveOut_ri M N := by
      simpa [N, C, hm] using Red_noncore_ri M hM hmono hnoncore
    calc
      entry M 0 0 = entry (Red M) 0 0 := by rw [hfix]
      _ = entry (redPositiveOut_ri M N) 0 0 := by rw [hred]
      _ = entry (redPositiveOut_ri M N) 1 0 := hdiag
      _ = entry (Red M) 1 0 := by rw [hred]
      _ = entry M 1 0 := by rw [hfix]

theorem mono_hasParent_row0 (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (j : ℕ)
    (hjpos : 0 < j) (hjL : j < Lng M) :
    hasParent M 0 j = true := by
  have hfull : leR M 0 0 (Lng M - 1) = true := by
    have hh := hmono
    simp only [monoT, Bool.and_eq_true] at hh
    exact hh.2
  have hjlast : j ≤ Lng M - 1 := by omega
  have hanc := ancestor_tree_1 M 0 j (Lng M - 1) hM hfull
    (Nat.zero_le _) hjlast
  have hstrict := ancestor_basic_1 M 0 j j hM hjpos (le_refl _) hanc
  rcases parent_exists_1 M 0 j hM hjpos hjL hstrict with
    ⟨p, hp0, hpj, hp⟩
  exact (hasParent_iff_unique_fseq M 0 j).mpr
    ⟨p, hp, fun q hq => row0_parent_unique M q p j hq hp⟩

theorem RTPS_mono_RedCondB (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) : RedCondB M = true := by
  have hM := RTPS_TPS M hR
  have hhead := RTPS_mono_head_eq M hR hmono
  simp only [RedCondB, List.all_eq_true, List.mem_range]
  intro j hj
  by_cases hp : hasParent M 0 j = true
  · simp [hp]
  · have hp' : hasParent M 0 j = false := Bool.eq_false_of_not_eq_true hp
    have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
    have hjL : j < Lng M := by omega
    have hj0 : j = 0 := by
      by_contra hjne
      have hjpos : 0 < j := Nat.pos_of_ne_zero hjne
      exact hp (mono_hasParent_row0 M hM hmono j hjpos hjL)
    subst j
    simp [hp', hhead]

theorem RTPS_iff_condAB_zeroT (M : PS) (hM : TPS M)
    (hz : zeroT M = true) :
    RTPS M ↔ RedCondA M = true ∧ RedCondB M = true := by
  constructor
  · intro hR
    have hfix := RTPS_Red_eq M hR
    have hred := Red_zero_mr M hz
    have hMeq : M = [(0, 0)] := by rw [← hfix, hred]
    subst M
    decide
  · rintro ⟨hA, hB⟩
    have hnm : multiT M = false := by simp [multiT, hz]
    exact RTPS_of_condAB_nonmulti M hM hA hB hnm

/-- The `multiT` branch of the keystone equivalence.  Once the equivalence is
known recursively on every `P` component, reducedness and conditions (A), (B)
are transferred blockwise in both directions. -/
theorem RTPS_iff_condAB_multi (M : PS) (hM : TPS M)
    (_hmulti : multiT M = true)
    (IH : ∀ J, J < (P M).length →
      (RTPS ((P M).getD J []) ↔
        RedCondA ((P M).getD J []) = true ∧
          RedCondB ((P M).getD J []) = true)) :
    RTPS M ↔ RedCondA M = true ∧ RedCondB M = true := by
  constructor
  · intro hR
    have hblocksR := (RTPS_iff_P_components M hM).mp hR
    apply RedCondAB_of_P_components M hM
    intro J hJ
    exact (IH J hJ).mp (hblocksR J hJ)
  · rintro ⟨hA, hB⟩
    apply (RTPS_iff_P_components M hM).mpr
    intro J hJ
    apply (IH J hJ).mpr
    exact RedCondAB_P_component M J hM hA hB hJ

#print axioms RTPS_of_condAB_nonmulti
#print axioms RTPS_mono_head_eq
#print axioms RTPS_mono_RedCondB
#print axioms RTPS_iff_condAB_zeroT
#print axioms RTPS_iff_condAB_multi

end PSS
