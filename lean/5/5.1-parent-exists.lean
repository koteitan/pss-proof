import PSS.Defs

/-!
# §5.1 命題（親の存在の判定条件）

- 原文: `isabelle/pss_paper.thy` の `p_5_1_parent_exists_1`–`_4`
- 訂正: なし
- Isabelle: `m_5_1_parent_exists_1`–`_4`
- 依存: `PSS.Defs`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem le0Aux_index_mono {M : PS} {fuel a b : ℕ}
    (h : le0Aux M fuel a b = true) : a ≤ b := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le0Aux] using h
      subst b
      exact le_refl _
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨j, hjb, _, haj⟩
      · omega
      · exact (ih haj).trans (Nat.le_of_lt hjb)

private theorem le1Aux_index_mono {M : PS} {fuel a b : ℕ}
    (h : le1Aux M fuel a b = true) : a ≤ b := by
  induction fuel generalizing b with
  | zero =>
      simp [le1Aux] at h
      omega
  | succ fuel ih =>
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨j, hjb, _, haj⟩
      · omega
      · exact (ih haj).trans (Nat.le_of_lt hjb)

private theorem le0_index_mono {M : PS} {a b : ℕ}
    (h : le0 M a b = true) : a ≤ b := by
  simp only [le0, Bool.and_eq_true] at h
  exact le0Aux_index_mono h.2

private theorem le1_index_mono {M : PS} {a b : ℕ}
    (h : le1 M a b = true) : a ≤ b := by
  simp only [le1, Bool.and_eq_true] at h
  exact le1Aux_index_mono h.2

private theorem le0Aux_refl (M : PS) (fuel a : ℕ) :
    le0Aux M fuel a a = true := by
  cases fuel <;> simp [le0Aux]

private theorem le0Aux_entry_le {M : PS} {fuel a b : ℕ}
    (h : le0Aux M fuel a b = true) : entry M 0 a ≤ entry M 0 b := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le0Aux] using h
      subst b
      exact le_refl _
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨j, _, hjnext, haj⟩
      · subst b
        exact le_refl _
      · have hle := ih haj
        have hlt : entry M 0 j < entry M 0 b := by
          have hn := hjnext
          simp [nextrel0] at hn
          omega
        omega

private theorem le0Aux_entry_growth {M : PS} {fuel a b c : ℕ}
    (h : le0Aux M fuel a b = true) (hac : a < c) (hcb : c ≤ b) :
    entry M 0 a < entry M 0 c := by
  induction fuel generalizing b with
  | zero =>
      simp [le0Aux] at h
      omega
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨j, hjb, hjnext, haj⟩
      · subst b
        omega
      · by_cases hcj : c ≤ j
        · exact ih haj hcj
        · have hjc : j < c := Nat.lt_of_not_ge hcj
          have hale : entry M 0 a ≤ entry M 0 j := le0Aux_entry_le haj
          have hjlt : entry M 0 j < entry M 0 b := by
            have hn := hjnext
            simp [nextrel0] at hn
            omega
          by_cases hcb' : c = b
          · subst c
            omega
          · have hclt : c < b := lt_of_le_of_ne hcb hcb'
            have hn := hjnext
            simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
              List.all_eq_true] at hn
            have hble : entry M 0 b ≤ entry M 0 c := by
              have hcMem : c ∈ List.range b := List.mem_range.mpr hclt
              have hc := hn.2 c hcMem
              simpa [hjc] using hc
            omega

theorem parent_exists_1
    (M : PS) (j₀ j₁ : ℕ)
    (hM : TPS M) (hlt : j₀ < j₁) (hbound : j₁ < Lng M)
    (hentry : entry M 0 j₀ < entry M 0 j₁) :
    ∃ j, j₀ ≤ j ∧ j < j₁ ∧ nextR M 0 j j₁ = true := by
  let S : Finset ℕ := (Finset.range j₁).filter fun j =>
    entry M 0 j < entry M 0 j₁
  have hj₀S : j₀ ∈ S := by simp [S, hlt, hentry]
  have hSne : S.Nonempty := ⟨j₀, hj₀S⟩
  let j := S.max' hSne
  have hjS : j ∈ S := Finset.max'_mem S hSne
  have hj₀le : j₀ ≤ j := Finset.le_max' S j₀ hj₀S
  have hjlt : j < j₁ := (Finset.mem_filter.mp hjS).1 |> Finset.mem_range.mp
  have hjentry : entry M 0 j < entry M 0 j₁ := (Finset.mem_filter.mp hjS).2
  have hjbound : j < Lng M := hjlt.trans hbound
  have hall : (List.range j₁).all (fun k =>
      !(decide (j < k)) || decide (entry M 0 j₁ ≤ entry M 0 k)) = true := by
    apply List.all_eq_true.mpr
    intro k hk
    have hklt : k < j₁ := List.mem_range.mp hk
    by_cases hjk : j < k
    · have hnot : ¬ entry M 0 k < entry M 0 j₁ := by
        intro hkentry
        have hkS : k ∈ S := by simp [S, hklt, hkentry]
        have hkle := Finset.le_max' S k hkS
        omega
      have hle : entry M 0 j₁ ≤ entry M 0 k := Nat.le_of_not_gt hnot
      simp [hjk, hle]
    · simp [hjk]
  refine ⟨j, hj₀le, hjlt, ?_⟩
  simp [nextR, nextrel0, hjbound, hbound, hjlt, hjentry, hall]

theorem parent_exists_2
    (M : PS) (j₀ j₁ : ℕ)
    (hM : TPS M) (hlt : j₀ < j₁) (hbound : j₁ < Lng M)
    (hentry : entry M 1 j₀ < entry M 1 j₁)
    (hanc : leR M 0 j₀ j₁ = true) :
    ∃ j, j₀ ≤ j ∧ j < j₁ ∧ nextR M 1 j j₁ = true := by
  have hj₀anc : le0 M j₀ j₁ = true := by simpa [leR] using hanc
  let S : Finset ℕ := (Finset.range j₁).filter fun j =>
    entry M 1 j < entry M 1 j₁ ∧ le0 M j j₁
  have hj₀S : j₀ ∈ S := by simp [S, hlt, hentry, hj₀anc]
  have hSne : S.Nonempty := ⟨j₀, hj₀S⟩
  let j := S.max' hSne
  have hjS : j ∈ S := Finset.max'_mem S hSne
  have hj₀le : j₀ ≤ j := Finset.le_max' S j₀ hj₀S
  have hjlt : j < j₁ := (Finset.mem_filter.mp hjS).1 |> Finset.mem_range.mp
  have hjentry : entry M 1 j < entry M 1 j₁ := (Finset.mem_filter.mp hjS).2.1
  have hjanc : le0 M j j₁ = true := (Finset.mem_filter.mp hjS).2.2
  have hjbound : j < Lng M := hjlt.trans hbound
  have hall : (List.range (Lng M)).all (fun k =>
      !(decide (j < k) && le0 M k j₁) ||
        decide (entry M 1 j₁ ≤ entry M 1 k)) = true := by
    apply List.all_eq_true.mpr
    intro k hk
    by_cases hjk : j < k
    · by_cases hkanc : le0 M k j₁ = true
      · have hkle : k ≤ j₁ := le0_index_mono hkanc
        have hnot : ¬ entry M 1 k < entry M 1 j₁ := by
          intro hkentry
          have hklt : k < j₁ := by
            have hkne : k ≠ j₁ := by
              intro hEq
              subst k
              omega
            omega
          have hkS : k ∈ S := by simp [S, hklt, hkentry, hkanc]
          have hklej := Finset.le_max' S k hkS
          omega
        have hle : entry M 1 j₁ ≤ entry M 1 k := Nat.le_of_not_gt hnot
        simp [hjk, hkanc, hle]
      · simp [hjk, hkanc]
    · simp [hjk]
  refine ⟨j, hj₀le, hjlt, ?_⟩
  simp only [nextR, nextrel1]
  rw [hall]
  simp [hjbound, hbound, hjlt, hjentry, hjanc]

private theorem le0Aux_build
    (M : PS) (fuel j₀ j₁ : ℕ)
    (hM : TPS M) (hlt : j₀ < j₁) (hbound : j₁ < Lng M)
    (hfuel : j₁ < fuel)
    (hentry : ∀ j, j₀ < j → j ≤ j₁ → entry M 0 j₀ < entry M 0 j) :
    le0Aux M fuel j₀ j₁ = true := by
  induction fuel generalizing j₁ with
  | zero => omega
  | succ fuel ih =>
      obtain ⟨j, hj₀le, hjlt, hjnext⟩ :=
        parent_exists_1 M j₀ j₁ hM hlt hbound (hentry j₁ hlt (le_refl _))
      have hjnext' : nextrel0 M j j₁ = true := by
        simpa [nextR] using hjnext
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range]
      right
      refine ⟨j, hjlt, hjnext', ?_⟩
      by_cases heq : j = j₀
      · subst j
        exact le0Aux_refl M fuel j₀
      · apply ih (j₁ := j)
        · omega
        · omega
        · omega
        · intro k hk₀ hkj
          exact hentry k hk₀ (hkj.trans (Nat.le_of_lt hjlt))

theorem parent_exists_3
    (M : PS) (j₀ j₁ : ℕ)
    (hM : TPS M) (hlt : j₀ < j₁) (hbound : j₁ < Lng M)
    (hentry : ∀ j, j₀ < j → j ≤ j₁ → entry M 0 j₀ < entry M 0 j) :
    leR M 0 j₀ j₁ = true := by
  have hj₀bound : j₀ < Lng M := hlt.trans hbound
  have haux := le0Aux_build M (Lng M) j₀ j₁ hM hlt hbound hbound hentry
  simp [leR, le0, hj₀bound, hbound, haux]

private theorem le0_prefix
    (M : PS) (a b c : ℕ) (hM : TPS M)
    (hab : le0 M a b = true) (hac : a ≤ c) (hcb : c ≤ b) :
    le0 M a c = true := by
  have hh := hab
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
  have haBound : a < Lng M := hh.1.1
  have hbBound : b < Lng M := hh.1.2
  have haux : le0Aux M (Lng M) a b = true := hh.2
  by_cases heq : a = c
  · subst c
    simp [le0, haBound, le0Aux_refl]
  · have halt : a < c := lt_of_le_of_ne hac heq
    have hcBound : c < Lng M := lt_of_le_of_lt hcb hbBound
    apply parent_exists_3 M a c hM halt hcBound
    intro k hak hkc
    exact le0Aux_entry_growth haux hak (hkc.trans hcb)

private theorem le0_transitive
    (M : PS) (a b c : ℕ) (hM : TPS M)
    (hab : le0 M a b = true) (hbc : le0 M b c = true) :
    le0 M a c = true := by
  have habIdx : a ≤ b := le0_index_mono hab
  have hbcIdx : b ≤ c := le0_index_mono hbc
  by_cases habEq : a = b
  · simpa [habEq] using hbc
  by_cases hbcEq : b = c
  · simpa [hbcEq] using hab
  have hac : a < c := lt_of_lt_of_le (lt_of_le_of_ne habIdx habEq) hbcIdx
  have hcBound : c < Lng M := by
    have hh := hbc
    simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.2
  apply parent_exists_3 M a c hM hac hcBound
  intro k hak hkc
  by_cases hkb : k ≤ b
  · have hh := hab
    simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact le0Aux_entry_growth hh.2 hak hkb
  · have hbk : b < k := Nat.lt_of_not_ge hkb
    have habEntry : entry M 0 a ≤ entry M 0 b := by
      have hh := hab
      simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
      exact le0Aux_entry_le hh.2
    have hbcEntry : entry M 0 b < entry M 0 k := by
      have hh := hbc
      simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
      exact le0Aux_entry_growth hh.2 hbk hkc
    omega

private theorem le1Aux_refl (M : PS) (fuel a : ℕ) :
    le1Aux M fuel a a = true := by
  cases fuel <;> simp [le1Aux]

private theorem le1Aux_build
    (M : PS) (fuel j₀ j₁ : ℕ)
    (hM : TPS M) (hlt : j₀ < j₁) (hbound : j₁ < Lng M)
    (hfuel : j₁ < fuel) (hrow0 : le0 M j₀ j₁ = true)
    (hentry : ∀ j, j₀ < j → le0 M j j₁ = true →
      entry M 1 j₀ < entry M 1 j) :
    le1Aux M fuel j₀ j₁ = true := by
  induction fuel generalizing j₁ with
  | zero => omega
  | succ fuel ih =>
      have hj₁refl : le0 M j₁ j₁ = true := by
        simp [le0, hbound, le0Aux_refl]
      have hlastEntry : entry M 1 j₀ < entry M 1 j₁ :=
        hentry j₁ hlt hj₁refl
      have hrow0R : leR M 0 j₀ j₁ = true := by simpa [leR] using hrow0
      obtain ⟨j, hj₀le, hjlt, hjnext⟩ :=
        parent_exists_2 M j₀ j₁ hM hlt hbound hlastEntry hrow0R
      have hjnext' : nextrel1 M j j₁ = true := by
        simpa [nextR] using hjnext
      have hjrow0 : le0 M j j₁ = true := by
        have hn := hjnext'
        simp [nextrel1] at hn
        exact hn.1.2
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range]
      right
      refine ⟨j, hjlt, hjnext', ?_⟩
      by_cases heq : j = j₀
      · subst j
        exact le1Aux_refl M fuel j₀
      · have hj₀lt : j₀ < j := lt_of_le_of_ne hj₀le (Ne.symm heq)
        have hjbound : j < Lng M := hjlt.trans hbound
        have hjfuel : j < fuel := by omega
        have hprefix : le0 M j₀ j = true :=
          le0_prefix M j₀ j₁ j hM hrow0 hj₀le (Nat.le_of_lt hjlt)
        apply ih (j₁ := j) hj₀lt hjbound hjfuel hprefix
        intro k hk₀ hkj
        exact hentry k hk₀ (le0_transitive M k j j₁ hM hkj hjrow0)

theorem parent_exists_4
    (M : PS) (j₀ j₁ : ℕ)
    (hM : TPS M) (hlt : j₀ < j₁) (hbound : j₁ < Lng M)
    (hentry : ∀ j, j₀ < j → leR M 0 j j₁ = true →
      entry M 1 j₀ < entry M 1 j)
    (hanc : leR M 0 j₀ j₁ = true) :
    leR M 1 j₀ j₁ = true := by
  have hj₀bound : j₀ < Lng M := hlt.trans hbound
  have hrow0 : le0 M j₀ j₁ = true := by simpa [leR] using hanc
  have hentry' : ∀ j, j₀ < j → le0 M j j₁ = true →
      entry M 1 j₀ < entry M 1 j := by
    intro j hj₀j hj
    exact hentry j hj₀j (by simpa [leR] using hj)
  have haux := le1Aux_build M (Lng M) j₀ j₁ hM hlt hbound hbound hrow0 hentry'
  simp [leR, le1, hj₀bound, hbound, haux]

#print axioms parent_exists_1
#print axioms parent_exists_2
#print axioms parent_exists_3
#print axioms parent_exists_4

end PSS
