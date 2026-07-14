import PSS.Defs
import «5».«5.1-parent-exists»
import «5».«5.1-parent-basic»

/-!
# §5.1 系（直系先祖の基本性質）

- 原文: `isabelle/pss_paper.thy` の `p_5_1_ancestor_basic_1`, `_2`
- 訂正: なし
- Isabelle: `m_5_1_ancestor_basic_1`, `_2`
- 依存: `5.1-parent-exists`, `5.1-parent-basic`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem le0Aux_refl_ab (M : PS) (fuel a : ℕ) :
    le0Aux M fuel a a = true := by
  cases fuel <;> simp [le0Aux]

private theorem le0Aux_entry_le_ab {M : PS} {fuel a b : ℕ}
    (h : le0Aux M fuel a b = true) : entry M 0 a ≤ entry M 0 b := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le0Aux] using h
      subst b
      exact le_refl _
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, _, hpnext, hap⟩
      · subst b
        exact le_refl _
      · have haple := ih hap
        have hpEntry : entry M 0 p < entry M 0 b := by
          have hn := hpnext
          simp [nextrel0] at hn
          omega
        omega

private theorem le0Aux_entry_growth_ab {M : PS} {fuel a b c : ℕ}
    (h : le0Aux M fuel a b = true) (hac : a < c) (hcb : c ≤ b) :
    entry M 0 a < entry M 0 c := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le0Aux] using h
      omega
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, hpb, hpnext, hap⟩
      · subst b
        omega
      · by_cases hcp : c ≤ p
        · exact ih hap hcp
        · have hpc : p < c := Nat.lt_of_not_ge hcp
          have hale := le0Aux_entry_le_ab hap
          have hpEntry : entry M 0 p < entry M 0 b := by
            have hn := hpnext
            simp [nextrel0] at hn
            omega
          by_cases hcbEq : c = b
          · subst c
            omega
          · have hclt : c < b := lt_of_le_of_ne hcb hcbEq
            have hn := hpnext
            simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
              List.all_eq_true] at hn
            have hc := hn.2 c (List.mem_range.mpr hclt)
            have hble : entry M 0 b ≤ entry M 0 c := by
              simpa [hpc] using hc
            omega

theorem ancestor_basic_1
    (M : PS) (j₀ j j₁ : ℕ)
    (hM : TPS M) (hj₀j : j₀ < j) (hjj₁ : j ≤ j₁)
    (hanc : leR M 0 j₀ j₁ = true) :
    entry M 0 j₀ < entry M 0 j := by
  have h0 : le0 M j₀ j₁ = true := by simpa [leR] using hanc
  have hh := h0
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
  exact le0Aux_entry_growth_ab hh.2 hj₀j hjj₁

private theorem row0_prefix_ab
    (M : PS) (a b c : ℕ) (hM : TPS M)
    (hab : leR M 0 a b = true) (hac : a ≤ c) (hcb : c ≤ b) :
    leR M 0 a c = true := by
  have h0 : le0 M a b = true := by simpa [leR] using hab
  have hh := h0
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
  have haBound : a < Lng M := hh.1.1
  have hbBound : b < Lng M := hh.1.2
  by_cases heq : a = c
  · subst c
    simp [leR, le0, haBound, le0Aux_refl_ab]
  · have haclt : a < c := lt_of_le_of_ne hac heq
    have hcBound : c < Lng M := lt_of_le_of_lt hcb hbBound
    apply parent_exists_3 M a c hM haclt hcBound
    intro k hak hkc
    exact ancestor_basic_1 M a k b hM hak (hkc.trans hcb) hab

private theorem le1Aux_entry_le_ab {M : PS} {fuel a b : ℕ}
    (h : le1Aux M fuel a b = true) : entry M 1 a ≤ entry M 1 b := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le1Aux] using h
      subst b
      exact le_refl _
  | succ fuel ih =>
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, _, hpnext, hap⟩
      · subst b
        exact le_refl _
      · have haple := ih hap
        have hpEntry : entry M 1 p < entry M 1 b := by
          have hn := hpnext
          simp [nextrel1] at hn
          omega
        omega

private theorem le1Aux_entry_growth_ab
    {M : PS} {fuel a b c : ℕ} (hM : TPS M)
    (h : le1Aux M fuel a b = true) (hac : a < c) (hcb : c ≤ b)
    (hcanc : le0 M c b = true) : entry M 1 a < entry M 1 c := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le1Aux] using h
      omega
  | succ fuel ih =>
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, hpb, hpnext, hap⟩
      · subst b
        omega
      · have hpRow0 : le0 M p b = true := by
          have hn := hpnext
          simp [nextrel1] at hn
          exact hn.1.2
        by_cases hcp : c ≤ p
        · have hcancR : leR M 0 c b = true := by simpa [leR] using hcanc
          have hcpAncR := row0_prefix_ab M c b p hM hcancR hcp (Nat.le_of_lt hpb)
          have hcpAnc : le0 M c p = true := by simpa [leR] using hcpAncR
          exact ih hap hcp hcpAnc
        · have hpc : p < c := Nat.lt_of_not_ge hcp
          have hale := le1Aux_entry_le_ab hap
          have hpEntry : entry M 1 p < entry M 1 b := by
            have hn := hpnext
            simp [nextrel1] at hn
            omega
          have hcBound : c < Lng M := by
            have hc := hcanc
            simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hc
            exact hc.1.1
          have hn := hpnext
          simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
            List.all_eq_true] at hn
          have hc := hn.2 c (List.mem_range.mpr hcBound)
          have hble : entry M 1 b ≤ entry M 1 c := by
            simpa [hpc, hcanc] using hc
          omega

theorem ancestor_basic_2
    (M : PS) (j₀ j j₁ : ℕ)
    (hM : TPS M) (hj₀j : j₀ < j) (hjj₁ : j ≤ j₁)
    (hanc1 : leR M 1 j₀ j₁ = true)
    (hanc0 : leR M 0 j j₁ = true) :
    entry M 1 j₀ < entry M 1 j := by
  have h1 := hanc1
  simp only [leR, if_neg (by decide : (1 : ℕ) ≠ 0), le1,
    Bool.and_eq_true, decide_eq_true_eq] at h1
  have h0 : le0 M j j₁ = true := by simpa [leR] using hanc0
  exact le1Aux_entry_growth_ab hM h1.2 hj₀j hjj₁ h0

#print axioms ancestor_basic_1
#print axioms ancestor_basic_2

end PSS
