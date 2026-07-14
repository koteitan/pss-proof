import PSS.Defs
import «5».«5.1-parent-exists»
import «5».«5.1-ancestor-basic»

/-!
# §5.1 系（直系先祖の木構造）

- 原文: `isabelle/pss_paper.thy` の `p_5_1_ancestor_tree_1`, `_2`
- 訂正: なし
- Isabelle: `m_5_1_ancestor_tree_1`, `_2`
- 依存: `5.1-parent-exists`, `5.1-ancestor-basic`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem le0Aux_index_at {M : PS} {fuel a b : ℕ}
    (h : le0Aux M fuel a b = true) : a ≤ b := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le0Aux] using h
      omega
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, hpb, _, hap⟩
      · omega
      · exact (ih hap).trans (Nat.le_of_lt hpb)

private theorem le0_index_at {M : PS} {a b : ℕ}
    (h : leR M 0 a b = true) : a ≤ b := by
  have h0 : le0 M a b = true := by simpa [leR] using h
  have hh := h0
  simp only [le0, Bool.and_eq_true] at hh
  exact le0Aux_index_at hh.2

private theorem le0Aux_refl_at (M : PS) (fuel a : ℕ) :
    le0Aux M fuel a a = true := by
  cases fuel <;> simp [le0Aux]

private theorem le1Aux_refl_at (M : PS) (fuel a : ℕ) :
    le1Aux M fuel a a = true := by
  cases fuel <;> simp [le1Aux]

private theorem le0_refl_at (M : PS) (a : ℕ) (ha : a < Lng M) :
    leR M 0 a a = true := by
  simp [leR, le0, ha, le0Aux_refl_at]

private theorem le1_refl_at (M : PS) (a : ℕ) (ha : a < Lng M) :
    leR M 1 a a = true := by
  simp [leR, le1, ha, le1Aux_refl_at]

theorem ancestor_tree_1
    (M : PS) (j₀ j j₁ : ℕ)
    (hM : TPS M) (hanc : leR M 0 j₀ j₁ = true)
    (hj₀j : j₀ ≤ j) (hjj₁ : j ≤ j₁) :
    leR M 0 j₀ j = true := by
  have hj₁bound : j₁ < Lng M := by
    have h0 : le0 M j₀ j₁ = true := by simpa [leR] using hanc
    have hh := h0
    simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.2
  by_cases heq : j = j₀
  · subst j
    exact le0_refl_at M j₀ (lt_of_le_of_lt hj₀j (lt_of_le_of_lt hjj₁ hj₁bound))
  · have hj₀lt : j₀ < j := lt_of_le_of_ne hj₀j (Ne.symm heq)
    have hjbound : j < Lng M := lt_of_le_of_lt hjj₁ hj₁bound
    apply parent_exists_3 M j₀ j hM hj₀lt hjbound
    intro k hj₀k hkj
    exact ancestor_basic_1 M j₀ k j₁ hM hj₀k (hkj.trans hjj₁) hanc

theorem row0_transitive
    (M : PS) (a b c : ℕ) (hM : TPS M)
    (hab : leR M 0 a b = true) (hbc : leR M 0 b c = true) :
    leR M 0 a c = true := by
  have habIdx := le0_index_at hab
  have hbcIdx := le0_index_at hbc
  by_cases habEq : a = b
  · simpa [habEq] using hbc
  by_cases hbcEq : b = c
  · simpa [hbcEq] using hab
  have habLt : a < b := lt_of_le_of_ne habIdx habEq
  have hbcLt : b < c := lt_of_le_of_ne hbcIdx hbcEq
  have hcBound : c < Lng M := by
    have h0 : le0 M b c = true := by simpa [leR] using hbc
    have hh := h0
    simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.2
  apply parent_exists_3 M a c hM (habLt.trans hbcLt) hcBound
  intro k hak hkc
  by_cases hkb : k ≤ b
  · exact ancestor_basic_1 M a k b hM hak hkb hab
  · have hbk : b < k := Nat.lt_of_not_ge hkb
    have habEntry : entry M 0 a < entry M 0 b :=
      ancestor_basic_1 M a b b hM habLt (le_refl _) hab
    have hbcEntry : entry M 0 b < entry M 0 k :=
      ancestor_basic_1 M b k c hM hbk hkc hbc
    omega

private theorem le1Aux_implies_row0_at
    (M : PS) (fuel a b : ℕ) (hM : TPS M) (hb : b < Lng M)
    (h : le1Aux M fuel a b = true) : leR M 0 a b = true := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le1Aux] using h
      subst b
      exact le0_refl_at M a hb
  | succ fuel ih =>
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, hpb, hpnext, hap⟩
      · subst b
        exact le0_refl_at M a hb
      · have hpBound : p < Lng M := hpb.trans hb
        have hap0 := ih p hpBound hap
        have hpb0 : leR M 0 p b = true := by
          have hn := hpnext
          simp [nextrel1] at hn
          simpa [leR] using hn.1.2
        exact row0_transitive M a p b hM hap0 hpb0

private theorem row1_implies_row0_at
    (M : PS) (a b : ℕ) (hM : TPS M) (h : leR M 1 a b = true) :
    leR M 0 a b = true := by
  have h1 : le1 M a b = true := by simpa [leR] using h
  have hh := h1
  simp only [le1, Bool.and_eq_true, decide_eq_true_eq] at hh
  exact le1Aux_implies_row0_at M (Lng M) a b hM hh.1.2 hh.2

theorem ancestor_tree_2
    (M : PS) (j₀ j j₁ : ℕ)
    (hM : TPS M) (hanc1 : leR M 1 j₀ j₁ = true)
    (hj₀j : j₀ ≤ j) (hanc0 : leR M 0 j j₁ = true) :
    leR M 1 j₀ j = true := by
  have hjbound : j < Lng M := by
    have h0 : le0 M j j₁ = true := by simpa [leR] using hanc0
    have hh := h0
    simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1
  by_cases heq : j = j₀
  · subst j
    exact le1_refl_at M j₀ hjbound
  · have hj₀lt : j₀ < j := lt_of_le_of_ne hj₀j (Ne.symm heq)
    have hrow0full := row1_implies_row0_at M j₀ j₁ hM hanc1
    have hjj₁ := le0_index_at hanc0
    have hrow0prefix := ancestor_tree_1 M j₀ j j₁ hM hrow0full hj₀j hjj₁
    apply parent_exists_4 M j₀ j hM hj₀lt hjbound
    · intro k hj₀k hkj
      have hkj₁ := row0_transitive M k j j₁ hM hkj hanc0
      have hklej := le0_index_at hkj
      exact ancestor_basic_2 M j₀ k j₁ hM hj₀k
        (hklej.trans hjj₁) hanc1 hkj₁
    · exact hrow0prefix

#print axioms ancestor_tree_1
#print axioms ancestor_tree_2
#print axioms row0_transitive

end PSS
