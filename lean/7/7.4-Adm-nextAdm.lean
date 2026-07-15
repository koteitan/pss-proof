import «6».«6.6-condAB-coeff»
import «6».«6.3-admof-slice»

/-!
# §7.4 命題（`Adm_M` と許容的親子関係の関係）

- 原文: `tmp/content.md` §7.4
- 訂正: なし
- Isabelle: `m_7_4_Adm_nextAdm`
- 状態: 証明済（`sorry` 0）
-/

namespace PSS

private theorem le1Aux_consecutive_chain_74 (M : PS) (a b fuel : ℕ)
    (hab : a ≤ b)
    (hstep : ∀ j, a < j → j ≤ b → nextrel1 M (j - 1) j = true)
    (hfuel : b - a ≤ fuel) : le1Aux M fuel a b = true := by
  induction fuel generalizing b with
  | zero =>
      have : a = b := by omega
      subst b
      simp [le1Aux]
  | succ fuel ih =>
      by_cases heq : a = b
      · subst b
        simp [le1Aux]
      · have hablt : a < b := lt_of_le_of_ne hab heq
        rw [le1Aux]
        simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
          Bool.and_eq_true, List.mem_range]
        right
        refine ⟨b - 1, by omega, hstep b hablt (le_refl _), ?_⟩
        apply ih (b := b - 1)
        · omega
        · intro j haj hjb
          exact hstep j haj (by omega)
        · omega

/-- The admissibilization of an in-range column is its row-one ancestor. -/
theorem adm_row1_ancestry (M : PS) (j : ℕ)
    (hM : TPS M) (hj : j ≤ Lng M - 1) :
    leR M 1 (Adm M j) j = true := by
  have hL : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hjL : j < Lng M := by omega
  have haLe : Adm M j ≤ j := Adm_le M j
  have haL : Adm M j < Lng M := haLe.trans_lt hjL
  have hstep : ∀ k, Adm M j < k → k ≤ j →
      nextrel1 M (k - 1) k = true := by
    intro k hak hkj
    have hkadm : adm M k = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hk
      have hmax := Adm_max M k j hk hkj
      omega
    have hnadm : nadm M k = true := by
      simpa [adm] using hkadm
    have hkL : k < Lng M := hkj.trans_lt hjL
    have hpair : nextR M 1 (k - 1) k = true ∧
        nextR M 1 k (k + 1) = true := by
      have hn := hnadm
      simp only [nadm, Bool.or_eq_true, decide_eq_true_eq,
        Bool.and_eq_true] at hn
      rcases hn with hn | hn
      · omega
      · exact hn
    simpa [nextR] using hpair.1
  have haux : le1Aux M (Lng M) (Adm M j) j = true :=
    le1Aux_consecutive_chain_74 M (Adm M j) j (Lng M)
      haLe hstep (by omega)
  simp [leR, le1, haL, hjL, haux]

private theorem le0Aux_index_74 {M : PS} {fuel a b : ℕ}
    (h : le0Aux M fuel a b = true) : a ≤ b := by
  induction fuel generalizing b with
  | zero =>
      have : a = b := by simpa [le0Aux] using h
      omega
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, hpb, _, hap⟩
      · omega
      · exact (ih hap).trans (Nat.le_of_lt hpb)

private theorem le1Aux_index_74 {M : PS} {fuel a b : ℕ}
    (h : le1Aux M fuel a b = true) : a ≤ b := by
  induction fuel generalizing b with
  | zero =>
      have : a = b := by simpa [le1Aux] using h
      omega
  | succ fuel ih =>
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, hpb, _, hap⟩
      · omega
      · exact (ih hap).trans (Nat.le_of_lt hpb)

private theorem le0Aux_refl_74 (M : PS) (fuel a : ℕ) :
    le0Aux M fuel a a = true := by
  cases fuel <;> simp [le0Aux]

private theorem le1Aux_implies_row0_74 (M : PS) (fuel a b : ℕ)
    (hM : TPS M) (hb : b < Lng M)
    (h : le1Aux M fuel a b = true) : leR M 0 a b = true := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le1Aux] using h
      subst b
      simp [leR, le0, hb, le0Aux_refl_74]
  | succ fuel ih =>
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, hpb, hpnext, hap⟩
      · subst b
        simp [leR, le0, hb, le0Aux_refl_74]
      · have hpL : p < Lng M := hpb.trans hb
        have hap₀ := ih p hpL hap
        have hpb₀ : leR M 0 p b = true := by
          have hn := hpnext
          simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hn
          simpa [leR] using hn.1.2
        exact row0_transitive M a p b hM hap₀ hpb₀

/-- Every row-one ancestor is also a row-zero ancestor. -/
theorem row1_implies_row0 (M : PS) (a b : ℕ)
    (hM : TPS M) (h : leR M 1 a b = true) :
    leR M 0 a b = true := by
  have h₁ : le1 M a b = true := by simpa [leR] using h
  have hh := h₁
  simp only [le1, Bool.and_eq_true, decide_eq_true_eq] at hh
  exact le1Aux_implies_row0_74 M (Lng M) a b hM hh.1.2 hh.2

private theorem parent_max_74 (M : PS) {i k p j : ℕ}
    (hp : hasParent M i j = true) (hpj : nextR M i p j = true)
    (hkj : leR M i k j = true) (hklt : k < j) : k ≤ p := by
  by_cases hi : i = 0
  · have hle : le0 M k j = true := by simpa [leR, hi] using hkj
    have hh := hle
    simp only [le0, Bool.and_eq_true] at hh
    cases hL : Lng M with
    | zero => simp [hL] at hh
    | succ fuel =>
        have haux := hh.2
        rw [hL] at haux
        simp only [le0Aux, Bool.or_eq_true, beq_iff_eq,
          List.any_eq_true, Bool.and_eq_true, List.mem_range] at haux
        rcases haux with heq | ⟨q, hqj, hqnext, hkq⟩
        · omega
        · have hqnextR : nextR M i q j = true := by
            simpa [nextR, hi] using hqnext
          have hqp : q = p := by
            obtain ⟨u, hu, huniq⟩ := (hasParent_iff_unique_fseq M i j).mp hp
            exact (huniq q hqnextR).trans (huniq p hpj).symm
          subst q
          exact le0Aux_index_74 hkq
  · have hle : le1 M k j = true := by simpa [leR, hi] using hkj
    have hh := hle
    simp only [le1, Bool.and_eq_true] at hh
    cases hL : Lng M with
    | zero => simp [hL] at hh
    | succ fuel =>
        have haux := hh.2
        rw [hL] at haux
        simp only [le1Aux, Bool.or_eq_true, beq_iff_eq,
          List.any_eq_true, Bool.and_eq_true, List.mem_range] at haux
        rcases haux with heq | ⟨q, hqj, hqnext, hkq⟩
        · omega
        · have hqnextR : nextR M i q j = true := by
            simpa [nextR, hi] using hqnext
          have hqp : q = p := by
            obtain ⟨u, hu, huniq⟩ := (hasParent_iff_unique_fseq M i j).mp hp
            exact (huniq q hqnextR).trans (huniq p hpj).symm
          subst q
          exact le1Aux_index_74 hkq

/-- If the last column has a parent in row `i`, admissibilizing that parent
gives the admissible parent of the last column. -/
theorem Adm_nextAdm (M : PS) (i : ℕ) (hM : TPS M)
    (hp : hasParent M i (Lng M - 1) = true) :
    nextAdm M i (Adm M (parent M i (Lng M - 1))) (Lng M - 1) = true := by
  let j₁ := Lng M - 1
  let j₀ := parent M i j₁
  let a := Adm M j₀
  have hpar : nextR M i j₀ j₁ = true := hasParent_next_fseq M i j₁ hp
  have hj₀lt : j₀ < j₁ := parent_lt_of_hasParent M i j₁ hp
  have hj₀last : j₀ ≤ Lng M - 1 := by omega
  have hale : a ≤ j₀ := Adm_le M j₀
  have halt : a < j₁ := hale.trans_lt hj₀lt
  have haadm : adm M a = true := Adm_adm M j₀
  have ha₁j₀ : leR M 1 a j₀ = true :=
    adm_row1_ancestry M j₀ hM hj₀last
  have haj₁ : leR M i a j₁ = true := by
    by_cases hi : i = 0
    · subst i
      have ha₀j₀ : leR M 0 a j₀ = true :=
        row1_implies_row0 M a j₀ hM ha₁j₀
      exact leR_then_next_cc M 0 a j₀ j₁ hM ha₀j₀ hpar
    · have haij₀ : leR M i a j₀ = true := by simpa [leR, hi] using ha₁j₀
      exact leR_then_next_cc M i a j₀ j₁ hM haij₀ hpar
  simp only [nextAdm, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.or_eq_true]
  refine ⟨⟨⟨haj₁, halt⟩, haadm⟩, ?_⟩
  intro j hj
  simp only [List.mem_range] at hj
  by_cases haj : a < j
  · by_cases hanc : leR M i j j₁ = true
    · right
      have hnotadm : adm M j = false := by
        apply Bool.eq_false_of_not_eq_true
        intro hjadm
        have hjle : j ≤ j₀ := parent_max_74 M hp hpar hanc (by omega)
        have hjlea : j ≤ a := Adm_max M j j₀ hjadm hjle
        omega
      simp [hnotadm]
    · left
      right
      have hf := Bool.eq_false_of_not_eq_true hanc
      simpa [hf]
  · left
    have : j ≤ a := Nat.le_of_not_gt haj
    left
    simpa [a, j₀] using this

#print axioms adm_row1_ancestry
#print axioms row1_implies_row0
#print axioms Adm_nextAdm

end PSS
