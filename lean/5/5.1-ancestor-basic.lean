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

private theorem le0Aux_refl_path (M : PS) (fuel a : ℕ) :
    le0Aux M fuel a a = true := by
  cases fuel <;> simp [le0Aux]

/-- Read the executable row-0 ancestor test as an ordinary finite parent path. -/
private theorem le0Aux_to_reflTransGen {M : PS} {fuel a b : ℕ}
    (h : le0Aux M fuel a b = true) :
    Relation.ReflTransGen (fun x y => nextrel0 M x y = true) a b := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le0Aux] using h
      subst b
      exact .refl
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with hab | ⟨p, _, hpnext, hap⟩
      · subst b
        exact .refl
      · exact (ih hap).tail hpnext

/-- Read the executable row-1 ancestor test as an ordinary finite parent path. -/
private theorem le1Aux_to_reflTransGen {M : PS} {fuel a b : ℕ}
    (h : le1Aux M fuel a b = true) :
    Relation.ReflTransGen (fun x y => nextrel1 M x y = true) a b := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le1Aux] using h
      subst b
      exact .refl
  | succ fuel ih =>
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with hab | ⟨p, _, hpnext, hap⟩
      · subst b
        exact .refl
      · exact (ih hap).tail hpnext

/-- Along a row-0 parent path, the entry at the start is strictly below every
intermediate index.  The proof consumes the path from the head: once its next
vertex reaches `c`, parent minimality closes the argument. -/
private theorem nextrel0_path_entry_growth {M : PS} {a b c : ℕ}
    (h : Relation.ReflTransGen (fun x y => nextrel0 M x y = true) a b)
    (hac : a < c) (hcb : c ≤ b) : entry M 0 a < entry M 0 c := by
  induction h using Relation.ReflTransGen.head_induction_on generalizing c with
  | refl => omega
  | @head a p hap hpb ih =>
    have hapIdx : a < p := by
      have hn := hap
      simp [nextrel0] at hn
      omega
    have hapEntry : entry M 0 a < entry M 0 p := by
      have hn := hap
      simp [nextrel0] at hn
      omega
    by_cases hcp : c ≤ p
    · by_cases hcEq : c = p
      · subst c
        exact hapEntry
      · have hcpLt : c < p := lt_of_le_of_ne hcp hcEq
        have hn := hap
        simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
          List.all_eq_true] at hn
        have hc := hn.2 c (List.mem_range.mpr hcpLt)
        have hpEntry : entry M 0 p ≤ entry M 0 c := by
          simpa [hac] using hc
        omega
    · have hpc : p < c := Nat.lt_of_not_ge hcp
      have hpcEntry := ih hpc hcb
      omega

theorem ancestor_basic_1
    (M : PS) (j₀ j j₁ : ℕ)
    (hM : TPS M) (hj₀j : j₀ < j) (hjj₁ : j ≤ j₁)
    (hanc : leR M 0 j₀ j₁ = true) :
    entry M 0 j₀ < entry M 0 j := by
  have h0 : le0 M j₀ j₁ = true := by simpa [leR] using hanc
  have hh := h0
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
  exact nextrel0_path_entry_growth (le0Aux_to_reflTransGen hh.2) hj₀j hjj₁

private theorem row0_prefix_path
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
    simp [leR, le0, haBound, le0Aux_refl_path]
  · have haclt : a < c := lt_of_le_of_ne hac heq
    have hcBound : c < Lng M := lt_of_le_of_lt hcb hbBound
    apply parent_exists_3 M a c hM haclt hcBound
    intro k hak hkc
    exact ancestor_basic_1 M a k b hM hak (hkc.trans hcb) hab

private theorem nextrel1_path_index_le {M : PS} {a b : ℕ}
    (h : Relation.ReflTransGen (fun x y => nextrel1 M x y = true) a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl _
  | @tail p q h hp ih =>
      have hpIdx : p < q := by
        have hn := hp
        simp [nextrel1] at hn
        omega
      omega

/-- Row-1 analogue of `nextrel0_path_entry_growth`.  When the next path vertex
already reaches `c`, the row-0 prefix property supplies the side condition in
the definition of a row-1 parent. -/
private theorem nextrel1_path_entry_growth
    {M : PS} {a b c : ℕ} (hM : TPS M)
    (h : Relation.ReflTransGen (fun x y => nextrel1 M x y = true) a b)
    (hac : a < c) (hcb : c ≤ b)
    (hcanc : le0 M c b = true) : entry M 1 a < entry M 1 c := by
  induction h using Relation.ReflTransGen.head_induction_on generalizing c with
  | refl => omega
  | @head a p hap hpb ih =>
    have hapIdx : a < p := by
      have hn := hap
      simp [nextrel1] at hn
      omega
    have hapEntry : entry M 1 a < entry M 1 p := by
      have hn := hap
      simp [nextrel1] at hn
      omega
    by_cases hcp : c ≤ p
    · have hpBound : p ≤ b := nextrel1_path_index_le hpb
      have hcancR : leR M 0 c b = true := by simpa [leR] using hcanc
      have hcpAncR := row0_prefix_path M c b p hM hcancR hcp hpBound
      have hcpAnc : le0 M c p = true := by simpa [leR] using hcpAncR
      by_cases hcEq : c = p
      · subst c
        exact hapEntry
      · have hcpLt : c < p := lt_of_le_of_ne hcp hcEq
        have hcBound : c < Lng M := by
          have hc := hcpAnc
          simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hc
          exact hc.1.1
        have hn := hap
        simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
          List.all_eq_true] at hn
        have hc := hn.2 c (List.mem_range.mpr hcBound)
        have hpEntry : entry M 1 p ≤ entry M 1 c := by
          simpa [hac, hcpAnc] using hc
        omega
    · have hpc : p < c := Nat.lt_of_not_ge hcp
      have hpcEntry := ih hpc hcb hcanc
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
  exact nextrel1_path_entry_growth hM (le1Aux_to_reflTransGen h1.2) hj₀j hjj₁ h0

#print axioms ancestor_basic_1
#print axioms ancestor_basic_2

end PSS
