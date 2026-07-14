import PSS.Defs

/-!
# §6.1 命題（`≤_M` の `IncrFirst` 不変性）

- 原文: `isabelle/pss_paper.thy` の `p_6_1_le_IncrFirst_inv`
- 訂正: なし
- Isabelle: `m_6_1_le_IncrFirst_inv`
- 依存: `PSS.Defs`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

@[simp] private theorem length_incr (M : PS) : Lng (IncrFirst M) = Lng M := by
  simp [IncrFirst]

private theorem entry_incr (M : PS) (i j : ℕ) (hj : j < Lng M) :
    entry (IncrFirst M) i j =
      if i = 0 then entry M 0 j + 1 else entry M i j := by
  by_cases hi : i = 0 <;> simp [IncrFirst, entry, hj, hi]

private theorem nextrel0_incr (M : PS) (a b : ℕ) :
    nextrel0 (IncrFirst M) a b = nextrel0 M a b := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, length_incr] at h ⊢
    rcases h with ⟨⟨⟨⟨ha, hb⟩, hab⟩, he⟩, hall⟩
    refine ⟨⟨⟨⟨ha, hb⟩, hab⟩, ?_⟩, ?_⟩
    · simpa [entry_incr, ha, hb] using he
    · intro k hk
      have hkb : k < b := List.mem_range.mp hk
      have hkL : k < Lng M := hkb.trans hb
      simpa [entry_incr, hb, hkL] using hall k hk
  · intro h
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, length_incr] at h ⊢
    rcases h with ⟨⟨⟨⟨ha, hb⟩, hab⟩, he⟩, hall⟩
    refine ⟨⟨⟨⟨ha, hb⟩, hab⟩, ?_⟩, ?_⟩
    · simpa [entry_incr, ha, hb] using he
    · intro k hk
      have hkb : k < b := List.mem_range.mp hk
      have hkL : k < Lng M := hkb.trans hb
      simpa [entry_incr, hb, hkL] using hall k hk

private theorem le0Aux_incr (M : PS) (fuel a b : ℕ) :
    le0Aux (IncrFirst M) fuel a b = le0Aux M fuel a b := by
  induction fuel generalizing b with
  | zero => simp [le0Aux]
  | succ fuel ih =>
      simp only [le0Aux, nextrel0_incr, ih]

private theorem le0_incr (M : PS) (a b : ℕ) :
    le0 (IncrFirst M) a b = le0 M a b := by
  simp [le0, le0Aux_incr]

private theorem nextrel1_incr (M : PS) (a b : ℕ) :
    nextrel1 (IncrFirst M) a b = nextrel1 M a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, length_incr, le0_incr]
  constructor
  · rintro ⟨⟨⟨⟨⟨ha, hb⟩, hab⟩, he⟩, h0⟩, hall⟩
    refine ⟨⟨⟨⟨⟨ha, hb⟩, hab⟩, ?_⟩, h0⟩, ?_⟩
    · simpa [entry_incr, ha, hb] using he
    · intro k hk
      have hkL : k < Lng M := List.mem_range.mp hk
      simpa [entry_incr, hb, hkL] using hall k hk
  · rintro ⟨⟨⟨⟨⟨ha, hb⟩, hab⟩, he⟩, h0⟩, hall⟩
    refine ⟨⟨⟨⟨⟨ha, hb⟩, hab⟩, ?_⟩, h0⟩, ?_⟩
    · simpa [entry_incr, ha, hb] using he
    · intro k hk
      have hkL : k < Lng M := List.mem_range.mp hk
      simpa [entry_incr, hb, hkL] using hall k hk

private theorem le1Aux_incr (M : PS) (fuel a b : ℕ) :
    le1Aux (IncrFirst M) fuel a b = le1Aux M fuel a b := by
  induction fuel generalizing b with
  | zero => simp [le1Aux]
  | succ fuel ih =>
      simp only [le1Aux, nextrel1_incr, ih]

private theorem le1_incr (M : PS) (a b : ℕ) :
    le1 (IncrFirst M) a b = le1 M a b := by
  simp [le1, le1Aux_incr]

theorem le_IncrFirst_invariance (M : PS) (i j₀ j₁ : ℕ) :
    leR (IncrFirst M) i j₀ j₁ = leR M i j₀ j₁ := by
  unfold leR
  split <;> simp [le0_incr, le1_incr]

#print axioms le_IncrFirst_invariance

end PSS
