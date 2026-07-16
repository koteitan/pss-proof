import «7».«7.4-RightAnces-RightNodes»

/-!
# §7.4 系（非零項の `RightAnces` が非空）

- 原文: `isabelle/pss_paper.thy` の `p_7_4_RightAnces_zeroT`
- Isabelle: `m_7_4_RightAnces_zeroT`
- 定式化する範囲: 訂正後の `RTPS` 上の形
-/

namespace PSS

private theorem rightNodesList_ne_nil (ps : List BP) (hps : ps ≠ []) :
    rightNodesList ps ≠ [] := by
  induction ps with
  | nil => exact (hps rfl).elim
  | cons p ps ih =>
      cases ps with
      | nil =>
          rcases p with ⟨v, t⟩
          simp [rightNodesList, rightNodesBP]
      | cons q qs =>
          exact ih (by simp)

/-- A Buchholz term has no right-spine nodes exactly when it is zero. -/
theorem RightNodes_eq_nil_iff (t : BT) :
    RightNodes t = [] ↔ t = BZero := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => simp [BZero, RightNodes, rightNodesList]
  | cons p ps =>
      have hne : rightNodesList (p :: ps) ≠ [] :=
        rightNodesList_ne_nil (p :: ps) (by simp)
      constructor
      · intro h
        exact (hne (by simpa [RightNodes] using h)).elim
      · intro h
        simp [BZero] at h

/-- Corrected `RTPS` form of the article corollary. -/
theorem RightAnces_zeroT (M : PS) (hR : RTPS M) :
    zeroT M = true ↔ RightAnces M = [] := by
  have hM : TPS M := RTPS_TPS M hR
  rw [RightAnces_RightNodes M hR, RightNodes_eq_nil_iff]
  exact Trans_preserves_zeroT M hM

theorem m_7_4_RightAnces_zeroT (M : PS) (hR : RTPS M) :
    zeroT M = true ↔ RightAnces M = [] :=
  RightAnces_zeroT M hR

#print axioms RightNodes_eq_nil_iff
#print axioms RightAnces_zeroT

end PSS
