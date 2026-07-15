import «7».«7.3-Trans-IncrFirst-Red»

/-!
# §7.3 命題（`Mark` の `(IncrFirst, Red, P)` 不変性）

- 原文: `tmp/content.md` の同名命題
- 訂正: A15（`Red` 軌道は二段で簡約核へ到達）、P 成分の
  添字と offset の off-by-one を修正
- Isabelle: `m_7_3_Mark_Red`, `m_7_3_Mark_IncrFirst`,
  `m_7_3_Mark_P_invariance`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem mark_fuel_after_red_ge (M : PS) (hM : TPS M) :
    Lng (Red M) ≤ transFuel M - 1 := by
  have hmul : Lng M + 1 ≤ 8 * (nu M + 1) * (Lng M + 1) :=
    Nat.le_mul_of_pos_left (Lng M + 1) (by positivity)
  rw [Lng_Red_invariance M hM]
  simp only [transFuel]
  omega

private theorem mark_fuel_after_red2_ge (M : PS) (hM : TPS M) :
    Lng (Red (Red M)) ≤ transFuel M - 2 := by
  have hRM : TPS (Red M) := Red_TPS M hM
  have hfactor : 2 ≤ 8 * (nu M + 1) := by
    calc
      2 ≤ 8 * 1 := by norm_num
      _ ≤ 8 * (nu M + 1) :=
        Nat.mul_le_mul_left 8 (Nat.succ_le_succ (Nat.zero_le (nu M)))
  have hmul : Lng M + 2 ≤ 8 * (nu M + 1) * (Lng M + 1) := by
    calc
      Lng M + 2 ≤ 2 * (Lng M + 1) := by omega
      _ ≤ (8 * (nu M + 1)) * (Lng M + 1) :=
        Nat.mul_le_mul_right (Lng M + 1) hfactor
  rw [Lng_Red_invariance (Red M) hRM, Lng_Red_invariance M hM]
  simp only [transFuel]
  omega

/-- One reduction step agrees with the public marked value when that reduct
is already reduced. -/
theorem Mark_Red_of_Red_reduced (M : PS) (m : ℕ) (hM : TPS M)
    (hRR : RTPS (Red M)) :
    Mark M m = Mark (Red M) m := by
  by_cases hR : RTPS M
  · rw [RTPS_Red_eq M hR]
  · have hred : reduced M = false := Bool.eq_false_of_not_eq_true hR
    calc
      Mark M m = MarkAux (transFuel M - 1) (Red M) m := by
        rw [Mark, show transFuel M = (transFuel M - 1) + 1 by
          have : 0 < transFuel M := by simp [transFuel]
          omega]
        simp [MarkAux, hred]
      _ = MarkAux (transFuel (Red M)) (Red M) m :=
        (TransAux_MarkAux_fuel_irrel_RTPS (Red M) hRR
          (transFuel M - 1) (transFuel (Red M))
          (mark_fuel_after_red_ge M hM)
          (transFuel_ge_length (Red M))).2 m
      _ = Mark (Red M) m := rfl

private theorem Mark_Red_of_Red2 (M : PS) (m : ℕ) (hM : TPS M)
    (hRR2 : RTPS (Red (Red M))) :
    Mark M m = Mark (Red M) m := by
  by_cases hRR : RTPS (Red M)
  · exact Mark_Red_of_Red_reduced M m hM hRR
  · have hRM : TPS (Red M) := Red_TPS M hM
    have hredR : reduced (Red M) = false :=
      Bool.eq_false_of_not_eq_true hRR
    have hredM : reduced M = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hR
      have hfix : Red M = M := RTPS_Red_eq M hR
      exact hRR (by simpa [hfix] using hR)
    have hfuel : 2 ≤ transFuel M := by
      have hfactor : 2 ≤ 8 * (nu M + 1) := by
        calc
          2 ≤ 8 * 1 := by norm_num
          _ ≤ 8 * (nu M + 1) :=
            Nat.mul_le_mul_left 8 (Nat.succ_le_succ (Nat.zero_le (nu M)))
      calc
        2 ≤ 2 * (Lng M + 1) := by omega
        _ ≤ (8 * (nu M + 1)) * (Lng M + 1) :=
          Nat.mul_le_mul_right (Lng M + 1) hfactor
        _ ≤ transFuel M := by simp [transFuel]
    calc
      Mark M m = MarkAux (transFuel M - 2) (Red (Red M)) m := by
        rw [Mark, show transFuel M = (transFuel M - 2) + 2 by omega]
        simp [MarkAux, hredM, hredR]
      _ = MarkAux (transFuel (Red (Red M))) (Red (Red M)) m :=
        (TransAux_MarkAux_fuel_irrel_RTPS (Red (Red M)) hRR2
          (transFuel M - 2) (transFuel (Red (Red M)))
          (mark_fuel_after_red2_ge M hM)
          (transFuel_ge_length (Red (Red M)))).2 m
      _ = Mark (Red (Red M)) m := rfl
      _ = Mark (Red M) m :=
        (Mark_Red_of_Red_reduced (Red M) m hRM hRR2).symm

/-- Reduction leaves every marked translation value invariant. -/
theorem Mark_Red (M : PS) (m : ℕ) (hM : TPS M) :
    Mark M m = Mark (Red M) m :=
  Mark_Red_of_Red2 M m hM (Red2 M hM)

/-- Incrementing row zero leaves every marked translation value invariant. -/
theorem Mark_IncrFirst (M : PS) (m : ℕ) (hM : TPS M) :
    Mark (IncrFirst M) m = Mark M m := by
  have hIT : TPS (IncrFirst M) := by
    simpa [TPS, IncrFirst] using hM
  have hRI : Red (IncrFirst M) = Red M := Red_IncrFirst M hM
  calc
    Mark (IncrFirst M) m = Mark (Red (IncrFirst M)) m :=
      Mark_Red (IncrFirst M) m hIT
    _ = Mark (Red M) m := by rw [hRI]
    _ = Mark M m := (Mark_Red M m hM).symm

/-- Part (1) of the corrected `Mark` invariance proposition. -/
theorem Mark_IncrFirst_Red (M : PS) (m : ℕ) (hM : TPS M) :
    Mark M m = Mark (Red M) m ∧ Mark M m = Mark (IncrFirst M) m :=
  ⟨Mark_Red M m hM, (Mark_IncrFirst M m hM).symm⟩

/-- Corrected P-component equation.  The last component is
`M.drop (Pcut M)` and its column offset is exactly `Pcut M`; the `-1` in the
source prose is an off-by-one typo. -/
theorem Mark_P_invariance (M : PS) (m : ℕ) (hR : RTPS M)
    (hmulti : multiT M = true) :
    Mark M m = if M.drop (Pcut M) == [(0, 0)] then Dprin 0 BZero
      else Mark (M.drop (Pcut M)) (m - Pcut M) := by
  exact (Trans_Mark_multi_equations M hR hmulti).2 m

#print axioms Mark_Red_of_Red_reduced
#print axioms Mark_Red
#print axioms Mark_IncrFirst
#print axioms Mark_IncrFirst_Red
#print axioms Mark_P_invariance

end PSS
