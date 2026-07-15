import «7».«7.3-Trans-IncrFirst-Red»

/-!
# §7.3 命題（`Trans` が零項性を保つこと）

- 原文: `tmp/content.md` の同名命題
- Isabelle: `m_7_3_Trans_zeroT`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem Trans_zero_singleton : Trans [(0, 0)] = BZero := by
  have hR : RTPS [(0, 0)] := by
    simpa [diagSeq] using RTPS_diagSeq_zero 0
  rw [Trans_eq_lengthAux [(0, 0)] hR]
  have hred : reduced [(0, 0)] = true := hR
  simp only [TransAux, hred, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, lastIdx]
  simp [entry]

/-- Translation reflects and preserves the zero pair sequence. -/
theorem Trans_preserves_zeroT (M : PS) (hM : TPS M) :
    zeroT M = true ↔ Trans M = BZero := by
  constructor
  · intro hz
    calc
      Trans M = Trans (Red M) := Trans_Red M hM
      _ = Trans [(0, 0)] := by rw [Red_zero_mr M hz]
      _ = BZero := Trans_zero_singleton
  · intro hzero
    have hRM : TPS (Red M) := Red_TPS M hM
    have hRR := Red2 M hM
    by_contra hnot
    have hzM : zeroT M = false := Bool.eq_false_of_not_eq_true hnot
    have hzRR : zeroT (Red (Red M)) = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hz2
      have hz1 := (Red_preserves_zeroT (Red M) hRM).mpr hz2
      have hz0 := (Red_preserves_zeroT M hM).mpr hz1
      rw [hzM] at hz0
      contradiction
    have hne := (Trans_Mark_invariant (Red (Red M)) hRR).2.1 hzRR
    apply hne
    calc
      Trans (Red (Red M)) = Trans (Red M) :=
        (Trans_Red (Red M) hRM).symm
      _ = Trans M := (Trans_Red M hM).symm
      _ = BZero := hzero

#print axioms Trans_preserves_zeroT

end PSS
