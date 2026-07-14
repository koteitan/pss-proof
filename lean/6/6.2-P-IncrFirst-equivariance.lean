import PSS.Mono
import «6».«6.1-le-IncrFirst-invariance»

/-!
# §6.2 命題（`P` の `IncrFirst` 同変性）

- 原文: `isabelle/pss_paper.thy` の `p_6_2_P_IncrFirst`
- 訂正: なし
- Isabelle: `m_6_2_P_IncrFirst`
- 依存: `PSS.Mono`, `6.1-le-IncrFirst-invariance`
- 状態: ✅ 証明済み
-/

namespace PSS

@[simp] private theorem length_incr_p (M : PS) :
    Lng (IncrFirst M) = Lng M := by simp [IncrFirst]

private theorem row1_incr_p (M : PS) (j : ℕ) :
    entry (IncrFirst M) 1 j = entry M 1 j := by
  simp only [IncrFirst, entry, List.getElem?_map]
  cases h : M[j]? <;> simp [h]

private theorem zero_incr_p (M : PS) :
    zeroT (IncrFirst M) = zeroT M := by
  simp [zeroT, row1_incr_p]

private theorem mono_incr_p (M : PS) :
    monoT (IncrFirst M) = monoT M := by
  simp [monoT, zero_incr_p, le_IncrFirst_invariance]

private theorem multi_incr_p (M : PS) :
    multiT (IncrFirst M) = multiT M := by
  simp [multiT, zero_incr_p, mono_incr_p]

private theorem pcut_incr_p (M : PS) :
    Pcut (IncrFirst M) = Pcut M := by
  simp [Pcut, le_IncrFirst_invariance]

private theorem take_incr_p (M : PS) (k : ℕ) :
    (IncrFirst M).take k = IncrFirst (M.take k) := by
  simp [IncrFirst]

private theorem drop_incr_p (M : PS) (k : ℕ) :
    (IncrFirst M).drop k = IncrFirst (M.drop k) := by
  simp [IncrFirst]

private theorem pAux_incr_p (fuel : ℕ) (M : PS) :
    PAux fuel (IncrFirst M) = (PAux fuel M).map IncrFirst := by
  induction fuel generalizing M with
  | zero => simp [PAux]
  | succ fuel ih =>
      simp only [PAux, multi_incr_p, length_incr_p, pcut_incr_p,
        take_incr_p, drop_incr_p]
      by_cases h : (multiT M && decide (1 < Lng M)) = true
      · rw [if_pos h, if_pos h]
        simp [ih]
      · rw [if_neg h, if_neg h]
        simp

theorem P_IncrFirst_equivariance (M : PS) :
    P (IncrFirst M) = (P M).map IncrFirst := by
  simp [P, pAux_incr_p]

#print axioms P_IncrFirst_equivariance

end PSS
