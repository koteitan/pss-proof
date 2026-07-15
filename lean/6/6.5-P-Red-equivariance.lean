import «6».«6.2-P-additivity»
import «6».«6.5-Red-preserves-monoT»

/-!
# §6.5 系（`P` の `Red` 同変性）

- 原文: `isabelle/pss_paper.thy` の `p_6_5_P_Red`
- 訂正: A4（原文の `TPS` 版は偽。`anchoredSlice` 上に制限）
- Isabelle: `m_6_5_P_Red_final`
- 依存: `6.5-Red-preserves-monoT`, §6.2 `P_nonmulti_eq`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-- 訂正 A4 後の主張: `P (Red M)` は各 `P M` 成分を簡約した列に一致する。 -/
theorem P_Red_equivariance (M : PS) (hM : anchoredSlice M) :
    P (Red M) = (P M).map Red := by
  have hMT : TPS M := by
    rcases hM with ⟨S, a, b, hsource, hab, hbL, habAnc, hseg⟩
    rw [hseg]
    apply List.ne_nil_of_length_pos
    simp
    omega
  have hnonmulti : multiT M = false := by
    rcases anchoredSlice_zero_or_mono M hM with hz | hmono
    · simp [multiT, hz]
    · simp [multiT, hmono]
  have hnonmultiR : multiT (Red M) = false := by
    rcases anchoredSlice_zero_or_mono M hM with hz | hmono
    · have hzR := (Red_preserves_zeroT M hMT).mp hz
      simp [multiT, hzR]
    · have hmonoR := Red_preserves_monoT_forward M hMT hmono
      simp [multiT, hmonoR]
  rw [P_nonmulti_eq M hnonmulti, P_nonmulti_eq (Red M) hnonmultiR]
  simp

/-- 原文の `TPS` 版に対する A4 の最小反例。 -/
theorem P_Red_equivariance_original_false :
    ∃ M : PS, TPS M ∧ P (Red M) ≠ (P M).map Red := by
  refine ⟨[(0, 0), (0, 1)], ?_, ?_⟩
  · simp [TPS]
  · decide

#print axioms P_Red_equivariance
#print axioms P_Red_equivariance_original_false

end PSS
