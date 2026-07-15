import PSS.Red

/-!
# §6.5 命題（`Red` の冪等性）

- 原文: `isabelle/pss_paper.thy` の `p_6_5_Red_idem`
- 訂正: A4（原文の `TPS` 上の主張は偽。`RTPS` 上に制限）
- Isabelle: `m_6_5_Red_idem`
- 依存: `PSS.Red`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-- 簡約形では、定義どおり `Red M = M` である。 -/
theorem Red_eq_self_of_RTPS (M : PS) (hM : RTPS M) :
    Red M = M := by
  have h := hM
  simp only [RTPS, reduced, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-- 訂正 A4 後の冪等性: 入力を簡約形に制限する。 -/
theorem Red_idempotence (M : PS) (hM : RTPS M) :
    Red (Red M) = Red M := by
  exact congrArg Red (Red_eq_self_of_RTPS M hM)

/-- 原文の `TPS` 版が偽であることを固定する反例。 -/
theorem Red_idempotence_original_false :
    ∃ M : PS, TPS M ∧ Red (Red M) ≠ Red M := by
  refine ⟨[(0, 0), (0, 2)], ?_, ?_⟩
  · simp [TPS]
  · decide

#print axioms Red_idempotence
#print axioms Red_idempotence_original_false

end PSS
