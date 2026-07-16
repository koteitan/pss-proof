import «6».«6.5-Red-preserves-adm»

/-!
# §6.5 系（許容化の `Red` 不変性）

- 原文: `isabelle/pss_paper.thy` の `p_6_5_admof_Red`
- 訂正: A4（原文の `TPS` 版は偽。`anchoredSlice` 上に制限）
- Isabelle: `m_6_5_admof_Red_final`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-- Corrected A4: reduction does not change admissibilization. -/
theorem Adm_Red_invariance (M : PS) (j : ℕ) (hM : anchoredSlice M) :
    Adm M j = Adm (Red M) j := by
  simp [Adm, ← adm_Red_eq M hM]

#print axioms Adm_Red_invariance

end PSS
