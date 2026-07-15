import PSS.Flat

/-!
# §7.2 命題（scb 分解の自明性の判定条件）

- Isabelle: `m_7_2_scb_triviality`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem scb_eq_implies_empty {t c : BT} (htc : t = c) :
    ∀ s b, scb_decomp t s (flatBT c) b → s = [] ∧ b = [] := by
  intro s b h
  have hflat := h.1
  subst t
  have hlen := congrArg List.length hflat
  simp only [List.length_append] at hlen
  have hslen : s.length = 0 := by omega
  have hblen : b.length = 0 := by omega
  have hs : s = [] := by
    cases s with
    | nil => rfl
    | cons x xs => simp at hslen
  have hb : b = [] := by
    cases b with
    | nil => rfl
    | cons x xs => simp at hblen
  exact ⟨hs, hb⟩

/-- `(t,c)` が marked なら、`t=c` は「全 scb 分解が自明」および
「空の前置部を持つ scb 分解が存在」のそれぞれと同値。 -/
theorem scb_decomposition_triviality {t c : BT} (hm : (t, c) ∈ MarkedB) :
    (t = c ↔ ∀ s b, scb_decomp t s (flatBT c) b → s = [] ∧ b = []) ∧
      (t = c ↔ ∃ b, scb_decomp t [] (flatBT c) b) := by
  rcases hm with ⟨sw, bw, hw⟩
  constructor
  · constructor
    · exact scb_eq_implies_empty
    · intro hall
      rcases hall sw bw hw with ⟨hs, hb⟩
      apply flatBT_injective
      simpa [hs, hb] using hw.1
  · constructor
    · intro htc
      subst t
      refine ⟨[], ?_⟩
      refine ⟨by simp, ?_, by simp⟩
      intro hc
      exact hw.2.1 hc
    · rintro ⟨b, hb⟩
      have hflat : flatBT t = flatBT c ++ b := by
        simpa using hb.1
      have : b = [] := flatBT_append_suffix_nil hflat
      apply flatBT_injective
      simpa [this] using hflat

#print axioms scb_decomposition_triviality

end PSS
