import PSS.Defs
import «5».«5.1-parent-exists»

/-!
# §5.1 命題（親の基本性質）

- 原文: `isabelle/pss_paper.thy` の `p_5_1_parent_basic_1`, `_2`
- 訂正: なし
- Isabelle: `m_5_1_parent_basic_1`, `_2`
- 依存: `PSS.Defs`, `5.1-parent-exists`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

theorem parent_basic_1
    (M : PS) (j₀ j j₁ : ℕ)
    (hM : TPS M) (hj₀j : j₀ < j) (hjj₁ : j ≤ j₁)
    (hnext : nextR M 0 j₀ j₁ = true) :
    entry M 0 j₁ ≤ entry M 0 j := by
  have hn : nextrel0 M j₀ j₁ = true := by simpa [nextR] using hnext
  by_cases heq : j = j₁
  · subst j
    exact le_refl _
  · have hjlt : j < j₁ := lt_of_le_of_ne hjj₁ heq
    have hh := hn
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] at hh
    have hc := hh.2 j (List.mem_range.mpr hjlt)
    simpa [hj₀j] using hc

theorem parent_basic_2
    (M : PS) (j₀ j j₁ : ℕ)
    (hM : TPS M) (hj₀j : j₀ < j) (hjj₁ : j ≤ j₁)
    (hnext : nextR M 1 j₀ j₁ = true)
    (hanc : leR M 0 j j₁ = true) :
    entry M 1 j₁ ≤ entry M 1 j := by
  have hn : nextrel1 M j₀ j₁ = true := by simpa [nextR] using hnext
  have hj₁bound : j₁ < Lng M := by
    have hh := hn
    simp [nextrel1] at hh
    omega
  have hjbound : j < Lng M := lt_of_le_of_lt hjj₁ hj₁bound
  have hjanc : le0 M j j₁ = true := by simpa [leR] using hanc
  have hh := hn
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hh
  have hc := hh.2 j (List.mem_range.mpr hjbound)
  simpa [hj₀j, hjanc] using hc

#print axioms parent_basic_1
#print axioms parent_basic_2

end PSS
