import PSS.Mono
import «5».«5.1-parent-exists»
import «5».«5.1-ancestor-basic»

/-!
# §6.2 命題（複項性の判定条件）

- 原文: `isabelle/pss_paper.thy` の `p_6_2_multi_crit_12`, `_23`
- 訂正: なし
- Isabelle: `m_6_2_multi_crit_12`, `_23`
- 依存: `PSS.Mono`, §5.1 親存在・祖先基本性質
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem not_multi_iff_le (M : PS) (hM : TPS M) :
    multiT M = false ↔ leR M 0 0 (Lng M - 1) = true := by
  cases hz : zeroT M
  · simp [multiT, monoT, hz]
  · have hlen : Lng M = 1 := by
      have hh := hz
      simp [zeroT] at hh
      exact hh.1
    have hle : leR M 0 0 (Lng M - 1) = true := by
      simp [hlen, leR, le0, le0Aux]
    simp [multiT, hz, hle]

theorem multi_criterion_23 (M : PS) (hM : TPS M) :
    (∀ j, 0 < j → j < Lng M → entry M 0 0 < entry M 0 j) ↔
      leR M 0 0 (Lng M - 1) = true := by
  constructor
  · intro h
    by_cases hlen : Lng M = 1
    · simp [hlen, leR, le0, le0Aux]
    · have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
      have hgt : 1 < Lng M := by omega
      apply parent_exists_3 M 0 (Lng M - 1) hM
      · omega
      · omega
      · intro j hj hlast
        apply h j hj
        omega
  · intro hle j hj hjL
    apply ancestor_basic_1 M 0 j (Lng M - 1) hM hj
    · omega
    · exact hle

theorem multi_criterion_12 (M : PS) (hM : TPS M) :
    multiT M = false ↔
      ∀ j, 0 < j → j < Lng M → entry M 0 0 < entry M 0 j := by
  rw [not_multi_iff_le M hM]
  exact (multi_criterion_23 M hM).symm

#print axioms multi_criterion_12
#print axioms multi_criterion_23

end PSS
