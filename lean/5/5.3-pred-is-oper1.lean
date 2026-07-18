import PSS.Defs

/-!
# §5.3 命題（`Pred` が `[1]` で表されること）

- 原文: `isabelle/pss_paper.thy` の `p_5_3_pred_is_oper1`
- 訂正: A40 は原文の付随する型主張に適用（本等式は訂正なし）
- Isabelle: `m_5_3_pred_is_oper1`
- 依存: `PSS.Defs`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem map_entry_range_eq
    (M : PS) (a n : ℕ) (hbound : a + n ≤ Lng M) :
    (List.range' a n).map (fun j => (entry M 0 j, entry M 1 j)) =
      (M.drop a).take n := by
  apply List.ext_getElem
  · have hnle : n ≤ M.length - a :=
      Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hbound)
    simp [hnle]
  · intro k hk₁ hk₂
    have hklt : k < n := by simpa using hk₁
    have hak : a + k < Lng M := by omega
    have hget := List.getElem?_eq_getElem (l := M) hak
    simp only [List.getElem_map, List.getElem_range', List.getElem_take,
      List.getElem_drop]
    simp [entry, hget]

private theorem hasParent_next
    (M : PS) (i j₁ : ℕ) (h : hasParent M i j₁ = true) :
    nextR M i (parent M i j₁) j₁ = true := by
  have hlen : (parents M i j₁).length = 1 := by
    simpa [hasParent] using h
  obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp hlen
  have hpMem : p ∈ parents M i j₁ := by simp [hp]
  have hpNext : nextR M i p j₁ = true := by
    simpa [parents] using (List.mem_filter.mp hpMem).2
  have hparent : parent M i j₁ = p := by simp [parent, hp]
  simpa [hparent] using hpNext

theorem hasParent_parent_lt
    (M : PS) (i j₁ : ℕ) (h : hasParent M i j₁ = true) :
    parent M i j₁ < j₁ := by
  have hn := hasParent_next M i j₁ h
  unfold nextR at hn
  split at hn <;> simp [nextrel0, nextrel1] at hn <;> omega

theorem pred_is_oper1
    (M : PS) (hM : TPS M) (hlen : 1 < Lng M) :
    Pred M = oper M 1 := by
  let j₁ := Lng M - 1
  have hj₁pos : 0 < j₁ := by omega
  have hj₁ne : j₁ ≠ 0 := Nat.ne_of_gt hj₁pos
  have hj₁bound : j₁ ≤ Lng M := by omega
  have hpred : Pred M = M.take j₁ := by
    simp [Pred, Nat.not_le_of_lt hlen, List.dropLast_eq_take, j₁]
  by_cases hzero :
      (decide (entry M 0 j₁ = 0) && decide (entry M 1 j₁ = 0)) = true
  · simp [oper, j₁, hj₁ne, hzero, hpred]
  · let i₁ := idx1 M j₁
    by_cases hnoParent : (!hasParent M i₁ j₁) = true
    · simp [oper, j₁, hj₁ne, hzero, i₁, hnoParent, hpred]
    · have hhasParent : hasParent M i₁ j₁ = true := by
        cases hp : hasParent M i₁ j₁
        · simp [hp] at hnoParent
        · simp [hp]
      let j₀ := parent M i₁ j₁
      have hj₀lt : j₀ < j₁ := hasParent_parent_lt M i₁ j₁ hhasParent
      have hj₀le : j₀ ≤ j₁ := Nat.le_of_lt hj₀lt
      have hrange := map_entry_range_eq M j₀ (j₁ - j₀) (by omega)
      have htake : M.take j₀ ++ (M.drop j₀).take (j₁ - j₀) = M.take j₁ := by
        rw [← List.take_add]
        congr 1
        omega
      rw [hpred]
      simp [oper, j₁, hj₁ne, hzero, i₁, hnoParent, j₀]
      rw [hrange, htake]

#print axioms pred_is_oper1

end PSS
