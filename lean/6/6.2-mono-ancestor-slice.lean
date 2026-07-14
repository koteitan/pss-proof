import PSS.Mono
import «5».«5.1-parent-exists»
import «5».«5.1-ancestor-basic»

/-!
# §6.2 命題（単項性の直系先祖による切片への遺伝性）

- 原文: `isabelle/pss_paper.thy` の `p_6_2_mono_ancestor_slice`
- 訂正: なし
- Isabelle: `m_6_2_mono_ancestor_slice`
- 依存: `PSS.Mono`, §5.1 親存在・祖先基本性質
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

@[simp] theorem length_seg (M : PS) (a b : ℕ) :
    Lng (seg M a b) = b + 1 - a := by
  simp [seg]

theorem entry_seg
    (M : PS) (a b i j : ℕ) (hj : j < Lng (seg M a b)) :
    entry (seg M a b) i j = entry M i (a + j) := by
  have hj' : j < b + 1 - a := by simpa using hj
  have haj : a + j < b + 1 := by omega
  unfold seg entry
  simp only [List.getElem?_map]
  rw [List.getElem?_eq_getElem (by simpa using hj')]
  by_cases hi : i = 0 <;> simp [List.getElem_range', entry, hi]

theorem mono_ancestor_slice
    (M : PS) (j₀ j₁ : ℕ) (hM : TPS M)
    (hlt : j₀ < j₁) (hanc : leR M 0 j₀ j₁ = true) :
    monoT (seg M j₀ j₁) = true := by
  let N := seg M j₀ j₁
  have hlen : 1 < Lng N := by simp [N]; omega
  have hN : TPS N := by
    intro hnil
    have : Lng N = 0 := by simp [hnil]
    omega
  have hzero : zeroT N = false := by
    simp [zeroT]
    omega
  have hle : leR N 0 0 (Lng N - 1) = true := by
    apply parent_exists_3 N 0 (Lng N - 1) hN
    · omega
    · omega
    · intro j hj hlast
      have hjN : j < Lng N := by omega
      have hstart : entry N 0 0 = entry M 0 j₀ := by
        have hsegpos : 0 < Lng (seg M j₀ j₁) := by
          simpa [N] using (show 0 < Lng N by omega)
        simpa [N] using entry_seg M j₀ j₁ 0 0 hsegpos
      have hjentry : entry N 0 j = entry M 0 (j₀ + j) :=
        entry_seg M j₀ j₁ 0 j hjN
      have hindex : j₀ + j ≤ j₁ := by
        simp [N] at hlast
        omega
      have hgrowth := ancestor_basic_1 M j₀ (j₀ + j) j₁ hM (by omega) hindex hanc
      simpa [hstart, hjentry] using hgrowth
  change (!zeroT N && leR N 0 0 (Lng N - 1)) = true
  simp [hzero, hle]

#print axioms mono_ancestor_slice

end PSS
