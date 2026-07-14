import «5».«5.1-ancestor-tree»
import «6».«6.3-adm-slice»

/-!
# §6.3 命題（基点の切片への遺伝性）

- 原文: `isabelle/pss_paper.thy` の `p_6_3_marked_slice`
- 訂正: なし
- Isabelle: `m_6_3_marked_slice`
- 依存: `5.1-ancestor-tree`, `6.3-adm-slice`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

theorem marked_slice (M : PS) (m s e : ℕ)
    (hmarked : Marked M m) (hsm : s ≤ m) (hme : m ≤ e)
    (he : e ≤ Lng M - 1) :
    Marked (seg M s e) (m - s) := by
  rcases hmarked with ⟨hM, hadmM, hleM⟩
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have heM : e < Lng M := by omega
  have hse : s ≤ e := hsm.trans hme
  let N := seg M s e
  have hNlen : Lng N = e + 1 - s := by simp [N]
  have hNpos : 0 < Lng N := by rw [hNlen]; omega
  have hNT : TPS N := by
    intro heq
    have : Lng N = 0 := by simp [heq]
    omega
  have hadmN : adm N (m - s) = true := by
    have hiff := adm_slice M s m e hM hsm hme he
    exact hiff.mp (Or.inl hadmM)
  have hmeAnc : leR M 0 m e = true :=
    ancestor_tree_1 M m e (Lng M - 1) hM hleM hme he
  have hmN : m - s < Lng N := by rw [hNlen]; omega
  have hlastN : Lng N - 1 < Lng N := by omega
  have hshift := leR0_seg_adm M s e (m - s) (Lng N - 1)
    hse heM hmN hlastN
  have hsidx : s + (m - s) = m := by omega
  have helast : s + (Lng N - 1) = e := by rw [hNlen]; omega
  have hshift' : leR N 0 (m - s) (Lng N - 1) = leR M 0 m e := by
    rw [hsidx, helast] at hshift
    exact hshift
  have hleN : leR N 0 (m - s) (Lng N - 1) = true := by
    rw [hshift']
    exact hmeAnc
  exact ⟨hNT, hadmN, hleN⟩

#print axioms marked_slice

end PSS
