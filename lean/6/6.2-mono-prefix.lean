import PSS.Mono
import «5».«5.1-ancestor-tree»
import «6».«6.2-mono-ancestor-slice»

/-!
# §6.2 系（単項性の始切片への遺伝性）

- 原文: `isabelle/pss_paper.thy` の `p_6_2_mono_prefix`
- 訂正: なし
- Isabelle: `m_6_2_mono_prefix`
- 依存: `5.1-ancestor-tree`, `6.2-mono-ancestor-slice`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

theorem mono_prefix
    (M : PS) (j₀ : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hj₀pos : 0 < j₀) (hj₀bound : j₀ < Lng M) :
    monoT (seg M 0 j₀) = true := by
  have hfull : leR M 0 0 (Lng M - 1) = true := by
    have hm := hmono
    simp [monoT] at hm
    exact hm.2
  have hj₀last : j₀ ≤ Lng M - 1 := by omega
  have hprefix := ancestor_tree_1 M 0 j₀ (Lng M - 1) hM hfull
    (Nat.zero_le _) hj₀last
  exact mono_ancestor_slice M 0 j₀ hM hj₀pos hprefix

#print axioms mono_prefix

end PSS
