import «6».«6.5-admof-Red-invariance»

/-!
# §6.5 系（`Red` が基点を保つこと）

- 原文: `isabelle/pss_paper.thy` の `p_6_5_Red_marked`
- 訂正: A4（原文の `TPS` 版は偽。`anchoredSlice` 上に制限）
- Isabelle: `m_6_5_Red_marked_final`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-- Corrected A4: a marked anchored slice remains marked after reduction. -/
theorem Red_preserves_marked (M : PS) (m : ℕ)
    (hM : anchoredSlice M) (hm : Marked M m) :
    Marked (Red M) m := by
  rcases hm with ⟨hMT, hadm, hle⟩
  have hL : Lng (Red M) = Lng M := Lng_Red_invariance M hMT
  have hRT : TPS (Red M) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (Red M)
    rw [hL]
    exact List.length_pos_of_ne_nil hMT
  have hadmR : adm (Red M) m = true := by
    rw [← adm_Red_eq M hM]
    exact hadm
  have hleR : leR (Red M) 0 m (Lng M - 1) = true := by
    rw [← Red_le_anchored M hM 0 m (Lng M - 1)]
    exact hle
  exact ⟨hRT, hadmR, by simpa [hL] using hleR⟩

#print axioms Red_preserves_marked

end PSS
