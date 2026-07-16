import «6».«6.7-standard-reduced»

/-!
# §6.5 系（直系先祖の `Red` 不変性）

- 原文: `isabelle/pss_paper.thy` の `p_6_5_Red_le`
- 訂正: A4（原文の `TPS` 版は偽。`anchoredSlice` 上に制限）
- Isabelle: `m_6_5_Red_le_final`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-- Every corrected-A4 anchored slice satisfies coefficient condition (A). -/
theorem anchoredSlice_RedCondA (M : PS) (hM : anchoredSlice M) :
    RedCondA M = true := by
  rcases hM with ⟨S, a, b, hsource, hab, hbL, hanc, rfl⟩
  have hR : RTPS S := by
    rcases hsource with hST | hR
    · exact STPS_RTPS S hST
    · exact hR.1
  exact RedCondA_seg S a b hab hbL (RTPS_condAB S hR).1

/-- Corrected A4: reduction preserves both ancestor relations on anchored
slices of standard or reduced-mono pair sequences. -/
theorem Red_le_anchored (M : PS) (hM : anchoredSlice M)
    (i j₀ j₁ : ℕ) :
    leR M i j₀ j₁ = leR (Red M) i j₀ j₁ := by
  exact Red_le_anchored_of_condA M hM (anchoredSlice_RedCondA M hM) i j₀ j₁

#print axioms anchoredSlice_RedCondA
#print axioms Red_le_anchored

end PSS
