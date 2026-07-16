import «6».«6.5-Red-le-invariance»

/-!
# §6.5 命題（`Red` が許容性を保つこと）

- 原文: `isabelle/pss_paper.thy` の `p_6_5_Red_adm`
- 訂正: A4（原文の `TPS` 版は偽。`anchoredSlice` 上に制限）
- Isabelle: `m_6_5_Red_adm_final`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem anchoredSlice_row0_floor_ra (M : PS)
    (hM : anchoredSlice M) :
    ∀ j < Lng M, entry M 0 0 ≤ entry M 0 j := by
  rcases anchoredSlice_zero_or_mono M hM with hz | hmono
  · have hL : Lng M = 1 := by
      have hh := hz
      simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
      exact hh.1
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    exact le_rfl
  · exact mono_row0_min_mr M (anchoredSlice_TPS M hM) hmono

/-- Reduction preserves the complete admissibility predicate on corrected-A4
anchored slices. -/
theorem adm_Red_eq (M : PS) (hM : anchoredSlice M) :
    adm M = adm (Red M) := by
  have hMT : TPS M := anchoredSlice_TPS M hM
  have hred : Red M =
      rebaseRow0 (entry M 0 0) (entry M 1 0) M :=
    Red_rebase_nonmulti M hMT (anchoredSlice_RedCondA M hM)
      (anchoredSlice_nonmulti M hM)
  have hnext : nextR (Red M) = nextR M := by
    rw [hred]
    exact nextR_rebaseRow0 (entry M 0 0) (entry M 1 0) M
      (anchoredSlice_row0_floor_ra M hM)
  have hL : Lng (Red M) = Lng M := Lng_Red_invariance M hMT
  funext j
  simp [adm, nadm, hL, hnext]

/-- Corrected A4: the admissible index sets of `M` and `Red M` coincide. -/
theorem Red_preserves_AdmSet (M : PS) (hM : anchoredSlice M) :
    AdmSet M = AdmSet (Red M) := by
  ext j
  simp [AdmSet, adm_Red_eq M hM]

#print axioms adm_Red_eq
#print axioms Red_preserves_AdmSet

end PSS
