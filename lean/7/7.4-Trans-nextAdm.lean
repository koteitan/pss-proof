import «7».«7.4-Trans-Mark-Pred»

/-!
# §7.4 命題（`Trans` と許容的親子関係の関係）

- 原文: `tmp/content.md` §7.4
- 訂正: A45（定義域を `TPS` から `RTPS` へ制限）
- Isabelle: `m_7_4_Trans_nextAdm`
-/

namespace PSS

/-- Corrected A45 form.  The unique admissible parent of the last column is a
marked proper ancestor, so this is the corresponding instance of
`Trans_Mark_Pred`. -/
theorem Trans_nextAdm (M : PS) (hR : RTPS M)
    (huniq : ∃! j₀, nextAdm M 0 j₀ (Lng M - 1) = true) :
    let j₀ := Classical.choose huniq.exists
    ∃! sb : List Sym × List Sym,
      scb_decomp (Trans (Pred M)) sb.1 (flatBT (Mark (Pred M) j₀)) sb.2 ∧
      scb_decomp (Trans M) sb.1 (flatBT (Mark M j₀)) sb.2 := by
  let j₀ := Classical.choose huniq.exists
  have hna : nextAdm M 0 j₀ (Lng M - 1) = true :=
    Classical.choose_spec huniq.exists
  have hh := hna
  simp only [nextAdm, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.or_eq_true] at hh
  have hm : Marked M j₀ :=
    ⟨RTPS_TPS M hR, hh.1.2, hh.1.1.1⟩
  exact Trans_Mark_Pred M j₀ hm hR hh.1.1.2

theorem m_7_4_Trans_nextAdm (M : PS) (hR : RTPS M)
    (huniq : ∃! j₀, nextAdm M 0 j₀ (Lng M - 1) = true) :
    let j₀ := Classical.choose huniq.exists
    ∃! sb : List Sym × List Sym,
      scb_decomp (Trans (Pred M)) sb.1 (flatBT (Mark (Pred M) j₀)) sb.2 ∧
      scb_decomp (Trans M) sb.1 (flatBT (Mark M j₀)) sb.2 :=
  Trans_nextAdm M hR huniq

private theorem bad45_values :
    let M : PS := [(0, 0), (0, 1), (1, 2), (1, 0)]
    (Trans (Pred M) == Dprin 0 (Dprin 2 BZero)) = true ∧
    (Mark (Pred M) 1 == Dprin 2 BZero) = true ∧
    (Trans M == Dprin 0
      (addBT (Dprin 2 BZero)
        (Dprin 1 (addBT (Dprin 2 BZero) (Dprin 0 BZero))))) = true ∧
    (Mark M 1 == Dprin 0 BZero) = true := by
  decide

/-- Executable/formal witness for A45: the article's original `TPS` domain is
too broad.  Its unique `nextAdm` parent is column `1`, but no shared scb
context exists there. -/
theorem Trans_nextAdm_original_counterexample :
    let M : PS := [(0, 0), (0, 1), (1, 2), (1, 0)]
    TPS M ∧
    (∃! j₀, nextAdm M 0 j₀ (Lng M - 1) = true) ∧
    ¬∃ sb : List Sym × List Sym,
      scb_decomp (Trans (Pred M)) sb.1 (flatBT (Mark (Pred M) 1)) sb.2 ∧
      scb_decomp (Trans M) sb.1 (flatBT (Mark M 1)) sb.2 := by
  dsimp only
  have hTPS : TPS [(0, 0), (0, 1), (1, 2), (1, 0)] := by simp [TPS]
  have huniq : ∃! j₀,
      nextAdm [(0, 0), (0, 1), (1, 2), (1, 0)] 0 j₀
        (Lng [(0, 0), (0, 1), (1, 2), (1, 0)] - 1) = true := by
    refine ⟨1, by decide, ?_⟩
    intro y hy
    have hyle : y < 4 := by
      have hh := hy
      simp only [nextAdm, Bool.and_eq_true, decide_eq_true_eq] at hh
      have := le0_index_fseq (by simpa [leR] using hh.1.1.1)
      omega
    interval_cases y
    all_goals first | rfl | (exfalso; revert hy; decide)
  refine ⟨hTPS, huniq, ?_⟩
  rintro ⟨⟨s, b⟩, hdPred, hdM⟩
  have hvb := bad45_values
  dsimp only at hvb
  have hvPred :
      Trans (Pred [(0, 0), (0, 1), (1, 2), (1, 0)]) =
        Dprin 0 (Dprin 2 BZero) := eq_of_beq hvb.1
  have hkPred :
      Mark (Pred [(0, 0), (0, 1), (1, 2), (1, 0)]) 1 =
        Dprin 2 BZero := eq_of_beq hvb.2.1
  have hvM : Trans [(0, 0), (0, 1), (1, 2), (1, 0)] = Dprin 0
      (addBT (Dprin 2 BZero)
        (Dprin 1 (addBT (Dprin 2 BZero) (Dprin 0 BZero)))) :=
    eq_of_beq hvb.2.2.1
  have hkM : Mark [(0, 0), (0, 1), (1, 2), (1, 0)] 1 =
      Dprin 0 BZero := eq_of_beq hvb.2.2.2
  have hzeroTB : BZero ∈ T_B := by
    simp [T_B, BZero, dfree_BT, dfree_BPList]
  have hD2TB : Dprin 2 BZero ∈ T_B :=
    Dprin_mem_T_B (by simp) hzeroTB
  have hD2P : ∃ p, Dprin 2 BZero = .trm [p] := ⟨_, rfl⟩
  have hD2ptb : isPTB_str (flatBT (Dprin 2 BZero)) :=
    (principal_flat_properties hD2TB hD2P).1
  have hknown : scb_decomp (Dprin 0 (Dprin 2 BZero))
      [.dsym 0] (flatBT (Dprin 2 BZero)) [] := by
    refine ⟨?_, ?_, by simp⟩
    · simp [Dprin, flatBT, flatBP]
    · intro _
      exact hD2ptb
  have hpin := scb_unique_decomp_unconditional
    (Dprin 0 (Dprin 2 BZero)) s [.dsym 0]
      (flatBT (Dprin 2 BZero)) b []
      (by simpa [hvPred, hkPred] using hdPred) hknown
  have hs : s = [.dsym 0] := hpin.1
  have hb : b = [] := hpin.2
  rcases hdM with ⟨hflat, _, _⟩
  rw [hs, hb, hvM, hkM] at hflat
  simp [Dprin, BZero, addBT, flatBT, flatBP, flatBPTail] at hflat

#print axioms Trans_nextAdm
#print axioms Trans_nextAdm_original_counterexample

end PSS
