import «7».«7.4-Trans-nextAdm»

/-!
# §7.4 命題（`Mark` と許容的親子関係の関係）

- 原文: `tmp/content.md` §7.4
- 訂正: A18（祖先列 `j` は `Marked`）および A47（定義域を `RTPS`
  へ制限）
- Isabelle: `Mark_nest_common_marked`, `m_7_4_Mark_nextAdm`
-/

namespace PSS

private theorem Mark_self_scb_74 (N : PS) (k : ℕ)
    (hR : RTPS N) (hk : Marked N k) :
    scb_decomp (Mark N k) [] (flatBT (Mark N k)) [] := by
  refine ⟨by simp, ?_, by simp⟩
  intro hkne
  have hTransNe : Trans N ≠ BZero := by
    intro hzero
    have hz : zeroT N = true :=
      (Trans_preserves_zeroT N (RTPS_TPS N hR)).2 hzero
    have hNeq : N = [(0, 0)] := by
      rw [← RTPS_Red_eq N hR]
      exact Red_zero_mr N hz
    subst N
    have hmark : Mark [(0, 0)] k = BZero := by
      rw [Mark_eq_lengthAux [(0, 0)] k hR]
      have hred : reduced [(0, 0)] = true := hR
      simp [MarkAux, lastIdx, BZero, hred]
    exact hkne hmark
  have hp : ∃ p, Mark N k = .trm [p] :=
    marked_component_principal hTransNe
      (Trans_Mark_mem_MarkedB N k hR hk)
  exact (principal_flat_properties (Mark_mem_T_B N k hR hk) hp).1

/-- If `m ≤ m'` are marked columns strictly before the final column of a
reduced pair sequence, the occurrence of `Mark _ m'` inside `Mark _ m` has
the same scb position before and after deleting the final column. -/
theorem Mark_nest_common_marked (M : PS) (m m' : ℕ)
    (hR : RTPS M) (hm : Marked M m) (hm' : Marked M m')
    (hmm' : m ≤ m') (hm'lt : m' < Lng M - 1) :
    ∃! sb : List Sym × List Sym,
      scb_decomp (Mark (Pred M) m) sb.1
        (flatBT (Mark (Pred M) m')) sb.2 ∧
      scb_decomp (Mark M m) sb.1 (flatBT (Mark M m')) sb.2 := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hmlt : m < Lng M - 1 := hmm'.trans_lt hm'lt
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hmPred : Marked (Pred M) m :=
    Marked_Pred M m hM hlen hm hmlt
  have hm'Pred : Marked (Pred M) m' :=
    Marked_Pred M m' hM hlen hm' hm'lt
  by_cases heq : m = m'
  · subst m'
    have hdPred := Mark_self_scb_74 (Pred M) m hpredR hmPred
    have hdM := Mark_self_scb_74 M m hR hm
    refine ⟨([], []), ⟨hdPred, hdM⟩, ?_⟩
    rintro ⟨s, b⟩ ⟨hcand, _⟩
    have hu := scb_unique_decomp_unconditional
      (Mark (Pred M) m) s [] (flatBT (Mark (Pred M) m)) b []
      hcand hdPred
    simpa using hu
  · have hmmlt : m < m' := lt_of_le_of_ne hmm' heq
    obtain ⟨⟨sm, bm⟩, ⟨hPm, hMm⟩, _⟩ :=
      Trans_Mark_Pred M m hm hR hmlt
    obtain ⟨⟨sm', bm'⟩, ⟨hPm', hMm'⟩, _⟩ :=
      Trans_Mark_Pred M m' hm' hR hm'lt
    obtain ⟨sP, bP, hdP⟩ :=
      Mark_MarkedB_nest (Pred M) m m' hmPred hm'Pred hmm' hpredR
    obtain ⟨sM, bM, hdM⟩ :=
      Mark_MarkedB_nest M m m' hm hm' hmm' hR
    have hPredTransNe : Trans (Pred M) ≠ BZero := by
      intro hzero
      have hz : zeroT (Pred M) = true :=
        (Trans_preserves_zeroT (Pred M) (RTPS_TPS (Pred M) hpredR)).2 hzero
      have hPredOne : Lng (Pred M) = 1 := by
        simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
        exact hz.1
      have hPredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
      omega
    have hMTransNe : Trans M ≠ BZero := by
      intro hzero
      have hz : zeroT M = true :=
        (Trans_preserves_zeroT M hM).2 hzero
      simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
      omega
    have hpPred : ∃ p, Mark (Pred M) m = .trm [p] :=
      marked_component_principal hPredTransNe
        (Trans_Mark_mem_MarkedB (Pred M) m hpredR hmPred)
    have hpM : ∃ p, Mark M m = .trm [p] :=
      marked_component_principal hMTransNe
        (Trans_Mark_mem_MarkedB M m hR hm)
    have hcompP : scb_decomp (Trans (Pred M)) (sm ++ sP)
        (flatBT (Mark (Pred M) m')) (bP ++ bm) :=
      scb_compose (Trans (Pred M)) (Mark (Pred M) m)
        sm sP (flatBT (Mark (Pred M) m')) bP bm hpPred hPm hdP
    have hcompM : scb_decomp (Trans M) (sm ++ sM)
        (flatBT (Mark M m')) (bM ++ bm) :=
      scb_compose (Trans M) (Mark M m)
        sm sM (flatBT (Mark M m')) bM bm hpM hMm hdM
    have hcohP := scb_unique_decomp_unconditional
      (Trans (Pred M)) (sm ++ sP) sm'
        (flatBT (Mark (Pred M) m')) (bP ++ bm) bm' hcompP hPm'
    have hcohM := scb_unique_decomp_unconditional
      (Trans M) (sm ++ sM) sm'
        (flatBT (Mark M m')) (bM ++ bm) bm' hcompM hMm'
    have hs : sP = sM := by
      simpa using hcohP.1.trans hcohM.1.symm
    have hb : bP = bM := by
      exact List.append_cancel_right (hcohP.2.trans hcohM.2.symm)
    have hdM' : scb_decomp (Mark M m) sP
        (flatBT (Mark M m')) bP := by simpa [hs, hb] using hdM
    refine ⟨(sP, bP), ⟨hdP, hdM'⟩, ?_⟩
    rintro ⟨s, b⟩ ⟨hcand, _⟩
    have hu := scb_unique_decomp_unconditional
      (Mark (Pred M) m) s sP (flatBT (Mark (Pred M) m')) b bP
      hcand hdP
    simpa using hu

/-- Corrected A18+A47 form of the article proposition. -/
theorem Mark_nextAdm (M : PS) (j : ℕ) (hR : RTPS M)
    (huniq : ∃! j₀, nextAdm M 0 j₀ (Lng M - 1) = true)
    (hj : Marked M j)
    (hjle : leR M 0 j (Classical.choose huniq.exists) = true) :
    let j₀ := Classical.choose huniq.exists
    ∃! sb : List Sym × List Sym,
      scb_decomp (Mark (Pred M) j) sb.1
        (flatBT (Mark (Pred M) j₀)) sb.2 ∧
      scb_decomp (Mark M j) sb.1 (flatBT (Mark M j₀)) sb.2 := by
  let j₀ := Classical.choose huniq.exists
  have hna : nextAdm M 0 j₀ (Lng M - 1) = true :=
    Classical.choose_spec huniq.exists
  have hh := hna
  simp only [nextAdm, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.or_eq_true] at hh
  have hj₀ : Marked M j₀ :=
    ⟨RTPS_TPS M hR, hh.1.2, hh.1.1.1⟩
  have hjj₀ : j ≤ j₀ :=
    le0_index_fseq (by simpa [j₀, leR] using hjle)
  exact Mark_nest_common_marked M j j₀ hR hj hj₀ hjj₀ hh.1.1.2

theorem m_7_4_Mark_nextAdm (M : PS) (j : ℕ) (hR : RTPS M)
    (huniq : ∃! j₀, nextAdm M 0 j₀ (Lng M - 1) = true)
    (hj : Marked M j)
    (hjle : leR M 0 j (Classical.choose huniq.exists) = true) :
    let j₀ := Classical.choose huniq.exists
    ∃! sb : List Sym × List Sym,
      scb_decomp (Mark (Pred M) j) sb.1
        (flatBT (Mark (Pred M) j₀)) sb.2 ∧
      scb_decomp (Mark M j) sb.1 (flatBT (Mark M j₀)) sb.2 :=
  Mark_nextAdm M j hR huniq hj hjle

/-- Executable/formal witness for A18: row-0 ancestry alone does not make the
outer column admissible, hence it does not put the argument in `Marked`. -/
theorem Mark_nextAdm_missing_marked_counterexample :
    let M : PS := [(0, 0), (1, 1), (2, 2), (3, 1)]
    RTPS M ∧
    (∃! j₀, nextAdm M 0 j₀ (Lng M - 1) = true) ∧
    leR M 0 1 2 = true ∧
    ¬Marked M 1 := by
  dsimp only
  have hR : RTPS [(0, 0), (1, 1), (2, 2), (3, 1)] := by decide
  have huniq : ∃! j₀,
      nextAdm [(0, 0), (1, 1), (2, 2), (3, 1)] 0 j₀
        (Lng [(0, 0), (1, 1), (2, 2), (3, 1)] - 1) = true := by
    refine ⟨2, by decide, ?_⟩
    intro y hy
    have hylt : y < 4 := by
      have hh := hy
      simp only [nextAdm, Bool.and_eq_true, decide_eq_true_eq] at hh
      have := le0_index_fseq (by simpa [leR] using hh.1.1.1)
      omega
    interval_cases y
    all_goals first | rfl | (exfalso; revert hy; decide)
  exact ⟨hR, huniq, by decide, by decide⟩

private theorem bad47_values :
    let M : PS := [(0, 0), (4, 2), (2, 6), (4, 2), (8, 4), (6, 4)]
    (Mark (Pred M) 3 == Dprin 3 BZero) = true ∧
    (Mark M 3 == Dprin 3 BZero) = true ∧
    (Mark (Pred M) 0 ==
      Dprin 0 (addBT (Dprin 1 BZero) (Dprin 1 (Dprin 3 BZero)))) = true ∧
    (Mark M 0 ==
      Dprin 0 (addBT (Dprin 1 BZero)
        (Dprin 1 (addBT (Dprin 3 BZero) (Dprin 3 BZero))))) = true := by
  decide

/-- Executable/formal witness for A47: even after adding A18's `Marked`
hypothesis, the article's original `TPS` domain is too broad. -/
theorem Mark_nextAdm_original_counterexample :
    let M : PS := [(0, 0), (4, 2), (2, 6), (4, 2), (8, 4), (6, 4)]
    TPS M ∧
    (∃! j₀, nextAdm M 0 j₀ (Lng M - 1) = true) ∧
    Marked M 0 ∧ leR M 0 0 3 = true ∧
    ¬∃ sb : List Sym × List Sym,
      scb_decomp (Mark (Pred M) 0) sb.1
        (flatBT (Mark (Pred M) 3)) sb.2 ∧
      scb_decomp (Mark M 0) sb.1 (flatBT (Mark M 3)) sb.2 := by
  dsimp only
  let M : PS := [(0, 0), (4, 2), (2, 6), (4, 2), (8, 4), (6, 4)]
  have hTPS : TPS M := by simp [M, TPS]
  have huniq : ∃! j₀, nextAdm M 0 j₀ (Lng M - 1) = true := by
    refine ⟨3, by decide, ?_⟩
    intro y hy
    have hylt : y < 6 := by
      have hh := hy
      simp only [nextAdm, Bool.and_eq_true, decide_eq_true_eq] at hh
      have h : y < 5 := by simpa [M] using hh.1.1.2
      omega
    interval_cases y
    all_goals first | rfl | (exfalso; revert hy; decide)
  have hmarked : Marked M 0 := by decide
  have hle : leR M 0 0 3 = true := by decide
  refine ⟨hTPS, huniq, hmarked, hle, ?_⟩
  rintro ⟨⟨s, b⟩, hdPred, hdM⟩
  have hv := bad47_values
  dsimp only at hv
  have hcPred : Mark (Pred M) 3 = Dprin 3 BZero := eq_of_beq hv.1
  have hcM : Mark M 3 = Dprin 3 BZero := eq_of_beq hv.2.1
  have hoPred : Mark (Pred M) 0 =
      Dprin 0 (addBT (Dprin 1 BZero) (Dprin 1 (Dprin 3 BZero))) :=
    eq_of_beq hv.2.2.1
  have hoM : Mark M 0 =
      Dprin 0 (addBT (Dprin 1 BZero)
        (Dprin 1 (addBT (Dprin 3 BZero) (Dprin 3 BZero)))) :=
    eq_of_beq hv.2.2.2
  have hflat : flatBT (Mark (Pred M) 0) = flatBT (Mark M 0) := by
    calc
      flatBT (Mark (Pred M) 0) =
          s ++ flatBT (Mark (Pred M) 3) ++ b := hdPred.1
      _ = s ++ flatBT (Mark M 3) ++ b := by rw [hcPred, hcM]
      _ = flatBT (Mark M 0) := hdM.1.symm
  have hout := flatBT_injective hflat
  rw [hoPred, hoM] at hout
  simp [Dprin, addBT, BZero] at hout

#print axioms Mark_nest_common_marked
#print axioms Mark_nextAdm
#print axioms Mark_nextAdm_missing_marked_counterexample
#print axioms Mark_nextAdm_original_counterexample

end PSS
