import «7».«7.4-Mark-Trans-repr»

/-!
# §7.4 系（`Trans` の `Mark` と切片による表示）

- 原文: `isabelle/pss_paper.thy` の `p_7_4_Trans_Mark_seg`
- Isabelle: `m_7_4_Trans_Mark_seg`
- 訂正: A46（`RTPS` 上の形）
-/

namespace PSS

/-- Existence part of the common scb position.  Repeatedly remove the final
column until `m` becomes the rightmost column; `Trans_Mark_Pred` transports
the position through each removal. -/
theorem Trans_Mark_seg_exists (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M)
    (hmpos : 0 < m) (hmlt : m < Lng M - 1) :
    ∃ s b,
      scb_decomp (Trans (seg M 0 m)) s
          (flatBT (Dprin (entry M 1 m : ℕ∞) BZero)) b ∧
        scb_decomp (Trans M) s (flatBT (Mark M m)) b := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      have hM : TPS M := RTPS_TPS M hR
      have hlen : 1 < Lng M := by omega
      let P := Pred M
      have hPR : RTPS P := by simpa [P] using RTPS_Pred M hR
      have hPLen : Lng P = Lng M - 1 := by
        simpa [P] using length_Pred M hlen
      have hmP : Marked P m := by
        simpa [P] using Marked_Pred M m hM hlen hm hmlt
      have hmleP : m ≤ Lng P - 1 := by omega
      have hseg : seg P 0 m = seg M 0 m := by
        simpa [P] using seg_Pred_eq M 0 m hlen (Nat.zero_le _) hmlt
      have hentry : entry P 1 m = entry M 1 m := by
        simpa [P] using entry_Pred M 1 m hmlt
      obtain ⟨sb, hsb, _⟩ := Trans_Mark_Pred M m hm hR hmlt
      rcases sb with ⟨s, b⟩
      have hdP : scb_decomp (Trans P) s (flatBT (Mark P m)) b := by
        simpa [P] using hsb.1
      have hdM : scb_decomp (Trans M) s (flatBT (Mark M m)) b := hsb.2
      by_cases hright : m = Lng P - 1
      · have hPgt : 1 < Lng P := by omega
        have hzP : zeroT P = false := by
          simp [zeroT, hPgt.ne']
        have hmark : Mark P m = Dprin (entry P 1 m : ℕ∞) BZero := by
          rw [hright]
          exact Mark_rightmost1_forward P hPR hzP
        have hsegP : seg P 0 m = P := by
          have hmBound : m < Lng P := by omega
          rw [seg_eq_take_drop_adm P 0 m (Nat.zero_le _) hmBound]
          have hmLen : m + 1 = Lng P := by omega
          simp [hmLen]
        have hsegM : seg M 0 m = P := hseg.symm.trans hsegP
        refine ⟨s, b, ?_, hdM⟩
        simpa [hsegM, hentry, hmark] using hdP
      · have hmltP : m < Lng P - 1 := by omega
        have hPLt : Lng P < n := by rw [hPLen, ← hn]; omega
        obtain ⟨s', b', hdSeg', hdP'⟩ :=
          ih (Lng P) hPLt P hmP hPR hmltP rfl
        have hu := scb_unique_decomp_unconditional
          (Trans P) s' s (flatBT (Mark P m)) b' b hdP' hdP
        refine ⟨s, b, ?_, hdM⟩
        simpa [hseg, hentry, hu.1, hu.2] using hdSeg'

/-- Corrected A46 form of the article corollary. -/
theorem Trans_Mark_seg (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M)
    (hmpos : 0 < m) (hmlt : m < Lng M - 1) :
    ∃! sb : List Sym × List Sym,
      scb_decomp (Trans (seg M 0 m)) sb.1
          (flatBT (Dprin (entry M 1 m : ℕ∞) BZero)) sb.2 ∧
        scb_decomp (Trans M) sb.1 (flatBT (Mark M m)) sb.2 := by
  obtain ⟨s, b, hdSeg, hdM⟩ :=
    Trans_Mark_seg_exists M m hm hR hmpos hmlt
  refine ⟨(s, b), ⟨hdSeg, hdM⟩, ?_⟩
  rintro ⟨s', b'⟩ ⟨_, hdM'⟩
  have hu := scb_unique_decomp_unconditional
    (Trans M) s' s (flatBT (Mark M m)) b' b hdM' hdM
  simp [hu.1, hu.2]

theorem m_7_4_Trans_Mark_seg (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M)
    (hmpos : 0 < m) (hmlt : m < Lng M - 1) :
    ∃! sb : List Sym × List Sym,
      scb_decomp (Trans (seg M 0 m)) sb.1
          (flatBT (Dprin (entry M 1 m : ℕ∞) BZero)) sb.2 ∧
        scb_decomp (Trans M) sb.1 (flatBT (Mark M m)) sb.2 :=
  Trans_Mark_seg M m hm hR hmpos hmlt

#print axioms Trans_Mark_seg

end PSS
