import «7».«7.4-Mark-nextAdm»

/-!
# §7.4 命題（`Mark` の `Trans` による表示）

- 原文: `tmp/content.md` §7.4
- Isabelle: `m_7_4_Mark_Trans_repr`
- 定式化する範囲: 原文の証明が還元する `RTPS` 上の形
-/

namespace PSS

theorem scbContexts_head_exists_of_marked {t c : BT}
    (hc : c ∈ T_B) (hcP : ∃ p, c = .trm [p])
    (hm : (t, c) ∈ MarkedB) :
    ∃ s b, (scbContexts t (flatBT c)).head? = some (s, b) := by
  have hexec := (principal_flat_properties hc hcP).2
  obtain ⟨s₀, b₀, hflat, _hprincipal, htail⟩ := hm
  have htake : (flatBT t).take s₀.length = s₀ := by
    rw [hflat]
    simp
  have hmid : ((flatBT t).drop s₀.length).take (flatBT c).length =
      flatBT c := by
    rw [hflat]
    simp
  have hdrop : (flatBT t).drop (s₀.length + (flatBT c).length) = b₀ := by
    rw [hflat]
    simp
  have hall : b₀.all (fun x => decide (x = .rp)) = true := by
    rw [List.all_eq_true]
    intro x hx
    rw [htail x hx]
    decide
  have hidx : s₀.length < (flatBT t).length - (flatBT c).length + 1 := by
    have hlen := congrArg List.length hflat
    simp only [List.length_append] at hlen
    omega
  have hmem : (s₀, b₀) ∈ scbContexts t (flatBT c) := by
    unfold scbContexts
    rw [List.mem_filterMap]
    refine ⟨s₀.length, by simp [hidx], ?_⟩
    simp [htake, hmid, hdrop, hexec, hall]
  cases hctx : scbContexts t (flatBT c) with
  | nil =>
      rw [hctx] at hmem
      simp at hmem
  | cons x xs =>
      rcases x with ⟨s, b⟩
      exact ⟨s, b, by simp⟩

/-- At the leftmost marked column, `Mark` is the whole translation. -/
theorem Mark_zero_eq_Trans (M : PS) (hR : RTPS M) (h0 : Marked M 0) :
    Mark M 0 = Trans M := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      have hM : TPS M := RTPS_TPS M hR
      have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
      by_cases hOne : Lng M = 1
      · rw [Mark_eq_lengthAux M 0 hR, Trans_eq_lengthAux M hR]
        simp [MarkAux, TransAux, lastIdx, hOne]
      · have hlen : 1 < Lng M := by omega
        have hzero : zeroT M = false := by simp [zeroT, hOne]
        have hmono : monoT M = true := by
          simp [monoT, hzero, h0.2.2]
        have hpredR : RTPS (Pred M) := RTPS_Pred M hR
        have hpredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
        have hpredLt : Lng (Pred M) < n := by rw [hpredLen, ← hn]; omega
        have h0Pred : Marked (Pred M) 0 :=
          Marked_Pred M 0 hM hlen h0 (by omega)
        have hIH : Mark (Pred M) 0 = Trans (Pred M) :=
          ih (Lng (Pred M)) hpredLt (Pred M) hpredR h0Pred rfl
        have heq := Trans_Mark_mono_equations M hR hlen hmono
        rw [heq.1, heq.2 0]
        by_cases ht₁ : Trans (Pred M) = BZero
        · simp [ht₁]
        · have hp : hasParent M 0 (Lng M - 1) = true :=
            mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
          have hcMarked : Marked (Pred M) (Adm M (lastParent M)) := by
            simpa [lastParent, lastIdx] using Marked_Pred_Adm M hM hlen hp
          have hcTB := Mark_mem_T_B (Pred M) (Adm M (lastParent M))
            hpredR hcMarked
          have htc := Trans_Mark_mem_MarkedB (Pred M)
            (Adm M (lastParent M)) hpredR hcMarked
          have hcP := marked_component_principal ht₁ htc
          obtain ⟨s, b, hhead⟩ :=
            scbContexts_head_exists_of_marked hcTB hcP htc
          simp [ht₁, lastIdx, hlen, hIH, replaceScb, hhead]

/-- The representation theorem at its left-end base case. -/
theorem Mark_Trans_repr_zero (M : PS) (hR : RTPS M)
    (h0 : Marked M 0) (hlt : 0 < Lng M - 1) :
    Mark M 0 = Trans (seg M 0 (Lng M - 1)) := by
  have hlen : 1 < Lng M := by omega
  have hseg : seg M 0 (Lng M - 1) = M := by
    rw [seg_eq_take_drop_adm M 0 (Lng M - 1) (Nat.zero_le _) (by omega)]
    have hlast : Lng M - 1 + 1 = Lng M := by omega
    simp [hlast]
  rw [hseg]
  exact Mark_zero_eq_Trans M hR h0

theorem Mark_Trans_repr_multi_step (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M) (hlt : m < Lng M - 1)
    (hmulti : multiT M = true)
    (hrepr :
      Mark (M.drop (Pcut M)) (m - Pcut M) =
        Trans (seg (M.drop (Pcut M)) (m - Pcut M)
          (Lng (M.drop (Pcut M)) - 1))) :
    Mark M m = Trans (seg M m (Lng M - 1)) := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hcut := Pcut_props M hlen
  have hmParts := multi_Marked_last_component M m hM hmulti hm
  have hJne : M.drop (Pcut M) ≠ [(0, 0)] := by
    intro hJ
    have hJL := congrArg Lng hJ
    have hJL' : Lng M - Pcut M = 1 := by simpa using hJL
    omega
  have hMark : Mark M m = Mark (M.drop (Pcut M)) (m - Pcut M) := by
    have heq := Trans_Mark_multi_equations M hR hmulti
    simpa [hJne] using heq.2 m
  have hmLocal : m - Pcut M < Lng (M.drop (Pcut M)) := by
    rw [show Lng (M.drop (Pcut M)) = Lng M - Pcut M by simp]
    omega
  have hseg :
      seg (M.drop (Pcut M)) (m - Pcut M)
          (Lng (M.drop (Pcut M)) - 1) =
        seg M m (Lng M - 1) := by
    rw [← drop_eq_seg (M.drop (Pcut M)) (m - Pcut M) hmLocal,
      ← drop_eq_seg M m (by omega)]
    simp [List.drop_drop, Nat.add_sub_of_le hmParts.1]
  rw [hMark, ← hseg]
  exact hrepr

#print axioms Mark_zero_eq_Trans
#print axioms Mark_Trans_repr_multi_step

end PSS
