import «7».«7.4-Mark-nextAdm»
import «7».«7.3-two-column»
import «6».«6.6-ancestor-slice-Red-IncrFirst»

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

/-- At the last proper marked column, the terminal slice has two columns and
its translation has the corresponding closed form. -/
theorem Trans_terminal_slice_two_column (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M)
    (hmLast : m = Lng M - 2) (hlen : 1 < Lng M - 1) :
    Trans (seg M m (Lng M - 1)) =
      Dprin (entry M 1 m : ℕ∞)
        (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero) := by
  let j₁ := Lng M - 1
  let S := seg M m j₁
  let N := Red S
  have hlt : m < j₁ := by simp [j₁, hmLast]; omega
  have hanc : leR M 0 m j₁ = true := by simpa [j₁] using hm.2.2
  have hfacts := ancestor_slice_Red_IncrFirst M m j₁ hR hlt
    (by simp [j₁]) hanc
  have hredN : Red N = N := by simpa [S, N] using hfacts.1
  have hmonoN : monoT N = true := by simpa [S, N] using hfacts.2.1
  have hread : S = IncrFirstN (entry M 0 m - entry M 1 m) N := by
    simpa [S, N] using hfacts.2.2
  have hSlen : Lng S = 2 := by simp [S, j₁, hmLast]; omega
  have hNlen : Lng N = 2 := by
    have hlenEq := congrArg Lng hread
    simpa using hlenEq.symm.trans hSlen
  have hST : TPS S := by
    intro hnil
    have : Lng S = 0 := by simp [hnil]
    omega
  have hSnm : multiT S = false := by
    have hmonoS : monoT S = true := by
      simpa [S] using mono_ancestor_slice M m j₁ hm.1 hlt hanc
    simp [multiT, hmonoS]
  have hNR : RTPS N := by
    simpa [N] using Red_nonmulti_RTPS S hST hSnm
  have htransN := two_column_Trans N hNR hmonoN hNlen
  have he0 : entry N 1 0 = entry M 1 m := by
    have hSN : entry S 1 0 = entry N 1 0 := by
      rw [hread, entry_IncrFirstN_one]
    have hidx : 0 < Lng (seg M m j₁) := by
      simpa [S] using (show 0 < Lng S by omega)
    have hSM : entry S 1 0 = entry M 1 m := by
      simpa [S] using entry_seg M m j₁ 1 0 hidx
    omega
  have he1 : entry N 1 1 = entry M 1 j₁ := by
    have hSN : entry S 1 1 = entry N 1 1 := by
      rw [hread, entry_IncrFirstN_one]
    have hmSucc : m + 1 = j₁ := by simp [j₁, hmLast]; omega
    have hidx : 1 < Lng (seg M m j₁) := by
      simpa [S] using (show 1 < Lng S by omega)
    have hSM : entry S 1 1 = entry M 1 j₁ := by
      simpa [S, hmSucc] using entry_seg M m j₁ 1 1 hidx
    omega
  have htrans : Trans S = Trans N := by
    simpa [N] using Trans_Red S hST
  simpa [S, j₁, he0, he1] using htrans.trans htransN

/-- At the boundary, the predecessor mark is its rightmost principal term. -/
theorem Mark_Pred_terminal_boundary (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M)
    (hmLast : m = Lng M - 2) (hlen : 1 < Lng M - 1) :
    Mark (Pred M) m = Dprin (entry M 1 m : ℕ∞) BZero := by
  have hM : TPS M := RTPS_TPS M hR
  have hlenM : 1 < Lng M := by omega
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hlenM
  have hmlt : m < Lng M - 1 := by omega
  have hmPred : Marked (Pred M) m :=
    Marked_Pred M m hM hlenM hm hmlt
  have hmRight : m = Lng (Pred M) - 1 := by omega
  have hpredNz : zeroT (Pred M) = false := by
    have : 1 < Lng (Pred M) := by omega
    simp [zeroT, this.ne']
  have hright := (m_7_3_Mark_rightmost1 (Pred M) m hmPred hpredR hpredNz).1 hmRight
  rw [hright]
  congr 2
  exact entry_Pred M 1 m (by omega)

private theorem scbContexts_self_head_principal {c : BT}
    (hc : c ∈ T_B) (hcP : ∃ p, c = .trm [p]) :
    (scbContexts c (flatBT c)).head? = some ([], []) := by
  have hcFlat := principal_flat_properties hc hcP
  have hself : (c, c) ∈ MarkedB := by
    refine ⟨[], [], ?_⟩
    exact ⟨by simp, fun _ => hcFlat.1, by simp⟩
  obtain ⟨s, b, hhead⟩ :=
    scbContexts_head_exists_of_marked hc hcP hself
  have hd : scb_decomp c s (flatBT c) b :=
    scbContexts_head_decomp hcFlat.1 hhead
  have hdSelf : scb_decomp c [] (flatBT c) [] :=
    ⟨by simp, fun _ => hcFlat.1, by simp⟩
  have hu := scb_unique_decomp_unconditional c s [] (flatBT c) b []
    hd hdSelf
  simpa [hu.1, hu.2] using hhead

/-- The mark at the second basepoint is exactly the surgery component `c₂`. -/
theorem Mark_transJm1_eq_transC2 (M : PS)
    (hR : RTPS M) (hmono : monoT M = true) (hlen : 1 < Lng M)
    (ht₁ : Trans (Pred M) ≠ BZero) :
    Mark M (transJm1 M) = transC2 M := by
  have hM : TPS M := RTPS_TPS M hR
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hparLt : lastParent M < lastIdx M := by
    simpa [lastParent, lastIdx] using
      parent_lt_of_hasParent M 0 (Lng M - 1) hp
  have hmLt : transJm1 M < lastIdx M := by
    have := Adm_le M (lastParent M)
    simpa [transJm1, transJ0] using this.trans_lt hparLt
  have hmPred : Marked (Pred M) (transJm1 M) := by
    simpa [transJm1, transJ0, lastParent] using
      Marked_Pred_Adm M hM hlen hp
  have hcTB := Mark_mem_T_B (Pred M) (transJm1 M)
    (RTPS_Pred M hR) hmPred
  have hcMarked := Trans_Mark_mem_MarkedB (Pred M) (transJm1 M)
    (RTPS_Pred M hR) hmPred
  have hcP : ∃ p, Mark (Pred M) (transJm1 M) = .trm [p] :=
    marked_component_principal ht₁ hcMarked
  have hhead := scbContexts_self_head_principal hcTB hcP
  have hmLt' : Adm M (lastParent M) < lastIdx M := by
    simpa [transJm1, transJ0] using hmLt
  have hhead' :
      (scbContexts (Mark (Pred M) (Adm M (lastParent M)))
        (flatBT (Mark (Pred M) (Adm M (lastParent M))))).head? =
          some ([], []) := by
    simpa [transJm1, transJ0] using hhead
  have heq := (Trans_Mark_mono_equations M hR hlen hmono).2 (transJm1 M)
  simpa [ht₁, hmLt', transJm1, transJ0, transC2, transC1, transV,
    transT2, hhead', unflatBT_flat] using heq

private theorem nextR1_consecutive_74 (M : PS) (j : ℕ)
    (hL : j + 1 < Lng M)
    (he0 : entry M 0 j < entry M 0 (j + 1))
    (he1 : entry M 1 j < entry M 1 (j + 1)) :
    nextR M 1 j (j + 1) = true := by
  have hn0 : nextR M 0 j (j + 1) = true := by
    simp only [nextR, if_pos, nextrel0, Bool.and_eq_true,
      decide_eq_true_eq, List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨by omega, hL⟩, by omega⟩, he0⟩, ?_⟩
    intro k hk
    by_cases hjk : j < k
    · have : k = j + 1 := by omega
      subst k
      simp
    · simp [hjk]
  have hle0 : le0 M j (j + 1) = true := by
    simpa [leR] using nextR0_leR M j (j + 1) hn0
  simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨by omega, hL⟩, by omega⟩, he1⟩, hle0⟩, ?_⟩
  intro k hk
  by_cases hjk : j < k
  · by_cases hle : le0 M k (j + 1) = true
    · have hkle := le0_index_fseq hle
      have : k = j + 1 := by omega
      subst k
      simp
    · simp [hjk, hle]
  · simp [hjk]

private theorem terminal_primary_or_VI (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M)
    (hmLast : m = Lng M - 2) (hlen : 1 < Lng M - 1) :
    (transCondI M || transCondIII M || transCondV M) = true ∨
      transCondVI M = true := by
  have hM : TPS M := RTPS_TPS M hR
  have hlastLt : lastIdx M < Lng M := by simp [lastIdx]; omega
  have hmSucc : m + 1 = lastIdx M := by simp [lastIdx, hmLast]; omega
  have hle0last : le0 M m (lastIdx M) = true := by
    simpa [leR] using hm.2.2
  have hle0adj : le0 M m (m + 1) = true := by
    simpa [hmSucc] using hle0last
  have hnr0adj : nextrel0 M m (m + 1) = true :=
    le0_adjacent M m hle0adj
  have hn0 : nextR M 0 m (lastIdx M) = true := by
    simpa [nextR, hmSucc] using hnr0adj
  have hpar : lastParent M = m := by
    simpa [lastParent] using parent_eq_of_nextR0 M m (lastIdx M) hn0
  by_cases hb0 : entry M 1 (lastIdx M) = 0
  · left
    have hI : transCondI M = true := by
      simp [transCondI, hb0, hpar, hm.2.1]
    simp [hI]
  · have hbpos : 0 < entry M 1 (lastIdx M) := Nat.pos_of_ne_zero hb0
    by_cases hge : entry M 1 (lastIdx M) ≤ entry M 1 m
    · left
      have hIII : transCondIII M = true := by
        simp [transCondIII, hbpos, hpar, hge, hm.2.1]
      simp [hIII]
    · right
      have he1 : entry M 1 m < entry M 1 (lastIdx M) := by omega
      have hnr0 := hnr0adj
      simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true] at hnr0
      have he0 : entry M 0 m < entry M 0 (lastIdx M) := by
        simpa [← hmSucc] using hnr0.1.2
      have hn1adj := nextR1_consecutive_74 M m
        (by simpa [hmSucc] using hlastLt) (by simpa [hmSucc] using he0)
        (by simpa [hmSucc] using he1)
      have hn1 : nextR M 1 m (lastIdx M) = true := by
        simpa [hmSucc] using hn1adj
      have hp1 : hasParent M 1 (lastIdx M) = true :=
        (hasParent_iff_unique_fseq M 1 (lastIdx M)).mpr
          ⟨m, hn1, fun q hq => nextR1_unique_mr M q m (lastIdx M) hq hn1⟩
      have hpar1 : parent M 1 (lastIdx M) = m :=
        parent_eq_of_unique_fseq M 1 (lastIdx M) m hn1
          (fun q hq => nextR1_unique_mr M q m (lastIdx M) hq hn1)
      have hA := (RTPS_condAB M hR).1
      have hstep := RedCondA_apply M hA 1 (lastIdx M) (by omega)
        hlastLt hp1
      have hsucc : entry M 1 m + 1 = entry M 1 (lastIdx M) := by
        simpa [hpar1] using hstep
      simp only [transCondVI, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq]
      exact ⟨⟨hbpos, by simpa [hpar] using hsucc⟩,
        by simpa [hpar] using hmSucc⟩

/-- The representation theorem in the boundary case of a mono sequence. -/
theorem Mark_Trans_repr_mono_boundary (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M) (hmono : monoT M = true)
    (hmLast : m = Lng M - 2) (hlen : 1 < Lng M - 1) :
    Mark M m = Trans (seg M m (Lng M - 1)) := by
  have hM : TPS M := RTPS_TPS M hR
  have hlenM : 1 < Lng M := by omega
  have hmSucc : m + 1 = lastIdx M := by simp [lastIdx, hmLast]; omega
  have hle0last : le0 M m (lastIdx M) = true := by
    simpa [leR] using hm.2.2
  have hle0adj : le0 M m (m + 1) = true := by
    simpa [hmSucc] using hle0last
  have hn0 : nextR M 0 m (lastIdx M) = true := by
    have := le0_adjacent M m hle0adj
    simpa [nextR, hmSucc] using this
  have hpar : lastParent M = m := by
    simpa [lastParent] using parent_eq_of_nextR0 M m (lastIdx M) hn0
  have hjm : transJm1 M = m := by
    simp [transJm1, transJ0, hpar, Adm, hm.2.1]
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hlenM
  have hpredNz : zeroT (Pred M) = false := by
    have : 1 < Lng (Pred M) := by omega
    simp [zeroT, this.ne']
  have ht₁ : Trans (Pred M) ≠ BZero := by
    intro ht
    have hz := (Trans_preserves_zeroT (Pred M) (RTPS_TPS (Pred M) hpredR)).2 ht
    rw [hpredNz] at hz
    simp at hz
  have hmarkC2 : Mark M m = transC2 M := by
    simpa [hjm] using Mark_transJm1_eq_transC2 M hR hmono hlenM ht₁
  have hc0 := Mark_Pred_terminal_boundary M m hm hR hmLast hlen
  have hc1 : transC1 M = Dprin (entry M 1 m : ℕ∞) BZero := by
    simpa [transC1, hjm] using hc0
  have hv : transV M = (entry M 1 m : ℕ∞) := by
    simp [transV, hc1, bpHeadV, Dprin]
  have ht2 : transT2 M = BZero := by
    simp [transT2, hc1, bpHeadT, Dprin]
  have hcond := terminal_primary_or_VI M m hm hR hmLast hlen
  have hc2 : transC2 M =
      Dprin (entry M 1 m : ℕ∞)
        (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero) := by
    by_cases hprimary :
        (transCondI M || transCondIII M || transCondV M) = true
    · simp [transC2, transC2Core, hprimary, hv, ht2, lastIdx]
    · have hVI : transCondVI M = true := hcond.resolve_left hprimary
      simp [transC2, transC2Core, hprimary, hVI, hv, lastIdx]
  have hrhs := Trans_terminal_slice_two_column M m hm hR hmLast hlen
  exact hmarkC2.trans (hc2.trans hrhs.symm)

/-- Removing the last column commutes with reducing a nontrivial terminal
slice. -/
theorem Pred_Red_terminal_slice (M : PS) (m j₁ : ℕ) (hlt : m < j₁) :
    Pred (Red (seg M m j₁)) = Red (seg M m (j₁ - 1)) := by
  let S := seg M m j₁
  have hSlen : Lng S = j₁ + 1 - m := by simp [S]
  have hlen : 1 < Lng S := by omega
  have hST : TPS S := by
    intro hnil
    have : Lng S = 0 := by simp [hnil]
    omega
  have hpred : Pred S = seg M m (j₁ - 1) := by
    rw [Pred_eq_take S hlen]
    apply List.ext_getElem
    · simp [S]
      omega
    · intro i hiTake hiSeg
      simp only [List.getElem_take]
      have hi' : i < j₁ + 1 - m - 1 := by simpa [S] using hiTake
      have hi : i < j₁ - m := by omega
      simp [S, seg, List.getElem_range']
  rw [← Red_Pred S hST, hpred]

/-- The translation of the predecessor of a reduced terminal slice is the
translation of the slice shortened by one column. -/
theorem Trans_Pred_Red_terminal_slice (M : PS) (m : ℕ)
    (hlt : m < Lng M - 2) :
    Trans (Pred (Red (seg M m (Lng M - 1)))) =
      Trans (seg M m (Lng M - 2)) := by
  have hlast : m < Lng M - 1 := by omega
  rw [Pred_Red_terminal_slice M m (Lng M - 1) hlast]
  have heq : Lng M - 1 - 1 = Lng M - 2 := by omega
  rw [heq]
  have hT : TPS (seg M m (Lng M - 2)) := by
    intro hnil
    have hzero : Lng (seg M m (Lng M - 2)) = 0 := by simp [hnil]
    simp at hzero
    omega
  exact (Trans_Red (seg M m (Lng M - 2)) hT).symm

/-- A slice ending before the deleted final column is unchanged by `Pred`. -/
theorem seg_Pred_eq (M : PS) (a b : ℕ)
    (hlen : 1 < Lng M) (hab : a ≤ b) (hb : b < Lng M - 1) :
    seg (Pred M) a b = seg M a b := by
  rw [Pred_eq_take M hlen]
  apply List.ext_getElem
  · simp
  · intro i hiPred hiM
    have hi : i < b + 1 - a := by simpa using hiM
    have hai : a + i < Lng M - 1 := by omega
    simp [seg, List.getElem_range', entry_take M (Lng M - 1), hai]

/-- First surgery identity in the mono interior case. -/
theorem Mark_Pred_eq_Trans_Pred_Red_slice (M : PS) (m : ℕ)
    (hlt : m < Lng M - 2)
    (hIH : Mark (Pred M) m =
      Trans (seg (Pred M) m (Lng (Pred M) - 1))) :
    Mark (Pred M) m =
      Trans (Pred (Red (seg M m (Lng M - 1)))) := by
  have hlen : 1 < Lng M := by omega
  have hpredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hseg : seg (Pred M) m (Lng (Pred M) - 1) =
      seg M m (Lng M - 2) := by
    have hmle : m ≤ Lng M - 2 := by omega
    have hb : Lng M - 2 < Lng M - 1 := by omega
    simpa [hpredLen] using seg_Pred_eq M m (Lng M - 2) hlen hmle hb
  have hshort := Trans_Pred_Red_terminal_slice M m hlt
  rw [hIH, hseg]
  exact hshort.symm

private theorem parent_IncrFirstN_74 (k : ℕ) (M : PS) (i j : ℕ) :
    parent (IncrFirstN k M) i j = parent M i j := by
  simp [parent, parents, nextR_IncrFirstN_ri]

private theorem hasParent_IncrFirstN_74 (k : ℕ) (M : PS) (i j : ℕ) :
    hasParent (IncrFirstN k M) i j = hasParent M i j := by
  simp [hasParent, parents, nextR_IncrFirstN_ri]

private theorem adm_IncrFirstN_74 (k : ℕ) (M : PS) (j : ℕ) :
    adm (IncrFirstN k M) j = adm M j := by
  simp [adm, nadm, nextR_IncrFirstN_ri]

private theorem Adm_IncrFirstN_74 (k : ℕ) (M : PS) (j : ℕ) :
    Adm (IncrFirstN k M) j = Adm M j := by
  simp [Adm, adm_IncrFirstN_74]

private theorem parent0_terminal_seg (M : PS) (m j₁ : ℕ)
    (hj₁ : j₁ < Lng M) (hmp : m ≤ parent M 0 j₁)
    (hp : hasParent M 0 j₁ = true) :
    hasParent (seg M m j₁) 0 (j₁ - m) = true ∧
      parent (seg M m j₁) 0 (j₁ - m) = parent M 0 j₁ - m := by
  let p := parent M 0 j₁
  let pl := p - m
  let jl := j₁ - m
  have hnextM : nextR M 0 p j₁ = true := by
    simpa [p] using hasParent_next_fseq M 0 j₁ hp
  have hpLt : p < j₁ := by
    simpa [p] using parent_lt_of_hasParent M 0 j₁ hp
  have hmpl : m + pl = p := by simp [pl, p, hmp]
  have hmjl : m + jl = j₁ := by simp [jl]; omega
  have hpljl : pl < jl := by omega
  have hjlS : jl < Lng (seg M m j₁) := by simp [jl]; omega
  have hplS : pl < Lng (seg M m j₁) := hpljl.trans hjlS
  have hnextS : nextR (seg M m j₁) 0 pl jl = true := by
    rw [nextR_seg_adm M m j₁ 0 pl jl (by omega) hj₁ hplS hjlS]
    simpa [hmpl, hmjl] using hnextM
  have huniq : ∀ q, nextR (seg M m j₁) 0 q jl = true → q = pl := by
    intro q hq
    exact row0_parent_unique (seg M m j₁) q pl jl hq hnextS
  have hpS : hasParent (seg M m j₁) 0 jl = true :=
    (hasParent_iff_unique_fseq (seg M m j₁) 0 jl).mpr
      ⟨pl, hnextS, huniq⟩
  have hparS : parent (seg M m j₁) 0 jl = pl :=
    parent_eq_of_unique_fseq (seg M m j₁) 0 jl pl hnextS huniq
  simpa [jl, pl, p] using And.intro hpS hparS

theorem transJ0_Red_terminal_slice (M : PS) (m : ℕ)
    (hR : RTPS M) (hlt : m < Lng M - 2)
    (hanc : leR M 0 m (Lng M - 1) = true)
    (hp : hasParent M 0 (Lng M - 1) = true)
    (hmp : m ≤ parent M 0 (Lng M - 1)) :
    transJ0 (Red (seg M m (Lng M - 1))) = transJ0 M - m := by
  let j₁ := Lng M - 1
  let S := seg M m j₁
  let N := Red S
  let k := entry M 0 m - entry M 1 m
  have hmj : m < j₁ := by simp [j₁]; omega
  have hjL : j₁ < Lng M := by simp [j₁]; omega
  have hfacts := ancestor_slice_Red_IncrFirst M m j₁ hR hmj
    (by simp [j₁]) (by simpa [j₁] using hanc)
  have hread : S = IncrFirstN k N := by
    simpa [S, N, k] using hfacts.2.2
  have hSlen : Lng S = j₁ + 1 - m := by simp [S]
  have hNlen : Lng N = Lng S := by
    have heq := congrArg Lng hread
    simpa using heq.symm
  have hNlast : Lng N - 1 = j₁ - m := by omega
  have hs := parent0_terminal_seg M m j₁ hjL hmp hp
  have hparNS : parent N 0 (j₁ - m) = parent S 0 (j₁ - m) := by
    rw [hread, parent_IncrFirstN_74]
  calc
    transJ0 N = parent N 0 (j₁ - m) := by
      simp [transJ0, lastParent, lastIdx, hNlast]
    _ = parent S 0 (j₁ - m) := hparNS
    _ = parent M 0 j₁ - m := hs.2
    _ = transJ0 M - m := by simp [transJ0, lastParent, lastIdx, j₁]

theorem entry1_Red_terminal_slice (M : PS) (m i : ℕ)
    (hR : RTPS M) (hlt : m < Lng M - 2)
    (hanc : leR M 0 m (Lng M - 1) = true)
    (hi : i < Lng (Red (seg M m (Lng M - 1)))) :
    entry (Red (seg M m (Lng M - 1))) 1 i = entry M 1 (m + i) := by
  let j₁ := Lng M - 1
  let S := seg M m j₁
  let N := Red S
  let k := entry M 0 m - entry M 1 m
  have hmj : m < j₁ := by simp [j₁]; omega
  have hfacts := ancestor_slice_Red_IncrFirst M m j₁ hR hmj
    (by simp [j₁]) (by simpa [j₁] using hanc)
  have hread : S = IncrFirstN k N := by
    simpa [S, N, k] using hfacts.2.2
  have hiN : i < Lng N := by simpa [N, S] using hi
  have hiS : i < Lng S := by
    rw [hread]
    simpa using hiN
  have hSN : entry S 1 i = entry N 1 i := by
    rw [hread, entry_IncrFirstN_one]
  have hSM : entry S 1 i = entry M 1 (m + i) := by
    simpa [S] using entry_seg M m j₁ 1 i hiS
  exact hSN.symm.trans hSM

theorem transJm1_Red_terminal_slice (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M) (hlt : m < Lng M - 2)
    (hanc : leR M 0 m (Lng M - 1) = true)
    (hp : hasParent M 0 (Lng M - 1) = true)
    (hmp : m ≤ parent M 0 (Lng M - 1)) :
    transJm1 (Red (seg M m (Lng M - 1))) = transJm1 M - m := by
  let j₁ := Lng M - 1
  let S := seg M m j₁
  let N := Red S
  let k := entry M 0 m - entry M 1 m
  have hM : TPS M := RTPS_TPS M hR
  have hmj : m < j₁ := by simp [j₁]; omega
  have hjL : j₁ < Lng M := by simp [j₁]; omega
  have hfacts := ancestor_slice_Red_IncrFirst M m j₁ hR hmj
    (by simp [j₁]) (by simpa [j₁] using hanc)
  have hread : S = IncrFirstN k N := by
    simpa [S, N, k] using hfacts.2.2
  have hJ0 : transJ0 N = transJ0 M - m := by
    simpa [N, S] using transJ0_Red_terminal_slice M m hR hlt hanc hp hmp
  have hAdmNS (q : ℕ) : Adm N q = Adm S q := by
    rw [hread, Adm_IncrFirstN_74]
  have hAdmAnchor : m ≤ Adm M (transJ0 M) := by
    exact Adm_max M m (transJ0 M) hm.2.1 (by
      simpa [transJ0, lastParent, lastIdx] using hmp)
  have hJ0lt : transJ0 M < j₁ := by
    simpa [transJ0, lastParent, lastIdx, j₁] using
      parent_lt_of_hasParent M 0 (Lng M - 1) hp
  have hAdmSlice : Adm S (transJ0 M - m) = Adm M (transJ0 M) - m := by
    simpa [S] using admof_slice M m (transJ0 M) j₁ hM hAdmAnchor hJ0lt
      (by simp [j₁])
  calc
    transJm1 N = Adm N (transJ0 N) := by rfl
    _ = Adm N (transJ0 M - m) := by rw [hJ0]
    _ = Adm S (transJ0 M - m) := hAdmNS _
    _ = Adm M (transJ0 M) - m := hAdmSlice
    _ = transJm1 M - m := by rfl

theorem transC1_Red_terminal_slice (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M) (hlt : m < Lng M - 2)
    (hanc : leR M 0 m (Lng M - 1) = true)
    (hp : hasParent M 0 (Lng M - 1) = true)
    (hmp : m ≤ parent M 0 (Lng M - 1))
    (hMarkShift :
      Mark (Pred (Red (seg M m (Lng M - 1)))) (transJm1 M - m) =
        Mark (Pred M) (transJm1 M)) :
    transC1 M = transC1 (Red (seg M m (Lng M - 1))) := by
  have hjm := transJm1_Red_terminal_slice M m hm hR hlt hanc hp hmp
  simp only [transC1]
  rw [hjm, hMarkShift]

private theorem transC2_congr_74 (M N : PS)
    (hc1 : transC1 M = transC1 N)
    (he0 : entry N 1 (lastParent N) = entry M 1 (lastParent M))
    (he1 : entry N 1 (lastIdx N) = entry M 1 (lastIdx M))
    (hI : transCondI N = transCondI M)
    (hIII : transCondIII N = transCondIII M)
    (hV : transCondV N = transCondV M)
    (hVI : transCondVI N = transCondVI M) :
    transC2 M = transC2 N := by
  have hv : transV N = transV M := by simp [transV, hc1]
  have ht2 : transT2 N = transT2 M := by simp [transT2, hc1]
  unfold transC2 transC2Core
  simp only [hv, ht2, he0, he1, hI, hIII, hV, hVI]

theorem adm_lastParent_Red_terminal_slice (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M) (hlt : m < Lng M - 2)
    (hanc : leR M 0 m (Lng M - 1) = true)
    (hp : hasParent M 0 (Lng M - 1) = true)
    (hmp : m ≤ parent M 0 (Lng M - 1)) :
    adm (Red (seg M m (Lng M - 1)))
        (lastParent (Red (seg M m (Lng M - 1)))) =
      adm M (lastParent M) := by
  let j₁ := Lng M - 1
  let S := seg M m j₁
  let N := Red S
  let k := entry M 0 m - entry M 1 m
  have hM : TPS M := RTPS_TPS M hR
  have hmj : m < j₁ := by simp [j₁]; omega
  have hfacts := ancestor_slice_Red_IncrFirst M m j₁ hR hmj
    (by simp [j₁]) (by simpa [j₁] using hanc)
  have hread : S = IncrFirstN k N := by
    simpa [S, N, k] using hfacts.2.2
  have hJ0 : lastParent N = lastParent M - m := by
    simpa [transJ0] using
      transJ0_Red_terminal_slice M m hR hlt hanc hp hmp
  have hAdmNS : adm N (lastParent M - m) =
      adm S (lastParent M - m) := by
    rw [hread, adm_IncrFirstN_74]
  have hparLt : lastParent M < j₁ := by
    simpa [lastParent, lastIdx, j₁] using
      parent_lt_of_hasParent M 0 (Lng M - 1) hp
  have hslice := adm_slice M m (lastParent M) j₁ hM
    (by simpa [lastParent, lastIdx] using hmp) hparLt.le (by simp [j₁])
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hN
    have hS : adm S (lastParent M - m) = true := by
      rw [← hAdmNS, ← hJ0]
      simpa [N, S] using hN
    rcases hslice.mpr hS with hAdm | hleft | hright
    · exact hAdm
    · have hmAdm := hm.2.1
      simpa [hleft] using hmAdm
    · exact (Nat.ne_of_lt hparLt hright).elim
  · intro hAdm
    have hS : adm S (lastParent M - m) = true :=
      hslice.mp (Or.inl hAdm)
    rw [hJ0, hAdmNS]
    simpa [N, S] using hS

private theorem terminal_condition_congruences (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M) (hlt : m < Lng M - 2)
    (hanc : leR M 0 m (Lng M - 1) = true)
    (hp : hasParent M 0 (Lng M - 1) = true)
    (hmp : m ≤ parent M 0 (Lng M - 1)) :
    let N := Red (seg M m (Lng M - 1))
    transCondI N = transCondI M ∧
      transCondIII N = transCondIII M ∧
      transCondV N = transCondV M ∧
      transCondVI N = transCondVI M := by
  let S := seg M m (Lng M - 1)
  let N := Red S
  have hSlen : Lng S = Lng M - m := by simp [S]; omega
  have hST : TPS S := by
    intro hnil
    have : Lng S = 0 := by simp [hnil]
    omega
  have hNlen : Lng N = Lng S := by
    simpa [N] using Lng_Red_invariance S hST
  have hlast : lastIdx N = lastIdx M - m := by
    simp [lastIdx, hNlen, hSlen]
    omega
  have hpar : lastParent N = lastParent M - m := by
    simpa [N, S, transJ0] using
      transJ0_Red_terminal_slice M m hR hlt hanc hp hmp
  have hNpos : 0 < Lng N := by omega
  have hlastBound : lastIdx N < Lng N := by simp [lastIdx]; omega
  have hparBound : lastParent N < Lng N := by
    have hparMLt : lastParent M < lastIdx M := by
      simpa [lastParent, lastIdx] using
        parent_lt_of_hasParent M 0 (Lng M - 1) hp
    omega
  have hmp' : m ≤ lastParent M := by
    simpa [lastParent, lastIdx] using hmp
  have hmlast : m ≤ lastIdx M := by simp [lastIdx]; omega
  have hlastSum : m + lastIdx N = lastIdx M := by omega
  have hparSum : m + lastParent N = lastParent M := by omega
  have heLast : entry N 1 (lastIdx N) = entry M 1 (lastIdx M) := by
    have he := entry1_Red_terminal_slice M m (lastIdx N) hR hlt hanc
      (by simpa [N, S] using hlastBound)
    exact he.trans (by rw [hlastSum])
  have hePar : entry N 1 (lastParent N) = entry M 1 (lastParent M) := by
    have he := entry1_Red_terminal_slice M m (lastParent N) hR hlt hanc
      (by simpa [N, S] using hparBound)
    exact he.trans (by rw [hparSum])
  have hAdm : adm N (lastParent N) = adm M (lastParent M) := by
    simpa [N, S] using
      adm_lastParent_Red_terminal_slice M m hm hR hlt hanc hp hmp
  have hltAr : (lastParent N + 1 < lastIdx N) ↔
      lastParent M + 1 < lastIdx M := by omega
  have heqAr : (lastParent N + 1 = lastIdx N) ↔
      lastParent M + 1 = lastIdx M := by omega
  change transCondI N = transCondI M ∧
    transCondIII N = transCondIII M ∧
    transCondV N = transCondV M ∧
    transCondVI N = transCondVI M
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Bool.eq_iff_iff.mpr
    simp [transCondI, heLast, hAdm]
  · apply Bool.eq_iff_iff.mpr
    simp [transCondIII, heLast, hePar, hAdm]
  · apply Bool.eq_iff_iff.mpr
    simp [transCondV, heLast, hePar, hltAr]
  · apply Bool.eq_iff_iff.mpr
    simp [transCondVI, heLast, hePar, heqAr]

theorem Mark_Trans_repr_mono_interior (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M) (hmono : monoT M = true)
    (hlt : m < Lng M - 2)
    (hIHPred : Mark (Pred M) m =
      Trans (seg (Pred M) m (Lng (Pred M) - 1)))
    (hMarkShift :
      Mark (Pred (Red (seg M m (Lng M - 1)))) (transJm1 M - m) =
        Mark (Pred M) (transJm1 M)) :
    Mark M m = Trans (seg M m (Lng M - 1)) := by
  let j₁ := Lng M - 1
  let S := seg M m j₁
  let N := Red S
  have hM : TPS M := RTPS_TPS M hR
  have hlenM : 1 < Lng M := by omega
  have hmj : m < j₁ := by simp [j₁]; omega
  have hanc : leR M 0 m j₁ = true := by simpa [j₁] using hm.2.2
  have hp : hasParent M 0 j₁ = true := by
    simpa [j₁] using mono_hasParent_row0 M hM hmono (Lng M - 1)
      (by omega) (by omega)
  have hmp : m ≤ parent M 0 j₁ := by
    simpa [j₁] using marked_le_lastParent M hm hmono hlenM (by omega)
  have hST : TPS S := by
    intro hnil
    have : Lng S = 0 := by simp [hnil]
    simp [S] at this
    omega
  have hmonoS : monoT S = true := by
    simpa [S] using mono_ancestor_slice M m j₁ hM hmj hanc
  have hSnm : multiT S = false := by simp [multiT, hmonoS]
  have hNR : RTPS N := by
    simpa [N] using Red_nonmulti_RTPS S hST hSnm
  have hfacts := ancestor_slice_Red_IncrFirst M m j₁ hR hmj
    (by simp [j₁]) hanc
  have hmonoN : monoT N = true := by simpa [S, N] using hfacts.2.1
  have hSlen : Lng S = Lng M - m := by simp [S, j₁]; omega
  have hNlen : Lng N = Lng S := by
    simpa [N] using Lng_Red_invariance S hST
  have hlenN : 1 < Lng N := by omega
  have hlenN3 : 2 < Lng N := by omega
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hlenM
  have hpredNz : zeroT (Pred M) = false := by
    have : 1 < Lng (Pred M) := by omega
    simp [zeroT, this.ne']
  have htM : Trans (Pred M) ≠ BZero := by
    intro ht
    have hz := (Trans_preserves_zeroT (Pred M) (RTPS_TPS (Pred M) hpredR)).2 ht
    rw [hpredNz] at hz
    simp at hz
  have hpredNR : RTPS (Pred N) := RTPS_Pred N hNR
  have hpredNLen : Lng (Pred N) = Lng N - 1 := length_Pred N hlenN
  have hpredNNz : zeroT (Pred N) = false := by
    have : 1 < Lng (Pred N) := by omega
    simp [zeroT, this.ne']
  have htN : Trans (Pred N) ≠ BZero := by
    intro ht
    have hz := (Trans_preserves_zeroT (Pred N) (RTPS_TPS (Pred N) hpredNR)).2 ht
    rw [hpredNNz] at hz
    simp at hz
  have hid1 : Mark (Pred M) m = Trans (Pred N) := by
    simpa [N, S] using
      Mark_Pred_eq_Trans_Pred_Red_slice M m hlt hIHPred
  have hid2 : transC1 M = transC1 N := by
    simpa [N, S, j₁] using transC1_Red_terminal_slice M m hm hR hlt
      (by simpa [j₁] using hanc) (by simpa [j₁] using hp)
      (by simpa [j₁] using hmp) hMarkShift
  have hconds := terminal_condition_congruences M m hm hR hlt
    (by simpa [j₁] using hanc) (by simpa [j₁] using hp)
    (by simpa [j₁] using hmp)
  have hlastN : lastIdx N = lastIdx M - m := by
    simp [lastIdx, hNlen, hSlen]
    omega
  have hparN : lastParent N = lastParent M - m := by
    simpa [N, S, transJ0] using transJ0_Red_terminal_slice M m hR hlt
      (by simpa [j₁] using hanc) (by simpa [j₁] using hp)
      (by simpa [j₁] using hmp)
  have hmp' : m ≤ lastParent M := by
    simpa [lastParent, lastIdx, j₁] using hmp
  have hmlast : m ≤ lastIdx M := by simp [lastIdx]; omega
  have hlastBound : lastIdx N < Lng N := by simp [lastIdx]; omega
  have hparBound : lastParent N < Lng N := by
    have hpLt : lastParent M < lastIdx M := by
      simpa [lastParent, lastIdx, j₁] using
        parent_lt_of_hasParent M 0 j₁ hp
    omega
  have heLast : entry N 1 (lastIdx N) = entry M 1 (lastIdx M) := by
    have he := entry1_Red_terminal_slice M m (lastIdx N) hR hlt
      (by simpa [j₁] using hanc) (by simpa [N, S] using hlastBound)
    have hsum : m + lastIdx N = lastIdx M := by omega
    exact he.trans (by rw [hsum])
  have hePar : entry N 1 (lastParent N) = entry M 1 (lastParent M) := by
    have he := entry1_Red_terminal_slice M m (lastParent N) hR hlt
      (by simpa [j₁] using hanc) (by simpa [N, S] using hparBound)
    have hsum : m + lastParent N = lastParent M := by omega
    exact he.trans (by rw [hsum])
  have hid3 : transC2 M = transC2 N :=
    transC2_congr_74 M N hid2 hePar heLast hconds.1 hconds.2.1
      hconds.2.2.1 hconds.2.2.2
  have hpN : hasParent N 0 (Lng N - 1) = true :=
    mono_hasParent_row0 N (RTPS_TPS N hNR) hmonoN (Lng N - 1)
      (by omega) (by omega)
  have hc1Marked : Marked (Pred N) (transJm1 N) := by
    simpa [transJm1, transJ0, lastParent] using
      Marked_Pred_Adm N (RTPS_TPS N hNR) hlenN hpN
  have hc1TB := Mark_mem_T_B (Pred N) (transJm1 N) hpredNR hc1Marked
  have hc1MB := Trans_Mark_mem_MarkedB (Pred N) (transJm1 N)
    hpredNR hc1Marked
  have hc1P : ∃ p, Mark (Pred N) (transJm1 N) = .trm [p] :=
    marked_component_principal htN hc1MB
  obtain ⟨s, b, hheadNraw⟩ :=
    scbContexts_head_exists_of_marked hc1TB hc1P hc1MB
  have hheadN :
      (scbContexts (Trans (Pred N)) (flatBT (transC1 N))).head? =
        some (s, b) := by
    simpa [transC1] using hheadNraw
  have hheadM :
      (scbContexts (Mark (Pred M) m) (flatBT (transC1 M))).head? =
        some (s, b) := by
    simpa [hid1, hid2] using hheadN
  have hheadM' :
      (scbContexts (Mark (Pred M) m)
        (flatBT (Mark (Pred M) (Adm M (lastParent M))))).head? =
          some (s, b) := by
    simpa [transC1, transJm1, transJ0] using hheadM
  have hheadN' :
      (scbContexts (Trans (Pred N))
        (flatBT (Mark (Pred N) (Adm N (lastParent N))))).head? =
          some (s, b) := by
    simpa [transC1, transJm1, transJ0] using hheadN
  have hmjLast : m < lastIdx M := by simpa [j₁, lastIdx] using hmj
  have hmarkEq := (Trans_Mark_mono_equations M hR hlenM hmono).2 m
  have hmarkVal : Mark M m =
      unflatBT (s ++ flatBT (transC2 M) ++ b) := by
    simpa [htM, hmjLast, transC1, transC2, transV, transT2, transJm1,
      transJ0, hheadM'] using hmarkEq
  have htransEq := (Trans_Mark_mono_equations N hNR hlenN hmonoN).1
  have htransVal : Trans N =
      unflatBT (s ++ flatBT (transC2 N) ++ b) := by
    simpa [htN, replaceScb, transC1, transC2, transV, transT2,
      transJm1, transJ0, hheadN'] using htransEq
  have hMN : Mark M m = Trans N := by
    rw [hmarkVal, htransVal, hid3]
  have hSN : Trans S = Trans N := by
    simpa [N] using Trans_Red S hST
  exact hMN.trans hSN.symm

private theorem Trans_IncrFirstN_74 (k : ℕ) (M : PS) (hM : TPS M) :
    Trans (IncrFirstN k M) = Trans M := by
  induction k generalizing M with
  | zero => rfl
  | succ k ih =>
      have hI : TPS (IncrFirst M) := by
        simpa [TPS, IncrFirst] using hM
      calc
        Trans (IncrFirstN (k + 1) M) =
            Trans (IncrFirstN k (IncrFirst M)) := by rfl
        _ = Trans (IncrFirst M) := ih (IncrFirst M) hI
        _ = Trans M := Trans_IncrFirst M hM

/-- Translation transport for an interior terminal slice of the predecessor
of a reduced backward slice. -/
theorem Trans_Pred_Red_slice_shift (M : PS) (m a : ℕ)
    (hR : RTPS M) (hlt : m < Lng M - 2)
    (hanc : leR M 0 m (Lng M - 1) = true)
    (ha : a < Lng (Red (seg M m (Lng M - 2))) - 1) :
    Trans (seg (Pred (Red (seg M m (Lng M - 1)))) a
        (Lng (Pred (Red (seg M m (Lng M - 1)))) - 1)) =
      Trans (seg M (m + a) (Lng M - 2)) := by
  let e := Lng M - 2
  let S' := seg M m e
  let R := Red S'
  have hM : TPS M := RTPS_TPS M hR
  have hlenM : 1 < Lng M := by omega
  have hlast : m < Lng M - 1 := by omega
  have hpredN : Pred (Red (seg M m (Lng M - 1))) = R := by
    simpa [R, S', e] using Pred_Red_terminal_slice M m (Lng M - 1) hlast
  have hanc' : leR M 0 m e = true := by
    exact ancestor_tree_1 M m e (Lng M - 1) hM hanc (by omega) (by omega)
  have hS'T : TPS S' := by
    intro hnil
    have : Lng S' = 0 := by simp [hnil]
    simp [S', e] at this
    omega
  have hfacts := ancestor_slice_Red_IncrFirst M m e hR (by omega)
    (by simp [e]; omega) hanc'
  let k := entry M 0 m - entry M 1 m
  have hread : S' = IncrFirstN k R := by
    simpa [S', R, k, e] using hfacts.2.2
  have hRlen : Lng R = Lng S' := by
    simpa [R] using Lng_Red_invariance S' hS'T
  have haR' : a < Lng R - 1 := by simpa [R, S', e] using ha
  have haR : a < Lng R := by omega
  have hRdropT : TPS (R.drop a) := by
    apply List.ne_nil_of_length_pos
    simp only [List.length_drop]
    exact Nat.sub_pos_of_lt haR
  have hdropRead : S'.drop a = IncrFirstN k (R.drop a) := by
    rw [hread, IncrFirstN_eq_map, IncrFirstN_eq_map]
    simp
  have htransDrop : Trans (R.drop a) = Trans (S'.drop a) := by
    rw [hdropRead, Trans_IncrFirstN_74 k (R.drop a) hRdropT]
  have hleft :
      seg (Pred (Red (seg M m (Lng M - 1)))) a
          (Lng (Pred (Red (seg M m (Lng M - 1)))) - 1) = R.drop a := by
    rw [hpredN]
    exact (drop_eq_seg R a haR).symm
  have hpredMLen : Lng (Pred M) = Lng M - 1 := length_Pred M hlenM
  have hmPred : m < Lng (Pred M) := by omega
  have hmaPred : m + a < Lng (Pred M) := by
    have hS'len : Lng S' = Lng M - 1 - m := by simp [S', e]; omega
    omega
  have hmae : m + a ≤ e := by
    have hS'len : Lng S' = Lng M - 1 - m := by simp [S', e]; omega
    omega
  have hS'drop : S'.drop a = seg M (m + a) e := by
    have hS'Pred : S' = (Pred M).drop m := by
      have hseg := seg_Pred_eq M m e hlenM (by omega) (by simp [e]; omega)
      calc
        S' = seg (Pred M) m (Lng (Pred M) - 1) := by
          rw [length_Pred M hlenM]
          simpa [S', e] using hseg.symm
        _ = (Pred M).drop m := (drop_eq_seg (Pred M) m hmPred).symm
    have htail : (Pred M).drop (m + a) =
        seg (Pred M) (m + a) (Lng (Pred M) - 1) :=
      drop_eq_seg (Pred M) (m + a) hmaPred
    have hseg := seg_Pred_eq M (m + a) e hlenM hmae
      (by simp [e]; omega)
    rw [hS'Pred, List.drop_drop, htail]
    rw [length_Pred M hlenM]
    simpa [e] using hseg
  rw [hleft]
  exact htransDrop.trans (congrArg Trans hS'drop)

/-- §7.4 keystone: every proper marked component of a reduced pair sequence
is the translation of its backward terminal slice. -/
theorem Mark_Trans_repr (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M) (hlt : m < Lng M - 1) :
    Mark M m = Trans (seg M m (Lng M - 1)) := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M m with
  | h n ih =>
      rw [← hn]
      have hM : TPS M := RTPS_TPS M hR
      have hlenM : 1 < Lng M := by omega
      by_cases hm0 : m = 0
      · subst m
        exact Mark_Trans_repr_zero M hR hm (by omega)
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        by_cases hmono : monoT M = true
        · by_cases hbnd : m = Lng M - 2
          · have hlenB : 1 < Lng M - 1 := by omega
            exact Mark_Trans_repr_mono_boundary M m hm hR hmono hbnd hlenB
          · have hint : m < Lng M - 2 := by omega
            have hpredR : RTPS (Pred M) := RTPS_Pred M hR
            have hpredLen : Lng (Pred M) = Lng M - 1 :=
              length_Pred M hlenM
            have hpredLt : Lng (Pred M) < n := by rw [hpredLen, ← hn]; omega
            have hmPred : Marked (Pred M) m :=
              Marked_Pred M m hM hlenM hm (by omega)
            have hmPredLt : m < Lng (Pred M) - 1 := by omega
            have hIHPred : Mark (Pred M) m =
                Trans (seg (Pred M) m (Lng (Pred M) - 1)) :=
              ih (Lng (Pred M)) hpredLt (Pred M) m hmPred hpredR hmPredLt rfl
            let j₁ := Lng M - 1
            let S := seg M m j₁
            let N := Red S
            let q := transJm1 M
            let a := q - m
            have hmj : m < j₁ := by simp [j₁]; omega
            have hanc : leR M 0 m j₁ = true := by simpa [j₁] using hm.2.2
            have hp : hasParent M 0 j₁ = true := by
              simpa [j₁] using mono_hasParent_row0 M hM hmono (Lng M - 1)
                (by omega) (by omega)
            have hmp : m ≤ parent M 0 j₁ := by
              simpa [j₁] using marked_le_lastParent M hm hmono hlenM (by omega)
            have hST : TPS S := by
              intro hnil
              have hz : Lng S = 0 := by simp [hnil]
              simp [S, j₁] at hz
              omega
            have hmonoS : monoT S = true := by
              simpa [S] using mono_ancestor_slice M m j₁ hM hmj hanc
            have hNR : RTPS N := by
              have hSnm : multiT S = false := by simp [multiT, hmonoS]
              simpa [N] using Red_nonmulti_RTPS S hST hSnm
            have hNlen : Lng N = Lng M - m := by
              calc
                Lng N = Lng S := by simpa [N] using Lng_Red_invariance S hST
                _ = Lng M - m := by simp [S, j₁]; omega
            have hPredNEq : Pred N = Red (seg M m (Lng M - 2)) := by
              simpa [N, S, j₁] using
                Pred_Red_terminal_slice M m (Lng M - 1) (by omega)
            have hlenN : 1 < Lng N := by omega
            have hlenN3 : 2 < Lng N := by omega
            have hmonoN : monoT N = true := by
              have hf := ancestor_slice_Red_IncrFirst M m j₁ hR hmj
                (by simp [j₁]) hanc
              simpa [S, N] using hf.2.1
            have hpN : hasParent N 0 (Lng N - 1) = true :=
              mono_hasParent_row0 N (RTPS_TPS N hNR) hmonoN (Lng N - 1)
                (by omega) (by omega)
            have hjmN : transJm1 N = q - m := by
              simpa [N, S, q, j₁] using
                transJm1_Red_terminal_slice M m hm hR hint
                  (by simpa [j₁] using hanc) (by simpa [j₁] using hp)
                  (by simpa [j₁] using hmp)
            have hqLower : m ≤ q := by
              have := Adm_max M m (transJ0 M) hm.2.1 (by
                simpa [q, transJm1, transJ0, lastParent, lastIdx, j₁] using hmp)
              simpa [q, transJm1] using this
            have hqUpper : q ≤ Lng M - 2 := by
              have hAdmLe := Adm_le M (transJ0 M)
              have hpLt : parent M 0 j₁ < j₁ :=
                parent_lt_of_hasParent M 0 j₁ hp
              have hraw : Adm M (transJ0 M) ≤ Lng M - 2 := by
                have hpLt' : parent M 0 j₁ < Lng M - 1 := by simpa [j₁] using hpLt
                have hparent : transJ0 M = parent M 0 j₁ := by
                  simp [transJ0, lastParent, lastIdx, j₁]
                rw [hparent] at hAdmLe
                have hpLe : parent M 0 j₁ ≤ Lng M - 2 := by
                  apply Nat.le_sub_of_add_le
                  omega
                exact hAdmLe.trans hpLe
              simpa [q, transJm1] using hraw
            have haEq : a = q - m := rfl
            have hmPredQ : Marked (Pred M) q := by
              simpa [q, transJm1, transJ0, lastParent, lastIdx, j₁] using
                Marked_Pred_Adm M hM hlenM (by simpa [j₁] using hp)
            have hmPredNA : Marked (Pred N) a := by
              have hbase := Marked_Pred_Adm N (RTPS_TPS N hNR) hlenN hpN
              have hbase' : Marked (Pred N) (transJm1 N) := by
                simpa [transJm1, transJ0, lastParent] using hbase
              simpa [a, hjmN] using hbase'
            have hpredNR : RTPS (Pred N) := RTPS_Pred N hNR
            have hpredNLen : Lng (Pred N) = Lng N - 1 :=
              length_Pred N hlenN
            have hpredNLt : Lng (Pred N) < n := by rw [hpredNLen, hNlen, ← hn]; omega
            have hMarkShift :
                Mark (Pred N) a = Mark (Pred M) q := by
              by_cases hqBnd : q = Lng M - 2
              · have haRight : a = Lng (Pred N) - 1 := by
                  simp [a, hpredNLen, hNlen, hqBnd]
                  omega
                have hqRight : q = Lng (Pred M) - 1 := by omega
                have hpredNNz : zeroT (Pred N) = false := by
                  have : 1 < Lng (Pred N) := by omega
                  simp [zeroT, this.ne']
                have hpredMNz : zeroT (Pred M) = false := by
                  have : 1 < Lng (Pred M) := by omega
                  simp [zeroT, this.ne']
                have hmarkN :=
                  (m_7_3_Mark_rightmost1 (Pred N) a hmPredNA hpredNR hpredNNz).1
                    haRight
                have hmarkM :=
                  (m_7_3_Mark_rightmost1 (Pred M) q hmPredQ hpredR hpredMNz).1
                    hqRight
                have haN : a < Lng N - 1 := by omega
                have hentryN : entry (Pred N) 1 a = entry M 1 q := by
                  rw [entry_Pred N 1 a haN]
                  have he := entry1_Red_terminal_slice M m a hR hint
                    (by simpa [j₁] using hanc) (by
                      have : a < Lng N := by omega
                      simpa [N, S, j₁] using this)
                  have hsum : m + a = q := by simp [a, hqLower]
                  exact he.trans (by rw [hsum])
                have hentryM : entry (Pred M) 1 q = entry M 1 q :=
                  entry_Pred M 1 q (by omega)
                rw [hmarkN, hmarkM, hentryN, hentryM]
              · have hqInt : q < Lng M - 2 := by omega
                have haInt : a < Lng (Pred N) - 1 := by
                  simp [a, hpredNLen, hNlen]
                  omega
                have hqIntPred : q < Lng (Pred M) - 1 := by omega
                have hIHN : Mark (Pred N) a =
                    Trans (seg (Pred N) a (Lng (Pred N) - 1)) :=
                  ih (Lng (Pred N)) hpredNLt (Pred N) a hmPredNA hpredNR haInt rfl
                have hIHM : Mark (Pred M) q =
                    Trans (seg (Pred M) q (Lng (Pred M) - 1)) :=
                  ih (Lng (Pred M)) hpredLt (Pred M) q hmPredQ hpredR hqIntPred rfl
                have haShift :
                    a < Lng (Red (seg M m (Lng M - 2))) - 1 := by
                  rw [← hPredNEq]
                  exact haInt
                have hshift := Trans_Pred_Red_slice_shift M m a hR hint
                  (by simpa [j₁] using hanc) haShift
                have hsum : m + a = q := by simp [a, hqLower]
                have hsegQ : seg (Pred M) q (Lng (Pred M) - 1) =
                    seg M q (Lng M - 2) := by
                  simpa [hpredLen] using seg_Pred_eq M q (Lng M - 2)
                    hlenM (by omega) (by omega)
                calc
                  Mark (Pred N) a =
                      Trans (seg (Pred N) a (Lng (Pred N) - 1)) := hIHN
                  _ = Trans (seg M (m + a) (Lng M - 2)) := by
                    simpa [N, S] using hshift
                  _ = Trans (seg M q (Lng M - 2)) := by rw [hsum]
                  _ = Trans (seg (Pred M) q (Lng (Pred M) - 1)) :=
                    congrArg Trans hsegQ.symm
                  _ = Mark (Pred M) q := hIHM.symm
            have hMarkShift' :
                Mark (Pred (Red (seg M m (Lng M - 1)))) (transJm1 M - m) =
                  Mark (Pred M) (transJm1 M) := by
              simpa [N, S, q, a, j₁] using hMarkShift
            exact Mark_Trans_repr_mono_interior M m hm hR hmono hint
              hIHPred hMarkShift'
        · have hzero : zeroT M = false := by simp [zeroT]; omega
          have hmonoF : monoT M = false := Bool.eq_false_of_not_eq_true hmono
          have hmulti : multiT M = true := by simp [multiT, hzero, hmonoF]
          let J := M.drop (Pcut M)
          have hparts := multi_Marked_last_component M m hM hmulti hm
          have hmJ : Marked J (m - Pcut M) := by simpa [J] using hparts.2
          have hcut := Pcut_props M hlenM
          have hJlen : Lng J = Lng M - Pcut M := by simp [J]
          have hJlt : Lng J < n := by rw [hJlen, ← hn]; omega
          have hlastComp := trans_multi_last_component M hM hmulti
          let pJ := (P M).getD ((P M).length - 1) []
          have hpJeq : pJ = J := by simpa [pJ, J] using hlastComp.1
          have hPne : P M ≠ [] := P_nonempty M
          have hidx : (P M).length - 1 < (P M).length := by
            have := List.length_pos_of_ne_nil hPne
            omega
          have hpJR : RTPS pJ :=
            (RTPS_iff_P_components M hM).1 hR ((P M).length - 1) hidx
          have hJR : RTPS J := by simpa [hpJeq] using hpJR
          have hmJlt : m - Pcut M < Lng J - 1 := by omega
          have hIHJ : Mark J (m - Pcut M) =
              Trans (seg J (m - Pcut M) (Lng J - 1)) :=
            ih (Lng J) hJlt J (m - Pcut M) hmJ hJR hmJlt rfl
          exact Mark_Trans_repr_multi_step M m hm hR hlt hmulti
            (by simpa [J] using hIHJ)

#print axioms Mark_zero_eq_Trans
#print axioms Mark_Trans_repr_multi_step
#print axioms Trans_terminal_slice_two_column
#print axioms Mark_Pred_terminal_boundary
#print axioms Mark_transJm1_eq_transC2
#print axioms Mark_Trans_repr_mono_boundary
#print axioms Pred_Red_terminal_slice
#print axioms Trans_Pred_Red_terminal_slice
#print axioms seg_Pred_eq
#print axioms Mark_Pred_eq_Trans_Pred_Red_slice
#print axioms Mark_Trans_repr

end PSS
