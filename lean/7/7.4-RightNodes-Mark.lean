import «7».«7.4-Trans-Mark-seg»
import «7».«7.2-RightNodes-subexpr»
import «6».«6.6-reduced-slice»

/-!
# §7.4 系（`RightNodes` と `Mark` の関係）

- 原文: `isabelle/pss_paper.thy` の `p_7_4_RightNodes_Mark`
- Isabelle: `m_7_4_RightNodes_Mark`
- 訂正: A47（`RTPS` 上の形）
-/

namespace PSS

private theorem transC2Core_outer (M : PS) (v : ℕ∞) (t : BT) :
    ∃ a, transC2Core M v t = Dprin v a := by
  unfold transC2Core
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · split <;> exact ⟨_, rfl⟩

/-- Replacing a marked principal component by another component with the same
outer index preserves the outer index of a principal host. -/
private theorem replaceScb_outer_dprin {c₀ c₁ c₂ : BT} {v : ℕ∞} {a₀ a₂ : BT}
    (hc₀ : c₀ ∈ T_B) (hc₀P : ∃ p, c₀ = .trm [p])
    (hc₁ : c₁ ∈ T_B) (hc₁P : ∃ p, c₁ = .trm [p])
    (hc₂ : c₂ ∈ T_B) (hc₂P : ∃ p, c₂ = .trm [p])
    (hm : (c₀, c₁) ∈ MarkedB)
    (h₀ : c₀ = Dprin v a₀)
    (h₂ : c₂ = Dprin (bpHeadV c₁) a₂) :
    ∃ a, replaceScb c₀ c₁ c₂ = Dprin v a := by
  obtain ⟨s, b, hd, hflat, _⟩ :=
    replaceScb_spec hc₀ hc₁ hc₁P hc₂ hc₂P hm
  have hc₀Head : (flatBT c₀).head? = some (.dsym v) := by
    rw [h₀]
    rfl
  have hc₁Head : (flatBT c₁).head? = some (.dsym (bpHeadV c₁)) := by
    obtain ⟨p, hp⟩ := hc₁P
    rw [hp]
    rcases p with ⟨u, t⟩
    rfl
  have hc₂Head : (flatBT c₂).head? = some (.dsym (bpHeadV c₁)) := by
    rw [h₂]
    rfl
  have houtHead : (flatBT (replaceScb c₀ c₁ c₂)).head? =
      some (.dsym v) := by
    cases s with
    | nil =>
        have hsame : (flatBT c₀).head? = (flatBT c₁).head? := by
          have hh := congrArg List.head? hd.1
          simpa [hc₁Head] using hh
        have hv : bpHeadV c₁ = v := by
          rw [hc₀Head, hc₁Head] at hsame
          simpa using hsame.symm
        have hout : (flatBT (replaceScb c₀ c₁ c₂)).head? =
            (flatBT c₂).head? := by
          have hh := congrArg List.head? hflat
          simpa [hc₂Head] using hh
        rw [hout, hc₂Head, hv]
    | cons x xs =>
        have hx : x = .dsym v := by
          have hh := congrArg List.head? hd.1
          simpa [hc₀Head] using hh.symm
        have hout : (flatBT (replaceScb c₀ c₁ c₂)).head? = some x := by
          simpa using congrArg List.head? hflat
        simpa [hx] using hout
  obtain ⟨p, hp⟩ :=
    replaceScb_principal hc₀ hc₀P hc₁ hc₁P hc₂ hc₂P hm
  rcases p with ⟨u, a⟩
  have huv : u = v := by
    rw [hp] at houtHead
    simpa [flatBT, flatBP] using houtHead
  subst u
  exact ⟨a, hp⟩

/-- A reduced mono translation is either zero or starts with the row-one
entry of its leftmost column. -/
theorem Trans_mono_leftend_form (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) :
    Trans M = BZero ∨
      ∃ t, Trans M = Dprin (entry M 1 0 : ℕ∞) t := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      have hM : TPS M := RTPS_TPS M hR
      have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
      by_cases hOne : Lng M = 1
      · obtain ⟨v, hMv⟩ := (one_column M hM).1 ⟨hOne, hR⟩
        subst M
        by_cases hv : v = 0
        · left
          subst v
          exact (Trans_preserves_zeroT [(0, 0)] (by simp [TPS])).1
            (by simp [zeroT, entry])
        · right
          have hR' : RTPS [(v, v)] := hR
          refine ⟨BZero, ?_⟩
          rw [Trans_eq_lengthAux [(v, v)] hR']
          have hred : reduced [(v, v)] = true := hR'
          simp [TransAux, lastIdx, entry, hv, BZero, hred]
      · have hlen : 1 < Lng M := by omega
        let P := Pred M
        have hPR : RTPS P := by simpa [P] using RTPS_Pred M hR
        have hPT : TPS P := RTPS_TPS P hPR
        have hPLen : Lng P = Lng M - 1 := by
          simpa [P] using length_Pred M hlen
        have hPLt : Lng P < n := by rw [hPLen, ← hn]; omega
        have heq := (Trans_Mark_mono_equations M hR hlen hmono).1
        by_cases ht₁ : Trans P = BZero
        · right
          have hzP : zeroT P = true :=
            (Trans_preserves_zeroT P hPT).2 ht₁
          have heP : entry P 1 0 = 0 := by
            simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hzP
            exact hzP.2
          have heM : entry M 1 0 = 0 := by
            calc
              entry M 1 0 = entry P 1 0 := by
                simpa [P] using (entry_Pred M 1 0 (by omega)).symm
              _ = 0 := heP
          refine ⟨Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero, ?_⟩
          simpa [P, ht₁, heM] using heq
        · right
          have hzP : zeroT P = false := by
            apply Bool.eq_false_of_not_eq_true
            intro hz
            exact ht₁ ((Trans_preserves_zeroT P hPT).1 hz)
          have hmonoP : monoT P = true := by
            by_cases hPOne : Lng P = 1
            · have hle : leR P 0 0 (Lng P - 1) = true := by
                simp [hPOne, leR, le0, le0Aux]
              simp [monoT, hzP, hle]
            · have hlong : 2 < Lng M := by omega
              exact monoT_Pred_long M hM hmono hlong
          rcases ih (Lng P) hPLt P hPR hmonoP rfl with hzero | ⟨a₀, houter⟩
          · exact (ht₁ hzero).elim
          · have hentry : entry P 1 0 = entry M 1 0 := by
              simpa [P] using entry_Pred M 1 0 (by omega)
            have hp : hasParent M 0 (Lng M - 1) = true :=
              mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
            let jm := Adm M (lastParent M)
            let c₁ := Mark P jm
            let c₂ := transC2Core M (bpHeadV c₁) (bpHeadT c₁)
            have hjm : Marked P jm := by
              simpa [P, jm, lastParent] using Marked_Pred_Adm M hM hlen hp
            have hc₁TB : c₁ ∈ T_B := by
              simpa [c₁] using Mark_mem_T_B P jm hPR hjm
            have hc₁Marked : (Trans P, c₁) ∈ MarkedB := by
              simpa [c₁] using Trans_Mark_mem_MarkedB P jm hPR hjm
            have hc₁P : ∃ p, c₁ = .trm [p] :=
              marked_component_principal ht₁ hc₁Marked
            have hc₂Facts := transC2Core_properties M c₁ hc₁TB hc₁P
            have hc₂Outer : ∃ a₂, c₂ = Dprin (bpHeadV c₁) a₂ := by
              simpa [c₂] using transC2Core_outer M (bpHeadV c₁) (bpHeadT c₁)
            obtain ⟨a₂, hc₂Outer⟩ := hc₂Outer
            have ht₁TB : Trans P ∈ T_B := Trans_mem_T_B P hPR
            have ht₁P : ∃ p, Trans P = .trm [p] := by
              refine ⟨.db (entry P 1 0 : ℕ∞) a₀, ?_⟩
              simpa [Dprin] using houter
            obtain ⟨a, hrep⟩ := replaceScb_outer_dprin
              ht₁TB ht₁P hc₁TB hc₁P hc₂Facts.1 hc₂Facts.2 hc₁Marked
              houter hc₂Outer
            refine ⟨a, ?_⟩
            calc
              Trans M = replaceScb (Trans P) c₁ c₂ := by
                simpa [P, c₁, c₂, ht₁] using heq
              _ = Dprin (entry P 1 0 : ℕ∞) a := hrep
              _ = Dprin (entry M 1 0 : ℕ∞) a := by rw [hentry]

private theorem not_isPTB_str_flat_zero : ¬ isPTB_str (flatBT BZero) := by
  rintro ⟨p, _hp, hflat⟩
  rcases p with ⟨u, t⟩
  simp [BZero, flatBT, flatBP] at hflat

/-- A proper mark has the pinned outer row-one index needed by the
`RightNodes` splitting argument. -/
theorem Mark_leftend_form_proper (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M) (hlt : m < Lng M - 1) :
    ∃ t, Mark M m = Dprin (entry M 1 m : ℕ∞) t := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  let S := seg M m (Lng M - 1)
  let N := Red S
  have hST : TPS S := by
    intro hnil
    have hz : Lng S = 0 := by simp [hnil]
    simp [S] at hz
    omega
  have hmonoS : monoT S = true := by
    simpa [S] using mono_ancestor_slice M m (Lng M - 1) hM hlt hm.2.2
  have hSnm : multiT S = false := by simp [multiT, hmonoS]
  have hNR : RTPS N := by
    simpa [N] using Red_nonmulti_RTPS S hST hSnm
  have hfacts := ancestor_slice_Red_IncrFirst M m (Lng M - 1)
    hR hlt (by omega) hm.2.2
  have hmonoN : monoT N = true := by simpa [S, N] using hfacts.2.1
  have hentryS : entry S 1 0 = entry M 1 m := by
    have hSpos : 0 < Lng S := List.length_pos_of_ne_nil hST
    simpa [S] using entry_seg M m (Lng M - 1) 1 0 hSpos
  have hentryN : entry N 1 0 = entry M 1 m := by
    have hread : S = IncrFirstN (entry M 0 m - entry M 1 m) N := by
      simpa [S, N] using hfacts.2.2
    have hsame : entry S 1 0 = entry N 1 0 := by
      rw [hread, entry_IncrFirstN_one]
    omega
  have hrepr := Mark_Trans_repr M m hm hR hlt
  have htransRed : Trans S = Trans N := by
    simpa [N] using Trans_Red S hST
  have hmarkN : Mark M m = Trans N := by simpa [S, htransRed] using hrepr
  rcases Trans_mono_leftend_form N hNR hmonoN with hzero | ⟨t, ht⟩
  · have hTransMNe : Trans M ≠ BZero := by
      have hzM : zeroT M = false := by simp [zeroT, hlen.ne']
      exact (Trans_Mark_invariant M hR).2.1 hzM
    have hmarked := Trans_Mark_mem_MarkedB M m hR hm
    rcases hmarked with ⟨s, b, hd⟩
    have hip : isPTB_str (flatBT (Mark M m)) := hd.2.1 hTransMNe
    exact (not_isPTB_str_flat_zero (by simpa [hmarkN, hzero] using hip)).elim
  · exact ⟨t, by simpa [hmarkN, hentryN] using ht⟩

/-- Corrected A47 form of the article corollary. -/
theorem RightNodes_Mark (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M)
    (hmpos : 0 < m) (hmlt : m < Lng M - 1) :
    ∃ a₀ a₁,
      RightNodes (Trans M) = a₀ ++ [entry M 1 m] ++ a₁ ∧
      RightNodes (Trans (seg M 0 m)) = a₀ ++ [entry M 1 m] ∧
      RightNodes (Mark M m) = [entry M 1 m] ++ a₁ := by
  obtain ⟨sb, hsb, _⟩ := Trans_Mark_seg M m hm hR hmpos hmlt
  rcases sb with ⟨s, b⟩
  have hdSeg := hsb.1
  have hdM := hsb.2
  obtain ⟨t, hmark⟩ := Mark_leftend_form_proper M m hm hR hmlt
  have ht : t ∈ T_B := by
    have hMarkTB := Mark_mem_T_B M m hR hm
    rw [hmark] at hMarkTB
    simpa [T_B, Dprin, dfree_BT, dfree_BPList, dfree_BP] using hMarkTB
  have hsegR : RTPS (seg M 0 m) :=
    RTPS_initial_slice M m hR (by omega)
  have hsegTB : Trans (seg M 0 m) ∈ T_B :=
    Trans_mem_T_B (seg M 0 m) hsegR
  have hb : ∀ x ∈ b, x = .rp := hdSeg.2.2
  obtain ⟨aa, haa, _⟩ := rightNodes_subexpr_general
    ht hb hsegTB hdSeg.1
  rcases aa with ⟨a₀, a₁⟩
  have hflatSub := flat_spineSub_at_dprin_occurrence hdSeg.1 hb (c := t)
  have hsub : spineSub (Trans (seg M 0 m)) t = Trans M := by
    apply flatBT_injective
    rw [hflatSub, hdM.1, hmark]
  refine ⟨a₀, a₁, ?_, ?_, ?_⟩
  · simpa [hsub] using haa.1
  · exact haa.2.1
  · simpa [hmark] using haa.2.2

theorem m_7_4_RightNodes_Mark (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M)
    (hmpos : 0 < m) (hmlt : m < Lng M - 1) :
    ∃ a₀ a₁,
      RightNodes (Trans M) = a₀ ++ [entry M 1 m] ++ a₁ ∧
      RightNodes (Trans (seg M 0 m)) = a₀ ++ [entry M 1 m] ∧
      RightNodes (Mark M m) = [entry M 1 m] ++ a₁ :=
  RightNodes_Mark M m hm hR hmpos hmlt

#print axioms Trans_mono_leftend_form
#print axioms Mark_leftend_form_proper
#print axioms RightNodes_Mark

end PSS
