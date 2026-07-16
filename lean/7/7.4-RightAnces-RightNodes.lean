import «7».«7.4-RightNodes-Mark»

/-!
# §7.4 命題（`RightNodes` と `RightAnces` の関係）

- 原文: `isabelle/pss_paper.thy` の `p_7_4_RightAnces_RightNodes`
- Isabelle: `m_7_4_RightAnces_RightNodes`
- 定式化する範囲: 訂正後の `RTPS` 上の形
-/

namespace PSS

/-! ## The article's recursive right-ancestor list -/

def RightAncesAux : ℕ → PS → List ℕ
  | 0, _ => []
  | fuel + 1, M =>
      if !reduced M then
        RightAncesAux fuel (Red M)
      else
        let j₁ := Lng M - 1
        if j₁ == 0 then
          if M.getD 0 (0, 0) == (0, 0) then [] else [entry M 1 0]
        else if monoT M then
          if zeroT (Pred M) then
            [0, entry M 1 j₁]
          else
            let jp := parent M 0 j₁
            let jm := Adm M jp
            let a := if zeroT (seg M 0 jm) then [0]
              else RightAncesAux fuel (seg M 0 jm)
            if transCondI M || transCondIII M || transCondV M || transCondVI M
            then a ++ [entry M 1 j₁]
            else a ++ [entry M 1 jp, entry M 1 j₁]
        else
          let J := (P M).getD ((P M).length - 1) []
          if J == [(0, 0)] then [0] else RightAncesAux fuel J

def RightAnces (M : PS) : List ℕ := RightAncesAux (transFuel M) M

theorem RightAncesAux_RTPS_equation (fuel : ℕ) (M : PS) (hR : RTPS M) :
    RightAncesAux (fuel + 1) M =
      let j₁ := Lng M - 1
      if j₁ == 0 then
        if M.getD 0 (0, 0) == (0, 0) then [] else [entry M 1 0]
      else if monoT M then
        if zeroT (Pred M) then
          [0, entry M 1 j₁]
        else
          let jp := parent M 0 j₁
          let jm := Adm M jp
          let a := if zeroT (seg M 0 jm) then [0]
            else RightAncesAux fuel (seg M 0 jm)
          if transCondI M || transCondIII M || transCondV M || transCondVI M
          then a ++ [entry M 1 j₁]
          else a ++ [entry M 1 jp, entry M 1 j₁]
      else
        let J := (P M).getD ((P M).length - 1) []
        if J == [(0, 0)] then [0] else RightAncesAux fuel J := by
  simp [RightAncesAux, show reduced M = true from hR]

/-! ## `RightNodes` structural helpers -/

private theorem rightNodesList_append_right (as bs : List BP) (hbs : bs ≠ []) :
    rightNodesList (as ++ bs) = rightNodesList bs := by
  induction as with
  | nil => simp
  | cons a as ih =>
      cases as with
      | nil =>
          cases bs with
          | nil => exact (hbs rfl).elim
          | cons b bs =>
              cases bs <;> simp [rightNodesList]
      | cons a' as =>
          exact ih

theorem RightNodes_addBT_right (a b : BT) (hb : b ≠ BZero) :
    RightNodes (addBT a b) = RightNodes b := by
  rcases a with ⟨as⟩
  rcases b with ⟨bs⟩
  have hbs : bs ≠ [] := by
    intro hz
    subst bs
    exact hb rfl
  simpa [addBT, RightNodes] using rightNodesList_append_right as bs hbs

@[simp] theorem RightNodes_Dprin (v : ℕ∞) (t : BT) :
    RightNodes (Dprin v t) = v.toNat :: RightNodes t := rfl

@[simp] theorem RightNodes_BZero : RightNodes BZero = [] := rfl

@[simp] theorem RightNodes_addBT_Dprin (a t : BT) (v : ℕ∞) :
    RightNodes (addBT a (Dprin v t)) = v.toNat :: RightNodes t := by
  rw [RightNodes_addBT_right a (Dprin v t) (by simp [Dprin, BZero])]
  simp [Dprin, RightNodes, rightNodesList, rightNodesBP]

theorem RightNodes_transC2_tail (M : PS) :
    RightNodes (transC2 M) = (transV M).toNat ::
      (if transCondI M || transCondIII M || transCondV M || transCondVI M
       then [entry M 1 (transJ1 M)]
       else [entry M 1 (transJ0 M), entry M 1 (transJ1 M)]) := by
  by_cases h135 :
      (transCondI M || transCondIII M || transCondV M) = true
  · simp [transC2, transC2Core, h135, transJ1]
  · by_cases hVI : transCondVI M = true
    · simp [transC2, transC2Core, h135, hVI, transJ1]
    · by_cases ht₂ : transT2 M = BZero
      · simp [transC2, transC2Core, h135, hVI, ht₂, transJ1, transJ0]
      · have ht₂b : (transT2 M == BZero) = false := by
          simpa [beq_iff_eq] using ht₂
        simp [transC2, transC2Core, h135, hVI, ht₂b, transJ1, transJ0]

private theorem Mark_leftend_form_of_nonzero_trans (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M) (hTrans : Trans M ≠ BZero) :
    ∃ t, Mark M m = Dprin (entry M 1 m : ℕ∞) t := by
  have hlast := Marked_index_le_last hm
  by_cases hlt : m < Lng M - 1
  · exact Mark_leftend_form_proper M m hm hR hlt
  · have hmLast : m = Lng M - 1 := by omega
    have hM : TPS M := RTPS_TPS M hR
    have hz : zeroT M = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hz'
      exact hTrans ((Trans_preserves_zeroT M hM).1 hz')
    refine ⟨BZero, ?_⟩
    rw [hmLast]
    exact Mark_rightmost1_forward M hR hz

private theorem RightNodes_Trans_one (M : PS) (hR : RTPS M)
    (hOne : Lng M = 1) :
    RightNodes (Trans M) =
      if zeroT M then [] else [entry M 1 0] := by
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨v, hMv⟩ := (one_column M hM).1 ⟨hOne, hR⟩
  subst M
  by_cases hv : v = 0
  · subst v
    simp [zeroT, entry, BZero, RightNodes, rightNodesList,
      (Trans_preserves_zeroT [(0, 0)] (by simp [TPS])).1]
  · have hR' : RTPS [(v, v)] := hR
    rw [Trans_eq_lengthAux [(v, v)] hR']
    have hred : reduced [(v, v)] = true := hR'
    simp [TransAux, lastIdx, entry, hv, BZero, hred, zeroT,
      Dprin, RightNodes, rightNodesList, rightNodesBP]

/-! ## Correspondence -/

theorem RightAncesAux_eq_RightNodes_Trans (M : PS) (fuel : ℕ)
    (hR : RTPS M) (hfuel : Lng M ≤ fuel) :
    RightAncesAux fuel M = RightNodes (Trans M) := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M fuel with
  | h n ih =>
      have hM : TPS M := RTPS_TPS M hR
      have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
      cases fuel with
      | zero => omega
      | succ f =>
          by_cases hOne : Lng M = 1
          · obtain ⟨v, hMv⟩ := (one_column M hM).1 ⟨hOne, hR⟩
            subst M
            rw [RightAncesAux_RTPS_equation f [(v, v)] hR]
            simpa [zeroT, entry] using
              (RightNodes_Trans_one [(v, v)] hR (by simp)).symm
          · have hlen : 1 < Lng M := by omega
            have hj₁ne : Lng M - 1 ≠ 0 := by omega
            by_cases hmono : monoT M = true
            · let j₁ := Lng M - 1
              let jp := parent M 0 j₁
              let jm := Adm M jp
              let S := seg M 0 jm
              let tail :=
                if transCondI M || transCondIII M || transCondV M ||
                    transCondVI M
                then [entry M 1 j₁]
                else [entry M 1 jp, entry M 1 j₁]
              let P₁ := Pred M
              have hPR : RTPS P₁ := by simpa [P₁] using RTPS_Pred M hR
              have hPT : TPS P₁ := RTPS_TPS P₁ hPR
              by_cases hzP : zeroT P₁ = true
              · have hRA : RightAncesAux (f + 1) M =
                    [0, entry M 1 j₁] := by
                  rw [RightAncesAux_RTPS_equation f M hR]
                  simp [j₁, hj₁ne, hmono, P₁, hzP]
                have hTP : Trans P₁ = BZero :=
                  (Trans_preserves_zeroT P₁ hPT).1 hzP
                have hTrans := (Trans_Mark_mono_equations M hR hlen hmono).1
                rw [hRA]
                simpa [P₁, j₁, hTP] using congrArg RightNodes hTrans.symm
              · have hzPfalse : zeroT P₁ = false :=
                  Bool.eq_false_of_not_eq_true hzP
                have hTPne : Trans P₁ ≠ BZero := by
                  intro hzero
                  exact hzP ((Trans_preserves_zeroT P₁ hPT).2 hzero)
                have hp : hasParent M 0 j₁ = true := by
                  simpa [j₁] using mono_hasParent_row0 M hM hmono
                    (Lng M - 1) (by omega) (by omega)
                have hnext : nextR M 0 jp j₁ = true := by
                  simpa [jp] using nextR_parent0_of_hasParent M j₁ hp
                have hjplt : jp < j₁ :=
                  (nextR_implies_row0 M 0 jp j₁ hnext).1
                have hjmle : jm ≤ jp := by simpa [jm] using Adm_le M jp
                have hjmlt : jm < j₁ := hjmle.trans_lt hjplt
                have hjmLast : jm ≤ Lng M - 1 := by simpa [j₁] using hjmlt.le
                have hSR : RTPS S := by
                  simpa [S] using RTPS_initial_slice M jm hR hjmLast
                have hSLen : Lng S = jm + 1 := by
                  simp [S]
                have hSLt : Lng S < n := by rw [hSLen, ← hn]; omega
                have hfS : Lng S ≤ f := by omega
                have hIHS : RightAncesAux f S = RightNodes (Trans S) :=
                  ih (Lng S) hSLt S f hSR hfS rfl
                have hAdm : adm M jm = true := by simpa [jm] using Adm_adm M jp
                have hjpBound : jp ≤ Lng M - 1 := by
                  simpa [j₁] using hjplt.le
                have hrow1 : leR M 1 jm jp = true := by
                  simpa [jm] using adm_row1_ancestry M jp hM hjpBound
                have hrow0 : leR M 0 jm jp = true :=
                  row1_implies_row0 M jm jp hM hrow1
                have hjpLast : leR M 0 jp (Lng M - 1) = true := by
                  simpa [j₁] using nextR0_leR M jp j₁ hnext
                have hmM : Marked M jm :=
                  ⟨hM, hAdm, row0_transitive M jm jp (Lng M - 1)
                    hM hrow0 hjpLast⟩
                have hmPred : Marked P₁ jm := by
                  simpa [P₁, j₁, jp, jm] using
                    Marked_Pred_Adm M hM hlen hp
                obtain ⟨body₁, hmarkPred⟩ :=
                  Mark_leftend_form_of_nonzero_trans P₁ jm hmPred hPR hTPne
                have hentryPred : entry P₁ 1 jm = entry M 1 jm := by
                  simpa [P₁] using entry_Pred M 1 jm (by simpa [j₁] using hjmlt)
                have hv : (transV M).toNat = entry M 1 jm := by
                  have hc₁eq : transC1 M = Mark P₁ jm := by
                    simp [transC1, transJm1, transJ0, P₁, j₁, jp, jm,
                      lastParent, lastIdx]
                  have hv' : transV M = (entry P₁ 1 jm : ℕ∞) := by
                    rw [transV, hc₁eq, hmarkPred]
                    rfl
                  simp [hv', hentryPred]
                have hMarkC2 : Mark M jm = transC2 M := by
                  simpa [transJm1, transJ0, j₁, jp, jm] using
                    Mark_transJm1_eq_transC2 M hR hmono hlen hTPne
                have hRnC2 : RightNodes (transC2 M) =
                    entry M 1 jm :: tail := by
                  rw [RightNodes_transC2_tail M, hv]
                  simp [tail, transJ1, transJ0, lastIdx, lastParent, j₁, jp]
                have hRA : RightAncesAux (f + 1) M =
                    (if zeroT S then [0] else RightAncesAux f S) ++ tail := by
                  rw [RightAncesAux_RTPS_equation f M hR]
                  by_cases hc :
                      (transCondI M || transCondIII M || transCondV M ||
                        transCondVI M) = true
                  · simp [j₁, hj₁ne, hmono, P₁, hzPfalse, jp, jm, S,
                      tail, hc]
                  · simp [j₁, hj₁ne, hmono, P₁, hzPfalse, jp, jm, S,
                      tail, hc]
                by_cases hjm0 : jm = 0
                · have hM0 : Marked M 0 := by simpa [hjm0] using hmM
                  have hTransC2 : Trans M = transC2 M := by
                    rw [← hMarkC2, hjm0]
                    exact (Mark_zero_eq_Trans M hR hM0).symm
                  have hprefix :
                      (if zeroT S then [0] else RightAncesAux f S) =
                        [entry M 1 jm] := by
                    by_cases hzS : zeroT S = true
                    · have heS : entry S 1 0 = 0 := by
                        simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hzS
                        exact hzS.2
                      have heM : entry M 1 jm = 0 := by
                        have hSpos : 0 < Lng S := by rw [hSLen]; omega
                        have he := entry_seg M 0 jm 1 0 hSpos
                        calc
                          entry M 1 jm = entry S 1 0 := by
                            simpa [S, hjm0] using he.symm
                          _ = 0 := heS
                      simp [hzS, heM]
                    · have hzSf : zeroT S = false :=
                        Bool.eq_false_of_not_eq_true hzS
                      have hOneS : Lng S = 1 := by simp [hSLen, hjm0]
                      have hRnS := RightNodes_Trans_one S hSR hOneS
                      have hentryS : entry S 1 0 = entry M 1 jm := by
                        have hSpos : 0 < Lng S := by rw [hSLen]; omega
                        simpa [S, hjm0] using entry_seg M 0 jm 1 0 hSpos
                      rw [hIHS]
                      rw [hRnS]
                      simp [hzSf, hentryS]
                  rw [hRA, hprefix, hTransC2, hRnC2]
                  simp
                · have hjmpos : 0 < jm := Nat.pos_of_ne_zero hjm0
                  have hzSf : zeroT S = false := by
                    apply Bool.eq_false_of_not_eq_true
                    intro hzS
                    have hOneS : Lng S = 1 := by
                      simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hzS
                      exact hzS.1
                    rw [hSLen] at hOneS
                    omega
                  obtain ⟨a₀, a₁, hTM, hTS, hMark⟩ :=
                    RightNodes_Mark M jm hmM hR hjmpos (by simpa [j₁] using hjmlt)
                  have ha₁ : a₁ = tail := by
                    have hMarkTail : RightNodes (Mark M jm) =
                        [entry M 1 jm] ++ tail := by
                      rw [hMarkC2]
                      simpa using hRnC2
                    exact List.append_cancel_left (hMark.symm.trans hMarkTail)
                  rw [hRA, hzSf, hIHS]
                  calc
                    RightNodes (Trans S) ++ tail =
                        (a₀ ++ [entry M 1 jm]) ++ a₁ := by rw [hTS, ha₁]
                    _ = RightNodes (Trans M) := by simpa using hTM.symm
            · have hzM : zeroT M = false := by simp [zeroT, hlen.ne']
              have hmulti : multiT M = true := by simp [multiT, hzM, hmono]
              let A := M.take (Pcut M)
              let J := M.drop (Pcut M)
              have hlast := trans_multi_last_component M hM hmulti
              have hcut := Pcut_props M hlen
              have hJLen : Lng J = Lng M - Pcut M := by simp [J]
              have hJLt : Lng J < n := by rw [hJLen, ← hn]; omega
              have hPne : P M ≠ [] := P_nonempty M
              have hidx : (P M).length - 1 < (P M).length := by
                have := List.length_pos_of_ne_nil hPne
                omega
              have hJR : RTPS J := by
                have hh := (RTPS_iff_P_components M hM).1 hR
                  ((P M).length - 1) hidx
                rw [hlast.1] at hh
                simpa [J] using hh
              have hfJ : Lng J ≤ f := by omega
              have hIHJ : RightAncesAux f J = RightNodes (Trans J) :=
                ih (Lng J) hJLt J f hJR hfJ rfl
              have hRA : RightAncesAux (f + 1) M =
                  if J == [(0, 0)] then [0] else RightAncesAux f J := by
                rw [RightAncesAux_RTPS_equation f M hR]
                simp [hj₁ne, hmono]
                have hopt :
                    (P M)[(P M).length - 1]?.getD [] = J := by
                  simpa [J] using hlast.1
                rw [hopt]
              have hTrans := (Trans_Mark_multi_equations M hR hmulti).1
              by_cases hJzero : J = [(0, 0)]
              · rw [hRA]
                simp [hJzero, J] at hTrans ⊢
                rw [hTrans, RightNodes_addBT_right]
                · simp
                · simp [Dprin, BZero]
              · have hzJ : zeroT J = false := by
                  apply Bool.eq_false_of_not_eq_true
                  intro hz
                  have hred0 := Red_zero_mr J hz
                  have hfix := RTPS_Red_eq J hJR
                  exact hJzero (hfix.symm.trans hred0)
                have hJT : TPS J := RTPS_TPS J hJR
                have hTJne : Trans J ≠ BZero :=
                  fun ht => Bool.false_ne_true
                    (hzJ.symm.trans ((Trans_preserves_zeroT J hJT).2 ht))
                rw [hRA]
                simp [hJzero]
                rw [hIHJ]
                have hTrans' : Trans M = addBT (Trans A) (Trans J) := by
                  simpa [A, J, hJzero] using hTrans
                rw [hTrans', RightNodes_addBT_right _ _ hTJne]

/-- Corrected `RTPS` form of the article proposition. -/
theorem RightAnces_RightNodes (M : PS) (hR : RTPS M) :
    RightAnces M = RightNodes (Trans M) := by
  exact RightAncesAux_eq_RightNodes_Trans M (transFuel M) hR
    (transFuel_ge_length M)

theorem m_7_4_RightAnces_RightNodes (M : PS) (hR : RTPS M) :
    RightAnces M = RightNodes (Trans M) :=
  RightAnces_RightNodes M hR

#print axioms RightAnces_RightNodes

end PSS
