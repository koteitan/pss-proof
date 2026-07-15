import «7».«7.3-Trans-preserves-monoT»
import «7».«7.4-Adm-nextAdm»

/-!
# §7.4 系（`Trans` の `Mark` と `Pred` による表示）

- 原文: `tmp/content.md` §7.4
- 訂正: A46（定義域を `TPS` から `RTPS` へ制限）
- Isabelle: `m_7_4_Trans_Mark_Pred`
-/

namespace PSS

private theorem scb_decomp_self_74 {t : BT}
    (h : isPTB_str (flatBT t)) :
    scb_decomp t [] (flatBT t) [] := by
  simp [scb_decomp, h]

private theorem markedBHostNeZero_74 {t c : BT}
    (hcP : ∃ p, c = .trm [p]) (hm : (t, c) ∈ MarkedB) : t ≠ BZero := by
  obtain ⟨p, rfl⟩ := hcP
  rcases p with ⟨u, a⟩
  rcases hm with ⟨s, b, hd⟩
  intro ht
  subst t
  have hlen := congrArg List.length hd.1
  have hapos : 0 < (flatBT a).length := by
    rcases a with ⟨ps⟩
    cases ps with
    | nil => simp [flatBT]
    | cons p ps =>
        cases ps with
        | nil => rcases p with ⟨v, z⟩; simp [flatBT, flatBP]
        | cons q qs => simp [flatBT]
  simp only [BZero, flatBT, flatBP, List.length_cons,
    List.length_append, List.length_nil, Nat.zero_add] at hlen
  omega

/-- Prefix used when lifting an scb position through Buchholz addition. -/
def liftScbPrefix (Y : BT) (s : List Sym) : List Sym :=
  match untrm Y with
  | [] => s
  | p :: ps => .lp :: flatBP p ++ flatBPTail ps ++ [.cm] ++ s

private theorem flatBPTail_append_singleton_74 (ps : List BP) (p : BP) :
    flatBPTail (ps ++ [p]) = flatBPTail ps ++ (.cm :: flatBP p) := by
  induction ps with
  | nil => simp [flatBPTail]
  | cons q qs ih => simp [flatBPTail, ih, List.append_assoc]

private theorem scb_addBT_left_74 {X Y : BT} {s c b : List Sym}
    (hd : scb_decomp X s c b)
    (hXone : (untrm X).length = 1)
    (hYne : untrm Y ≠ []) :
    scb_decomp (addBT Y X) (liftScbPrefix Y s) c (b ++ [.rp]) := by
  rcases X with ⟨xs⟩
  rcases Y with ⟨ys⟩
  simp only [untrm] at hXone hYne
  cases xs with
  | nil => simp at hXone
  | cons x xs =>
      cases xs with
      | nil =>
          cases ys with
          | nil => exact (hYne rfl).elim
          | cons y ys =>
              rcases hd with ⟨hflat, hprincipal, htail⟩
              have hXne : BT.trm [x] ≠ BZero := by simp [BZero]
              have hc : isPTB_str c := hprincipal hXne
              have hflat' : flatBP x = s ++ c ++ b := by
                simpa [flatBT] using hflat
              refine ⟨?_, ?_, ?_⟩
              · cases ys <;>
                  simp [addBT, flatBT, flatBPTail, liftScbPrefix, untrm,
                    flatBPTail_append_singleton_74, hflat', List.append_assoc]
              · intro _
                exact hc
              · intro z hz
                rcases List.mem_append.mp hz with hz | hz
                · exact htail z hz
                · simpa using hz
      | cons x' xs => simp at hXone

/-- In the multi branch, `Pred` acts inside the final `P` component also for
the marked translation. -/
theorem Mark_Pred_multi_last (M : PS) (m : ℕ) (hR : RTPS M)
    (hmulti : multiT M = true)
    (hJlen : 1 < Lng (M.drop (Pcut M))) :
    Mark (Pred M) m =
      if Pred (M.drop (Pcut M)) == [(0, 0)] then Dprin 0 BZero
      else Mark (Pred (M.drop (Pcut M))) (m - Pcut M) := by
  let A := M.take (Pcut M)
  let J := M.drop (Pcut M)
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := multi_length_fseq M hM hmulti
  have hcut := Pcut_props M hlen
  have hlast := P_last_multi M hmulti hlen
  have hlastJ : (P M).getLastD [] = J := by
    simpa [J] using hlast.1
  have hbutA : (P M).dropLast = P A := by
    simpa [A] using hlast.2
  have hJlength : Lng J = Lng M - Pcut M := by simp [J]
  have hcutLast : Pcut M < Lng M - 1 := by
    change 1 < Lng J at hJlen
    omega
  have hsum : Pcut M + (Lng J - 1) = Lng M - 1 := by
    rw [hJlength]
    omega
  have hpredSplit : Pred M = A ++ Pred J := by
    have hpredM : Pred M = M.take (Lng M - 1) := Pred_eq_take M hlen
    have hpredJ : Pred J = J.take (Lng J - 1) := Pred_eq_take J hJlen
    rw [hpredM, hpredJ]
    symm
    change M.take (Pcut M) ++
        (M.drop (Pcut M)).take (Lng J - 1) = M.take (Lng M - 1)
    rw [← List.take_add, hsum]
  have hPpred : P (Pred M) = P A ++ [Pred J] := by
    have hlastLenNe : Lng ((P M).getLastD []) ≠ 1 := by
      rw [hlastJ]
      exact Nat.ne_of_gt hJlen
    rw [P_Pred_multi M hM hmulti, if_neg hlastLenNe, hlastJ, hbutA]
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredT : TPS (Pred M) := RTPS_TPS (Pred M) hpredR
  have hPAlen : 0 < (P A).length := List.length_pos_of_ne_nil (P_nonempty A)
  have hPpredLen : 1 < (P (Pred M)).length := by
    rw [hPpred]
    simp
    omega
  have hpredMulti : multiT (Pred M) = true :=
    (P_components_multi_iff (Pred M) hpredT).2 hPpredLen
  have hpredLen : 1 < Lng (Pred M) :=
    multi_length_fseq (Pred M) hpredT hpredMulti
  have hpredLast := P_last_multi (Pred M) hpredMulti hpredLen
  have hdropPred : (Pred M).drop (Pcut (Pred M)) = Pred J := by
    have hlastVal : (P (Pred M)).getLastD [] = Pred J := by
      rw [hPpred]
      simp
    exact hpredLast.1.symm.trans hlastVal
  have htakePred : (Pred M).take (Pcut (Pred M)) = A := by
    have happ := List.take_append_drop (Pcut (Pred M)) (Pred M)
    rw [hdropPred] at happ
    exact List.append_cancel_right (happ.trans hpredSplit)
  have hPcutPred : Pcut (Pred M) = Pcut M := by
    have hcPred : Pcut (Pred M) ≤ Lng (Pred M) := by
      have hc := Pcut_props (Pred M) hpredLen
      omega
    have hcM : Pcut M ≤ Lng M := by omega
    have hlenEq := congrArg Lng htakePred
    simpa [List.length_take, Nat.min_eq_left hcPred, A,
      Nat.min_eq_left hcM] using hlenEq
  have heq := (Trans_Mark_multi_equations (Pred M) hpredR hpredMulti).2 m
  rw [hdropPred, hPcutPred] at heq
  simpa [A, J] using heq

private theorem addBT_zero_left_74 (X : BT) : addBT BZero X = X := by
  rcases X with ⟨xs⟩
  simp [addBT, BZero]

private theorem RTPS_zeroT_eq_singleton_74 (M : PS)
    (hR : RTPS M) (hz : zeroT M = true) : M = [(0, 0)] := by
  have hM : TPS M := RTPS_TPS M hR
  have hL : Lng M = 1 := by
    have hh := hz
    simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
    exact hh.1
  obtain ⟨v, rfl⟩ := (one_column M hM).1 ⟨hL, hR⟩
  have hv : v = 0 := by
    simpa [zeroT, entry] using hz
  simp [hv]

private theorem Trans_ne_zero_of_not_singleton_74 (M : PS)
    (hR : RTPS M) (hne : M ≠ [(0, 0)]) : Trans M ≠ BZero := by
  intro ht
  have hz := (Trans_preserves_zeroT M (RTPS_TPS M hR)).2 ht
  exact hne (RTPS_zeroT_eq_singleton_74 M hR hz)

private theorem Trans_Mark_Pred_exists (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M) (hmlt : m < Lng M - 1) :
    ∃ s b,
      scb_decomp (Trans (Pred M)) s (flatBT (Mark (Pred M) m)) b ∧
      scb_decomp (Trans M) s (flatBT (Mark M m)) b := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M m with
  | h n ih =>
      have hM : TPS M := RTPS_TPS M hR
      have hlen : 1 < Lng M := by omega
      have hpredR : RTPS (Pred M) := RTPS_Pred M hR
      have hpredM : TPS (Pred M) := RTPS_TPS (Pred M) hpredR
      have hmPred : Marked (Pred M) m :=
        Marked_Pred M m hM hlen hm hmlt
      have hInvPred := Trans_Mark_mem_MarkedB (Pred M) m hpredR hmPred
      obtain ⟨s₀, b₀, hd₀⟩ := hInvPred
      by_cases hmono : monoT M = true
      · have heq := Trans_Mark_mono_equations M hR hlen hmono
        by_cases ht₁zero : Trans (Pred M) = BZero
        · have hzPred : zeroT (Pred M) = true :=
            (Trans_preserves_zeroT (Pred M) hpredM).2 ht₁zero
          have hpredEq : Pred M = [(0, 0)] :=
            RTPS_zeroT_eq_singleton_74 (Pred M) hpredR hzPred
          have hpredLen := length_Pred M hlen
          have hMtwo : Lng M = 2 := by simp [hpredEq] at hpredLen; omega
          have hm0 : m = 0 := by omega
          have hmarkPred : Mark (Pred M) m = BZero := by
            rw [hpredEq, hm0, Mark_eq_lengthAux [(0, 0)] 0]
            · simp [MarkAux, lastIdx, BZero]
            · simpa [hpredEq] using hpredR
          have hTrans : Trans M =
              Dprin 0 (Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero) := by
            simpa [ht₁zero] using heq.1
          have hMark : Mark M m = Trans M := by
            rw [hTrans]
            simpa [hm0, ht₁zero] using heq.2 m
          have hTransP : ∃ p, Trans M = .trm [p] := by
            rw [hTrans]
            exact ⟨_, rfl⟩
          have hself : scb_decomp (Trans M) [] (flatBT (Trans M)) [] :=
            scb_decomp_self_74
              (principal_flat_properties (Trans_mem_T_B M hR) hTransP).1
          refine ⟨[], [], ?_, ?_⟩
          · simp [ht₁zero, hmarkPred, scb_decomp, BZero]
          · simpa [hMark] using hself
        · let jp := lastParent M
          let t₁ := Trans (Pred M)
          let c₁ := Mark (Pred M) (Adm M jp)
          let c₂ := transC2Core M (bpHeadV c₁) (bpHeadT c₁)
          let c₀ := Mark (Pred M) m
          have hp : hasParent M 0 (Lng M - 1) = true :=
            mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
          have hc₁Marked : Marked (Pred M) (Adm M jp) := by
            simpa [jp] using Marked_Pred_Adm M hM hlen hp
          have ht₁TB : t₁ ∈ T_B := by
            simpa [t₁] using Trans_mem_T_B (Pred M) hpredR
          have hc₁TB : c₁ ∈ T_B := by
            simpa [c₁] using Mark_mem_T_B (Pred M) _ hpredR hc₁Marked
          have ht₁c₁ : (t₁, c₁) ∈ MarkedB := by
            simpa [t₁, c₁] using
              Trans_Mark_mem_MarkedB (Pred M) _ hpredR hc₁Marked
          have hc₁P : ∃ p, c₁ = .trm [p] :=
            marked_component_principal (by simpa [t₁] using ht₁zero) ht₁c₁
          have hc₂Facts := transC2Core_properties M c₁ hc₁TB hc₁P
          have hc₂TB : c₂ ∈ T_B := by simpa [c₂] using hc₂Facts.1
          have hc₂P : ∃ p, c₂ = .trm [p] := by simpa [c₂] using hc₂Facts.2
          have hc₀TB : c₀ ∈ T_B := by
            simpa [c₀] using Mark_mem_T_B (Pred M) m hpredR hmPred
          have ht₁c₀ : (t₁, c₀) ∈ MarkedB := by
            simpa [t₁, c₀] using
              Trans_Mark_mem_MarkedB (Pred M) m hpredR hmPred
          have hc₀P : ∃ p, c₀ = .trm [p] :=
            marked_component_principal (by simpa [t₁] using ht₁zero) ht₁c₀
          have hmjp : m ≤ jp := by
            simpa [jp, lastParent] using
              marked_le_lastParent M hm hmono hlen hmlt
          have hmAdm : m ≤ Adm M jp := Adm_max M m jp hm.2.1 hmjp
          have hc₀c₁ : (c₀, c₁) ∈ MarkedB := by
            simpa [c₀, c₁] using
              Mark_MarkedB_nest (Pred M) m (Adm M jp)
                hmPred hc₁Marked hmAdm hpredR
          have hTrans : Trans M = replaceScb t₁ c₁ c₂ := by
            simpa [t₁, jp, c₁, c₂, ht₁zero] using heq.1
          have hrepFacts := replaceScb_preserves_marked
            hc₀TB hc₁TB hc₁P hc₂TB hc₂P hc₀c₁
          have hrepP := replaceScb_principal
            hc₀TB hc₀P hc₁TB hc₁P hc₂TB hc₂P hc₀c₁
          have hrepNe : replaceScb c₀ c₁ c₂ ≠ BZero :=
            markedBHostNeZero_74 hc₂P hrepFacts.2
          have hMark : Mark M m = replaceScb c₀ c₁ c₂ := by
            have hmltLast : m < lastIdx M := by
              simpa [lastIdx] using hmlt
            cases hhead : (scbContexts c₀ (flatBT c₁)).head? with
            | none =>
                have hzrep : replaceScb c₀ c₁ c₂ = BZero := by
                  simp [replaceScb, hhead]
                exact (hrepNe hzrep).elim
            | some sb =>
                rcases sb with ⟨s, b⟩
                have hraw := heq.2 m
                simp [jp, c₁, c₀, ht₁zero, hmltLast, hhead] at hraw
                simpa [replaceScb, hhead] using hraw
          obtain ⟨sT, bT, hdT, hflatT, _⟩ :=
            replaceScb_spec ht₁TB hc₁TB hc₁P hc₂TB hc₂P ht₁c₁
          obtain ⟨sI, bI, hdI, hflatI, _⟩ :=
            replaceScb_spec hc₀TB hc₁TB hc₁P hc₂TB hc₂P hc₀c₁
          have hd₀' : scb_decomp t₁ s₀ (flatBT c₀) b₀ := by
            simpa [t₁, c₀] using hd₀
          have hcomp :
              scb_decomp t₁ (s₀ ++ sI) (flatBT c₁) (bI ++ b₀) :=
            scb_compose t₁ c₀ s₀ sI (flatBT c₁) bI b₀ hc₀P hd₀' hdI
          have hctx : sT = s₀ ++ sI ∧ bT = bI ++ b₀ :=
            scb_unique_decomp_unconditional t₁ sT (s₀ ++ sI)
              (flatBT c₁) bT (bI ++ b₀) hdT hcomp
          have hflat : flatBT (Trans M) =
              s₀ ++ flatBT (Mark M m) ++ b₀ := by
            rw [hTrans, hMark, hflatT, hflatI, hctx.1, hctx.2]
            simp [List.append_assoc]
          refine ⟨s₀, b₀, hd₀, hflat, ?_, hd₀.2.2⟩
          intro _
          rw [hMark]
          exact (principal_flat_properties hrepFacts.1 hrepP).1
      · have hmonoFalse : monoT M = false :=
          Bool.eq_false_of_not_eq_true hmono
        have hzero : zeroT M = false := by
          simp [zeroT]
          omega
        have hmulti : multiT M = true := by
          simp [multiT, hzero, hmonoFalse]
        let A := M.take (Pcut M)
        let J := M.drop (Pcut M)
        have hcut := Pcut_props M hlen
        have hJlength : Lng J = Lng M - Pcut M := by simp [J]
        have hmParts := multi_Marked_last_component M m hM hmulti hm
        have hcutm : Pcut M ≤ m := hmParts.1
        have hmJ : Marked J (m - Pcut M) := by
          simpa [J] using hmParts.2
        have hJlen : 1 < Lng J := by rw [hJlength]; omega
        have hJlt : Lng J < n := by rw [hJlength, ← hn]; omega
        have hmJlt : m - Pcut M < Lng J - 1 := by
          rw [hJlength]
          omega
        have hlast := (trans_multi_last_component M hM hmulti).1
        have hPne : P M ≠ [] := P_nonempty M
        have hidx : (P M).length - 1 < (P M).length := by
          have := List.length_pos_of_ne_nil hPne
          omega
        have hJR : RTPS J := by
          have hh := (RTPS_iff_P_components M hM).1 hR
            ((P M).length - 1) hidx
          dsimp [J]
          rw [← hlast]
          exact hh
        have hJT : TPS J := RTPS_TPS J hJR
        have hJne00 : J ≠ [(0, 0)] := by
          intro hbad
          rw [hbad] at hJlen
          simp at hJlen
        have hlastMem : (P M).getLastD [] ∈ P M := by
          cases hPM : P M with
          | nil => exact (hPne hPM).elim
          | cons Q Qs => simp [List.getLastD]
        have hJmem : J ∈ P M := by
          have hlastGet : (P M).getLastD [] = J := by
            simpa [J] using (P_last_multi M hmulti hlen).1
          rw [hlastGet] at hlastMem
          exact hlastMem
        have hJnonmulti := P_components_nonmulti M hM J hJmem
        have hJzeroFalse : zeroT J = false := by
          simp [zeroT]
          omega
        have hJmono : monoT J = true := by
          rcases hJnonmulti with hz | hm'
          · rw [hJzeroFalse] at hz
            contradiction
          · exact hm'
        obtain ⟨sJ, bJ, hdPJ, hdJ⟩ :=
          ih (Lng J) hJlt J (m - Pcut M) hmJ hJR hmJlt rfl
        have hTransJne : Trans J ≠ BZero :=
          Trans_ne_zero_of_not_singleton_74 J hJR hJne00
        obtain ⟨pJ, hpJ⟩ :=
          Trans_monoT_principal J hJR hJmono hTransJne
        have hTransJone : (untrm (Trans J)).length = 1 := by
          simp [hpJ, untrm]
        have hTransEq := (Trans_Mark_multi_equations M hR hmulti).1
        have hMarkEq := (Trans_Mark_multi_equations M hR hmulti).2 m
        have hTrans : Trans M = addBT (Trans A) (Trans J) := by
          simpa [A, J, hJne00] using hTransEq
        have hMark : Mark M m = Mark J (m - Pcut M) := by
          simpa [A, J, hJne00] using hMarkEq
        have hPredTrans : Trans (Pred M) = addBT (Trans A)
            (if Pred J == [(0, 0)] then Dprin 0 BZero
             else Trans (Pred J)) := by
          simpa [A, J] using Trans_Pred_multi_last M hR hmulti hJlen
        have hPredMark : Mark (Pred M) m =
            if Pred J == [(0, 0)] then Dprin 0 BZero
            else Mark (Pred J) (m - Pcut M) := by
          simpa [A, J] using Mark_Pred_multi_last M m hR hmulti hJlen
        by_cases hAzero : Trans A = BZero
        · have hTrans' : Trans M = Trans J := by
            rw [hTrans, hAzero, addBT_zero_left_74]
          by_cases hPJzero : Pred J = [(0, 0)]
          · have hPredJR : RTPS (Pred J) := RTPS_Pred J hJR
            have hPredJTrans : Trans (Pred J) = BZero := by
              have hz : zeroT (Pred J) = true := by
                simp [hPJzero, zeroT, entry]
              exact (Trans_preserves_zeroT (Pred J)
                (RTPS_TPS (Pred J) hPredJR)).1 hz
            have hPredJLen := length_Pred J hJlen
            have hlocal0 : m - Pcut M = 0 := by
              simp [hPJzero] at hPredJLen
              omega
            have hPredJMark : Mark (Pred J) (m - Pcut M) = BZero := by
              rw [hPJzero, hlocal0, Mark_eq_lengthAux [(0, 0)] 0]
              · simp [MarkAux, lastIdx, BZero]
              · simpa [hPJzero] using hPredJR
            have hzeroDec : scb_decomp BZero [] (flatBT BZero) [] := by
              simp [scb_decomp, BZero]
            have hpin := scb_unique_decomp_unconditional BZero sJ []
              (flatBT BZero) bJ []
              (by simpa [hPredJTrans, hPredJMark] using hdPJ) hzeroDec
            have hsJ : sJ = [] := hpin.1
            have hbJ : bJ = [] := hpin.2
            have hPredTrans' : Trans (Pred M) = Dprin 0 BZero := by
              simpa [hPJzero, hAzero, addBT_zero_left_74] using hPredTrans
            have hPredMark' : Mark (Pred M) m = Dprin 0 BZero := by
              simpa [hPJzero] using hPredMark
            have hD0TB : Dprin 0 BZero ∈ T_B := by
              exact Dprin_mem_T_B (by simp) (by
                simp [T_B, BZero, dfree_BT, dfree_BPList])
            have hD0P : ∃ p, Dprin 0 BZero = .trm [p] := ⟨_, rfl⟩
            have hPredSelf : scb_decomp (Dprin 0 BZero) []
                (flatBT (Dprin 0 BZero)) [] :=
              scb_decomp_self_74 (principal_flat_properties hD0TB hD0P).1
            refine ⟨[], [], ?_, ?_⟩
            · simpa [hPredTrans', hPredMark'] using hPredSelf
            · simpa [hTrans', hMark, hsJ, hbJ] using hdJ
          · have hPredTrans' : Trans (Pred M) = Trans (Pred J) := by
              simpa [hPJzero, hAzero, addBT_zero_left_74] using hPredTrans
            have hPredMark' : Mark (Pred M) m =
                Mark (Pred J) (m - Pcut M) := by
              simpa [hPJzero] using hPredMark
            refine ⟨sJ, bJ, ?_, ?_⟩
            · simpa [hPredTrans', hPredMark'] using hdPJ
            · simpa [hTrans', hMark] using hdJ
        · have hAuntrm : untrm (Trans A) ≠ [] := by
            intro hnil
            apply hAzero
            rcases hTA : Trans A with ⟨ps⟩
            have hps : ps = [] := by simpa [hTA, untrm] using hnil
            rw [hps]
            rfl
          have hLiftJ := scb_addBT_left_74 hdJ hTransJone hAuntrm
          have hdM : scb_decomp (Trans M) (liftScbPrefix (Trans A) sJ)
              (flatBT (Mark M m)) (bJ ++ [.rp]) := by
            simpa [hTrans, hMark] using hLiftJ
          by_cases hPJzero : Pred J = [(0, 0)]
          · have hPredJR : RTPS (Pred J) := RTPS_Pred J hJR
            have hPredJTrans : Trans (Pred J) = BZero := by
              have hz : zeroT (Pred J) = true := by
                simp [hPJzero, zeroT, entry]
              exact (Trans_preserves_zeroT (Pred J)
                (RTPS_TPS (Pred J) hPredJR)).1 hz
            have hPredJLen := length_Pred J hJlen
            have hlocal0 : m - Pcut M = 0 := by
              simp [hPJzero] at hPredJLen
              omega
            have hPredJMark : Mark (Pred J) (m - Pcut M) = BZero := by
              rw [hPJzero, hlocal0, Mark_eq_lengthAux [(0, 0)] 0]
              · simp [MarkAux, lastIdx, BZero]
              · simpa [hPJzero] using hPredJR
            have hzeroDec : scb_decomp BZero [] (flatBT BZero) [] := by
              simp [scb_decomp, BZero]
            have hpin := scb_unique_decomp_unconditional BZero sJ []
              (flatBT BZero) bJ []
              (by simpa [hPredJTrans, hPredJMark] using hdPJ) hzeroDec
            have hsJ : sJ = [] := hpin.1
            have hbJ : bJ = [] := hpin.2
            have hD0TB : Dprin 0 BZero ∈ T_B := by
              exact Dprin_mem_T_B (by simp) (by
                simp [T_B, BZero, dfree_BT, dfree_BPList])
            have hD0P : ∃ p, Dprin 0 BZero = .trm [p] := ⟨_, rfl⟩
            have hD0Self : scb_decomp (Dprin 0 BZero) []
                (flatBT (Dprin 0 BZero)) [] :=
              scb_decomp_self_74 (principal_flat_properties hD0TB hD0P).1
            have hD0one : (untrm (Dprin 0 BZero)).length = 1 := by
              simp [Dprin, untrm]
            have hLiftPred :=
              scb_addBT_left_74 hD0Self hD0one hAuntrm
            have hdPred : scb_decomp (Trans (Pred M))
                (liftScbPrefix (Trans A) []) (flatBT (Mark (Pred M) m))
                ([] ++ [.rp]) := by
              simpa [hPredTrans, hPredMark, hPJzero] using hLiftPred
            refine ⟨liftScbPrefix (Trans A) [], [] ++ [.rp], hdPred, ?_⟩
            simpa [hsJ, hbJ] using hdM
          · have hPredJR : RTPS (Pred J) := RTPS_Pred J hJR
            have hPredJT : TPS (Pred J) := RTPS_TPS (Pred J) hPredJR
            have hPredJne : Trans (Pred J) ≠ BZero :=
              Trans_ne_zero_of_not_singleton_74 (Pred J) hPredJR hPJzero
            have hPredJmono : monoT (Pred J) = true := by
              by_cases hOne : Lng (Pred J) = 1
              · have hz : zeroT (Pred J) = false := by
                  apply Bool.eq_false_of_not_eq_true
                  intro hz'
                  exact hPJzero
                    (RTPS_zeroT_eq_singleton_74 (Pred J) hPredJR hz')
                have hle : leR (Pred J) 0 0 (Lng (Pred J) - 1) = true := by
                  simp [hOne, leR, le0, le0Aux]
                simp [monoT, hz, hle]
              · have hlong : 2 < Lng J := by
                  rw [length_Pred J hJlen] at hOne
                  omega
                exact monoT_Pred_long J hJT hJmono hlong
            obtain ⟨pPJ, hpPJ⟩ :=
              Trans_monoT_principal (Pred J) hPredJR hPredJmono hPredJne
            have hPredJone : (untrm (Trans (Pred J))).length = 1 := by
              simp [hpPJ, untrm]
            have hLiftPred :=
              scb_addBT_left_74 hdPJ hPredJone hAuntrm
            have hdPred : scb_decomp (Trans (Pred M))
                (liftScbPrefix (Trans A) sJ) (flatBT (Mark (Pred M) m))
                (bJ ++ [.rp]) := by
              simpa [hPredTrans, hPredMark, hPJzero] using hLiftPred
            exact ⟨liftScbPrefix (Trans A) sJ, bJ ++ [.rp], hdPred, hdM⟩

/-- Corrected A46 form of the article proposition. -/
theorem Trans_Mark_Pred (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M) (hmlt : m < Lng M - 1) :
    ∃! sb : List Sym × List Sym,
      scb_decomp (Trans (Pred M)) sb.1 (flatBT (Mark (Pred M) m)) sb.2 ∧
      scb_decomp (Trans M) sb.1 (flatBT (Mark M m)) sb.2 := by
  obtain ⟨s, b, hPred, hM⟩ := Trans_Mark_Pred_exists M m hm hR hmlt
  refine ⟨(s, b), ⟨hPred, hM⟩, ?_⟩
  rintro ⟨s', b'⟩ ⟨hPred', _⟩
  have hu := scb_unique_decomp_unconditional
    (Trans (Pred M)) s' s (flatBT (Mark (Pred M) m)) b' b hPred' hPred
  simpa using hu

theorem m_7_4_Trans_Mark_Pred (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M) (hmlt : m < Lng M - 1) :
    ∃! sb : List Sym × List Sym,
      scb_decomp (Trans (Pred M)) sb.1 (flatBT (Mark (Pred M) m)) sb.2 ∧
      scb_decomp (Trans M) sb.1 (flatBT (Mark M m)) sb.2 :=
  Trans_Mark_Pred M m hm hR hmlt

#print axioms Trans_Mark_Pred

end PSS
