import «7».«7.3-Mark-rightmost1»

/-!
# §7.3 命題（`Trans` が単項性を保つこと）

- 原文: `tmp/content.md` の同名命題
- Isabelle: `Trans_PT_single`, `m_7_3_Trans_monoT`
- 訂正: A16（先頭 `P` 成分が零項でない簡約形に制限する）
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

@[simp] theorem PB_length_addBT (a b : BT) :
    (PB (addBT a b)).length = (PB a).length + (PB b).length := by
  rcases a with ⟨as⟩
  rcases b with ⟨bs⟩
  simp [PB, addBT, untrm]

theorem PB_length_eq_zero_iff (t : BT) :
    (PB t).length = 0 ↔ t = BZero := by
  rcases t with ⟨ps⟩
  simp [PB, BZero, untrm]

/-- A nonzero translation of a reduced monotone sequence consists of one
principal Buchholz component. -/
theorem Trans_monoT_principal (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) (htne : Trans M ≠ BZero) :
    ∃ p, Trans M = .trm [p] := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      have hM : TPS M := RTPS_TPS M hR
      have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
      by_cases hOne : Lng M = 1
      · obtain ⟨v, hMv⟩ := (one_column M hM).1 ⟨hOne, hR⟩
        subst M
        have hR' : RTPS [(v, v)] := hR
        have hv : v ≠ 0 := by
          intro hv
          subst v
          apply htne
          rw [Trans_eq_lengthAux [(0, 0)] hR']
          have hred : reduced [(0, 0)] = true := hR'
          simp [TransAux, lastIdx, BZero, hred]
        refine ⟨.db (v : ℕ∞) BZero, ?_⟩
        rw [Trans_eq_lengthAux [(v, v)] hR']
        have hred : reduced [(v, v)] = true := hR'
        simp [TransAux, lastIdx, entry, hv, BZero, hred, Dprin]
      · have hlen : 1 < Lng M := by omega
        have heq := (Trans_Mark_mono_equations M hR hlen hmono).1
        by_cases ht₁ : Trans (Pred M) = BZero
        · rw [heq]
          simp [ht₁]
          exact ⟨_, rfl⟩
        · have hpredR : RTPS (Pred M) := RTPS_Pred M hR
          have hpredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
          have hpredLt : Lng (Pred M) < n := by rw [hpredLen, ← hn]; omega
          have hpredM : TPS (Pred M) := RTPS_TPS (Pred M) hpredR
          have hpredMono : monoT (Pred M) = true := by
            by_cases hPredOne : Lng (Pred M) = 1
            · have hzPred : zeroT (Pred M) = false := by
                apply Bool.eq_false_of_not_eq_true
                intro hz
                have hzTrans := (Trans_preserves_zeroT (Pred M) hpredM).1 hz
                exact ht₁ hzTrans
              have hle : leR (Pred M) 0 0 (Lng (Pred M) - 1) = true := by
                simp [hPredOne, leR, le0, le0Aux]
              simp [monoT, hzPred, hle]
            · have hlong : 2 < Lng M := by omega
              exact monoT_Pred_long M hM hmono hlong
          have ht₁P : ∃ p, Trans (Pred M) = .trm [p] :=
            ih (Lng (Pred M)) hpredLt (Pred M) hpredR hpredMono ht₁ rfl
          let t₁ := Trans (Pred M)
          let jp := lastParent M
          let c₁ := Mark (Pred M) (Adm M jp)
          let c₂ := transC2Core M (bpHeadV c₁) (bpHeadT c₁)
          have hp : hasParent M 0 (Lng M - 1) = true :=
            mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
          have hc₁Marked : Marked (Pred M) (Adm M jp) := by
            simpa [jp] using Marked_Pred_Adm M hM hlen hp
          have hc₁Inv :=
            (Trans_Mark_invariant (Pred M) hpredR).2.2 _ hc₁Marked
          have ht₁TB : t₁ ∈ T_B := by
            simpa [t₁] using (Trans_Mark_invariant (Pred M) hpredR).1
          have hc₁TB : c₁ ∈ T_B := by simpa [c₁] using hc₁Inv.1
          have ht₁c₁ : (t₁, c₁) ∈ MarkedB := by
            simpa [t₁, c₁] using hc₁Inv.2
          have hc₁P : ∃ p, c₁ = .trm [p] := by
            apply marked_component_principal
            · simpa [t₁] using ht₁
            · exact ht₁c₁
          have hc₂Facts := transC2Core_properties M c₁ hc₁TB hc₁P
          have hc₂TB : c₂ ∈ T_B := by simpa [c₂] using hc₂Facts.1
          have hc₂P : ∃ p, c₂ = .trm [p] := by simpa [c₂] using hc₂Facts.2
          have hTrans : Trans M = replaceScb t₁ c₁ c₂ := by
            simpa [t₁, jp, c₁, c₂, ht₁] using heq
          rw [hTrans]
          exact replaceScb_principal ht₁TB (by simpa [t₁] using ht₁P)
            hc₁TB hc₁P hc₂TB hc₂P ht₁c₁

private theorem nonzero_of_leading_P_nonzero (M : PS)
    (hnz0 : zeroT ((P M).getD 0 []) = false) : zeroT M = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hz
  have hmulti : multiT M = false := by simp [multiT, hz]
  have hP : P M = [M] := P_nonmulti_eq M hmulti
  have : (P M).getD 0 [] = M := by simp [hP]
  rw [this, hz] at hnz0
  contradiction

/-- Corrected A16 form: away from a zero leading `P` component, reduced
pair-sequence monotonicity is exactly principality of its translation. -/
theorem m_7_3_Trans_monoT (M : PS) (hR : RTPS M)
    (hnz0 : zeroT ((P M).getD 0 []) = false) :
    (monoT M = true ↔ (PB (Trans M)).length = 1) := by
  have hM : TPS M := RTPS_TPS M hR
  have hzM : zeroT M = false := nonzero_of_leading_P_nonzero M hnz0
  constructor
  · intro hmono
    have htne : Trans M ≠ BZero := by
      intro ht
      have hz := (Trans_preserves_zeroT M hM).2 ht
      rw [hzM] at hz
      contradiction
    obtain ⟨p, hp⟩ := Trans_monoT_principal M hR hmono htne
    simp [hp, PB, untrm]
  · intro hPB
    apply Bool.eq_true_of_not_eq_false
    intro hmono
    have hmulti : multiT M = true := by simp [multiT, hzM, hmono]
    have hlen : 1 < Lng M := multi_length_fseq M hM hmulti
    let A := M.take (Pcut M)
    let J := M.drop (Pcut M)
    have hAR : RTPS A := by
      simpa [A] using trans_multi_prefix_RTPS M hR hmulti
    have hJR : RTPS J := by
      have hlast := (trans_multi_last_component M hM hmulti).1
      have hPne : P M ≠ [] := P_nonempty M
      have hidx : (P M).length - 1 < (P M).length := by
        have := List.length_pos_of_ne_nil hPne
        omega
      have hh := (RTPS_iff_P_components M hM).1 hR
        ((P M).length - 1) hidx
      dsimp [J]
      rw [← hlast]
      exact hh
    have hPsplit : P M = P A ++ [J] := by
      simpa [A, J] using P_multi_step M hmulti hlen
    have hPAne : P A ≠ [] := P_nonempty A
    have hhead : (P A).getD 0 [] = (P M).getD 0 [] := by
      rw [hPsplit]
      cases hPA : P A with
      | nil => exact (hPAne hPA).elim
      | cons x xs => simp
    have hnzA : zeroT ((P A).getD 0 []) = false := by
      rw [hhead]
      exact hnz0
    have hzA : zeroT A = false := nonzero_of_leading_P_nonzero A hnzA
    have hTAne : Trans A ≠ BZero := by
      intro hTA
      have hz := (Trans_preserves_zeroT A (RTPS_TPS A hAR)).2 hTA
      rw [hzA] at hz
      contradiction
    have hPBA : 1 ≤ (PB (Trans A)).length := by
      have hne : (PB (Trans A)).length ≠ 0 := by
        intro hzero
        exact hTAne ((PB_length_eq_zero_iff (Trans A)).1 hzero)
      omega
    have heq := (Trans_Mark_multi_equations M hR hmulti).1
    by_cases hJzero : J = [(0, 0)]
    · have hTrans : Trans M = addBT (Trans A) (Dprin 0 BZero) := by
        simpa [A, J, hJzero] using heq
      have hright : (PB (Dprin 0 BZero)).length = 1 := by
        simp [PB, Dprin, untrm]
      rw [hTrans, PB_length_addBT, hright] at hPB
      omega
    · have hzJ : zeroT J = false := by
        apply Bool.eq_false_of_not_eq_true
        intro hz
        apply hJzero
        rw [← RTPS_Red_eq J hJR]
        exact Red_zero_mr J hz
      have hTJne : Trans J ≠ BZero := by
        intro hTJ
        have hz := (Trans_preserves_zeroT J (RTPS_TPS J hJR)).2 hTJ
        rw [hzJ] at hz
        contradiction
      have hPBJ : 1 ≤ (PB (Trans J)).length := by
        have hne : (PB (Trans J)).length ≠ 0 := by
          intro hzero
          exact hTJne ((PB_length_eq_zero_iff (Trans J)).1 hzero)
        omega
      have hTrans : Trans M = addBT (Trans A) (Trans J) := by
        simpa [A, J, hJzero] using heq
      rw [hTrans, PB_length_addBT] at hPB
      omega

/-- A16 counterexample to the verbatim article statement.  The reduced
multi sequence `[(0,0),(0,0)]` translates to the principal `D_0 0`. -/
theorem Trans_monoT_original_counterexample :
    RTPS [(0, 0), (0, 0)] ∧
      monoT [(0, 0), (0, 0)] = false ∧
      Trans [(0, 0), (0, 0)] = Dprin 0 BZero ∧
      (PB (Trans [(0, 0), (0, 0)])).length = 1 ∧
      zeroT ((P [(0, 0), (0, 0)]).getD 0 []) = true ∧
      (P [(0, 0), (0, 0)]).length = 2 := by
  have hR : RTPS [(0, 0), (0, 0)] := by decide
  have hTrans : Trans [(0, 0), (0, 0)] = Dprin 0 BZero := by
    have hmulti : multiT [(0, 0), (0, 0)] = true := by decide
    have hzeroR : Trans [(0, 0)] = BZero := by
      have hR0 : RTPS [(0, 0)] := by decide
      rw [Trans_eq_lengthAux [(0, 0)] hR0]
      simp [TransAux, lastIdx, BZero]
    have heq := (Trans_Mark_multi_equations
      [(0, 0), (0, 0)] hR hmulti).1
    have hcut : Pcut [(0, 0), (0, 0)] = 1 := by decide
    simpa [hcut, hzeroR, addBT, Dprin, BZero] using heq
  refine ⟨hR, by decide, hTrans, ?_, by decide, by decide⟩
  simp [hTrans, PB, Dprin, untrm]

#print axioms Trans_monoT_principal
#print axioms m_7_3_Trans_monoT
#print axioms Trans_monoT_original_counterexample

end PSS
