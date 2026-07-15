import «7».«7.3-Trans-welldefined»
import «7».«7.1-buchholz-fseq-lt»
import «7».«7.1-term-components»

/-!
# §7.3 命題（`c₁` と `c₂` の大小関係）

- 原文: `tmp/content.md` の同名命題
- Isabelle: `transC2_single_principal`, `transC1_single_principal`,
  `transC1_lessBT_transC2_full`
- 状態: 🚧 単一 principal 性を証明済、狭義不等式を移植中
-/

namespace PSS

/-- Every branch of the definition of `c₂` constructs one principal term. -/
theorem transC2_single_principal (M : PS) :
    (PB (transC2 M)).length = 1 := by
  simp only [PB, List.length_map]
  unfold transC2 transC2Core
  split <;> try split <;> try split
  all_goals simp [Dprin, untrm]

/-- A flattened string recognized as one principal code comes from exactly one
principal component. -/
theorem isPTB_str_imp_PB_length_one {c : BT}
    (h : isPTB_str (flatBT c)) :
    (PB c).length = 1 := by
  rcases h with ⟨p, _, hflat⟩
  have hc : c = .trm [p] := by
    apply flatBT_injective
    simpa [flatBT] using hflat
  subst c
  simp [PB, untrm]

/-- Under the recursive mono branch hypotheses, `c₁` is one principal term. -/
theorem transC1_single_principal (M : PS)
    (hR : RTPS M) (hmono : monoT M = true)
    (hj₁ : 0 < transJ1 M) (ht₁ : transT1 M ≠ BZero) :
    (PB (transC1 M)).length = 1 := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by simpa [transJ1, lastIdx] using hj₁
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hmarked := Marked_Pred_Adm M hM hlen hp
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hinv := (Trans_Mark_invariant (Pred M) hpredR).2.2 _ hmarked
  have hpair : (transT1 M, transC1 M) ∈ MarkedB := by
    simpa [transT1, transC1, transJm1, transJ0, lastParent] using hinv.2
  rcases hpair with ⟨s, b, hd⟩
  apply isPTB_str_imp_PB_length_one
  exact hd.2.1 ht₁

/-- A term with one principal component is reconstructed by its head
index and head body. -/
theorem principal_reconstruct {c : BT} (h : (PB c).length = 1) :
    c = Dprin (bpHeadV c) (bpHeadT c) := by
  rcases c with ⟨ps⟩
  simp only [PB, untrm, List.length_map] at h
  cases ps with
  | nil => simp at h
  | cons p ps =>
      cases ps with
      | nil =>
          rcases p with ⟨v, t⟩
          rfl
      | cons q ps => simp at h

private theorem SigmaB_snoc (xs : List BT) (x : BT) :
    SigmaB (xs ++ [x]) = addBT (SigmaB xs) x := by
  rcases x with ⟨ps⟩
  simp [SigmaB, addBT, untrm]

/-- Appending a nonzero principal list strictly increases a term. -/
theorem lessBT_addBT_self (t c : BT) (hc : c ≠ BZero) :
    lessBT t (addBT t c) = true := by
  rcases t with ⟨ts⟩
  rcases c with ⟨cs⟩
  have hcs : cs ≠ [] := by simpa [BZero] using hc
  have hlex : ∀ xs : List BP, lessBPList xs (xs ++ cs) = true := by
    intro xs
    induction xs with
    | nil =>
        cases cs with
        | nil => exact (hcs rfl).elim
        | cons q qs => rfl
    | cons p ps ih =>
        have hirr : lessBP p p = false := by
          rcases p with ⟨v, a⟩
          simp [lessBP, lessBT_linear_irrefl]
        simp [lessBPList, hirr, ih]
  simpa [lessBT, addBT] using hlex ts

private theorem getLastD_eq_getD_last {α : Type} (xs : List α) (d : α)
    (hxs : xs ≠ []) :
    xs.getLastD d = xs.getD (xs.length - 1) d := by
  cases h : xs with
  | nil => exact (hxs h).elim
  | cons x ys => simp [List.getLastD, List.getD, List.getLast_eq_getElem]

private theorem mem_PB_principal {t p : BT} (hp : p ∈ PB t) :
    ∃ q : BP, p = .trm [q] := by
  rcases t with ⟨ps⟩
  simp only [PB, untrm, List.mem_map] at hp
  rcases hp with ⟨q, _, rfl⟩
  exact ⟨q, rfl⟩

private theorem lessBT_Dprin_same (v : ℕ∞) {a b : BT}
    (h : lessBT a b = true) :
    lessBT (Dprin v a) (Dprin v b) = true := by
  simp [Dprin, lessBT, lessBPList, lessBP, h]

/-- The lexicographic part of `c₁ < c₂`; only the condition-(VI) body
comparison is left as an explicit premise. -/
theorem transC1_lessBT_transC2_of_condVI (M : PS)
    (hR : RTPS M) (hmono : monoT M = true)
    (hj₁ : 0 < transJ1 M) (ht₁ : transT1 M ≠ BZero)
    (hVIbound : transCondVI M = true →
      lessBT (transT2 M)
        (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero) = true) :
    lessBT (transC1 M) (transC2 M) = true := by
  let t₂ := transT2 M
  let j₁ := transJ1 M
  let jp := transJ0 M
  let dj₁ := Dprin (entry M 1 j₁ : ℕ∞) BZero
  have hdj₁ : dj₁ ≠ BZero := by simp [dj₁, Dprin, BZero]
  have hc₁len := transC1_single_principal M hR hmono hj₁ ht₁
  have hc₁eq : transC1 M = Dprin (transV M) t₂ := by
    have h := principal_reconstruct hc₁len
    simpa [transV, transT2, t₂] using h
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by simpa [transJ1, lastIdx] using hj₁
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hmarked := Marked_Pred_Adm M hM hlen hp
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hc₁TB : transC1 M ∈ T_B := by
    simpa [transC1, transJm1, transJ0, lastParent] using
      Mark_mem_T_B (Pred M) _ hpredR hmarked
  have ht₂TB : t₂ ∈ T_B := by
    rw [hc₁eq] at hc₁TB
    change dfree_BT (.trm [.db (transV M) t₂]) = true at hc₁TB
    simp only [dfree_BT, dfree_BPList, dfree_BP,
      Bool.and_eq_true, Bool.true_eq] at hc₁TB
    exact hc₁TB.1.2
  by_cases hA : (transCondI M || transCondIII M || transCondV M) = true
  · have hc₂eq : transC2 M = Dprin (transV M) (addBT t₂ dj₁) := by
      simp [transC2, transC2Core, hA, t₂, dj₁, j₁, transJ1]
    rw [hc₁eq, hc₂eq]
    exact lessBT_Dprin_same _ (lessBT_addBT_self t₂ dj₁ hdj₁)
  · by_cases hVI : transCondVI M = true
    · have hc₂eq : transC2 M = Dprin (transV M) dj₁ := by
        simp [transC2, transC2Core, hA, hVI, dj₁, j₁, transJ1]
      rw [hc₁eq, hc₂eq]
      apply lessBT_Dprin_same
      simpa [t₂, dj₁, j₁] using hVIbound hVI
    · by_cases ht₂zero : t₂ = BZero
      · have hc₂eq : transC2 M =
            Dprin (transV M) (Dprin (entry M 1 jp : ℕ∞) dj₁) := by
          simp [transC2, transC2Core, hA, hVI, t₂, ht₂zero,
            dj₁, j₁, jp, transJ1, transJ0]
        rw [hc₁eq, hc₂eq, ht₂zero]
        apply lessBT_Dprin_same
        simp [BZero, Dprin, lessBT, lessBPList]
      · have hPBpos : 0 < (PB t₂).length := by
          have hz := (term_components t₂ ht₂TB).1
          by_contra hnot
          have hzero : (PB t₂).length = 0 := by omega
          exact ht₂zero (hz.mp hzero)
        have hPBne : PB t₂ ≠ [] := List.ne_nil_of_length_pos hPBpos
        let J := (PB t₂).length - 1
        let pJ := (PB t₂).getD J BZero
        have hpJlast : pJ = (PB t₂).getLastD BZero := by
          rw [getLastD_eq_getD_last (PB t₂) BZero hPBne]
        have hpJmem : pJ ∈ PB t₂ := by
          rw [hpJlast]
          cases hxs : PB t₂ with
          | nil => exact (hPBne hxs).elim
          | cons x xs =>
              simpa [hxs, List.getLastD] using
                (List.getLastD_mem_cons (l := xs) (a := x))
        rcases mem_PB_principal hpJmem with ⟨q, hpJq⟩
        have hpJrec : pJ = Dprin (bpHeadV pJ) (bpHeadT pJ) := by
          rw [hpJq]
          rcases q with ⟨v, a⟩
          rfl
        have hPBdecomp : (PB t₂).take J ++ [pJ] = PB t₂ := by
          rw [show (PB t₂).take J = (PB t₂).dropLast by
            simp [List.dropLast_eq_take, J]]
          rw [hpJlast]
          cases hxs : PB t₂ with
          | nil => exact (hPBne hxs).elim
          | cons x xs =>
              simpa [List.getLastD] using
                List.dropLast_append_getLast (show x :: xs ≠ [] by simp)
        have ht₂split :
            t₂ = addBT (SigmaB ((PB t₂).take J)) pJ := by
          calc
            t₂ = SigmaB (PB t₂) := (term_components t₂ ht₂TB).2.symm
            _ = SigmaB ((PB t₂).take J ++ [pJ]) := by rw [hPBdecomp]
            _ = addBT (SigmaB ((PB t₂).take J)) pJ := SigmaB_snoc _ _
        by_cases hleft : bpHeadV pJ = (entry M 1 jp : ℕ∞)
        · have hc₂eq : transC2 M = Dprin (transV M)
              (addBT (SigmaB ((PB t₂).take J))
                (Dprin (entry M 1 jp : ℕ∞) (addBT (bpHeadT pJ) dj₁))) := by
            unfold transC2
            change transC2Core M (transV M) t₂ = _
            have hleft' :
                bpHeadV ((PB t₂).getD ((PB t₂).length - 1) BZero) =
                  (entry M 1 jp : ℕ∞) := by
              simpa [pJ, J] using hleft
            have hleft'' :
                bpHeadV (((PB t₂)[(PB t₂).length - 1]?).getD BZero) =
                  (entry M 1 jp : ℕ∞) := by
              simpa [List.getD_eq_getElem?_getD] using hleft'
            simp [transC2Core, hA, hVI, ht₂zero,
              J, pJ, List.getD_eq_getElem?_getD, hleft'',
              dj₁, j₁, jp, transJ1, transJ0]
          have hpJval : pJ = Dprin (entry M 1 jp : ℕ∞) (bpHeadT pJ) := by
            simpa [hleft] using hpJrec
          have hinner : lessBT pJ
              (Dprin (entry M 1 jp : ℕ∞) (addBT (bpHeadT pJ) dj₁)) = true := by
            rw [hpJval]
            exact lessBT_Dprin_same _
              (lessBT_addBT_self (bpHeadT pJ) dj₁ hdj₁)
          have hbody := addBT_lt_right_bf (SigmaB ((PB t₂).take J)) _ _ hinner
          rw [hc₁eq, hc₂eq]
          apply lessBT_Dprin_same
          nth_rewrite 1 [ht₂split]
          exact hbody
        · have hc₂eq : transC2 M = Dprin (transV M)
              (addBT t₂ (Dprin (entry M 1 jp : ℕ∞) (addBT t₂ dj₁))) := by
            unfold transC2
            change transC2Core M (transV M) t₂ = _
            have hleft' :
                ¬bpHeadV ((PB t₂).getD ((PB t₂).length - 1) BZero) =
                  (entry M 1 jp : ℕ∞) := by
              simpa [pJ, J] using hleft
            have hleft'' :
                ¬bpHeadV (((PB t₂)[(PB t₂).length - 1]?).getD BZero) =
                  (entry M 1 jp : ℕ∞) := by
              simpa [List.getD_eq_getElem?_getD] using hleft'
            have hleftLast :
                ¬bpHeadV (((PB t₂)[(PB t₂).length - 1]?).getD BZero) =
                  (entry M 1 (lastParent M) : ℕ∞) := by
              simpa [jp, transJ0] using hleft''
            simp [transC2Core, hA, hVI, ht₂zero,
              J, pJ, List.getD_eq_getElem?_getD, hleftLast,
              dj₁, j₁, jp, transJ1, transJ0]
          rw [hc₁eq, hc₂eq]
          apply lessBT_Dprin_same
          apply lessBT_addBT_self
          simp [Dprin, BZero]

#print axioms transC2_single_principal
#print axioms isPTB_str_imp_PB_length_one
#print axioms transC1_single_principal
#print axioms principal_reconstruct
#print axioms lessBT_addBT_self
#print axioms transC1_lessBT_transC2_of_condVI

end PSS
