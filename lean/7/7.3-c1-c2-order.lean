import «7».«7.3-Trans-welldefined»
import «Buchholz-1986».«Buchholz-1986-3.2-descent»
import «7».«7.1-term-components»

/-!
# §7.3 命題（`c₁` と `c₂` の大小関係）

- 原文: `tmp/content.md` の同名命題
- Isabelle: `transC2_single_principal`, `transC1_single_principal`,
  `transC1_lessBT_transC2_full`
- 状態: ✅ 証明済（sorry 0）
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

/-! ## Indices occurring in Buchholz terms -/

/-- The set of `D` indices occurring in a term, read from its flat code. -/
def flatIdx (t : BT) : Set ℕ∞ :=
  {v | .dsym v ∈ flatBT t}

@[simp] theorem flatIdx_BZero : flatIdx BZero = ∅ := by
  ext v
  simp [flatIdx, BZero, flatBT]

@[simp] theorem flatIdx_Dprin (v : ℕ∞) (t : BT) :
    flatIdx (Dprin v t) = insert v (flatIdx t) := by
  ext w
  simp [flatIdx, Dprin, flatBT, flatBP]

private theorem dsym_mem_flatBPTail_append (v : ℕ∞)
    (xs ys : List BP) :
    .dsym v ∈ flatBPTail (xs ++ ys) ↔
      .dsym v ∈ flatBPTail xs ∨ .dsym v ∈ flatBPTail ys := by
  induction xs with
  | nil => simp [flatBPTail]
  | cons p ps ih => simp [flatBPTail, ih, or_assoc]

@[simp] theorem flatIdx_addBT (a b : BT) :
    flatIdx (addBT a b) = flatIdx a ∪ flatIdx b := by
  rcases a with ⟨as⟩
  rcases b with ⟨bs⟩
  cases as with
  | nil =>
      change flatIdx (.trm bs) = flatIdx BZero ∪ flatIdx (.trm bs)
      simp
  | cons p ps =>
      cases ps with
      | nil =>
          cases bs with
          | nil =>
              change flatIdx (.trm [p]) = flatIdx (.trm [p]) ∪ flatIdx BZero
              simp
          | cons q qs =>
              cases qs with
              | nil =>
                  ext v
                  simp [flatIdx, addBT, flatBT, flatBPTail]
              | cons r rs =>
                  ext v
                  simp [flatIdx, addBT, flatBT, flatBPTail]
      | cons q qs =>
          cases bs with
          | nil =>
              rw [show addBT (BT.trm (p :: q :: qs)) (BT.trm []) =
                BT.trm (p :: q :: qs) by simp [addBT]]
              change flatIdx (.trm (p :: q :: qs)) =
                flatIdx (.trm (p :: q :: qs)) ∪ flatIdx BZero
              simp
          | cons r rs =>
              cases rs with
              | nil =>
                  ext v
                  simp [flatIdx, addBT, flatBT, flatBPTail,
                    dsym_mem_flatBPTail_append, or_assoc]
              | cons s ss =>
                  ext v
                  simp [flatIdx, addBT, flatBT, flatBPTail,
                    dsym_mem_flatBPTail_append, or_assoc]

private theorem SigmaB_cons (x : BT) (xs : List BT) :
    SigmaB (x :: xs) = addBT x (SigmaB xs) := by
  rcases x with ⟨ps⟩
  simp [SigmaB, addBT, untrm]

theorem flatIdx_SigmaB (ts : List BT) :
    flatIdx (SigmaB ts) = ⋃ t ∈ ts, flatIdx t := by
  induction ts with
  | nil =>
      rw [show SigmaB [] = BZero by rfl]
      simp
  | cons t ts ih =>
      rw [SigmaB_cons, flatIdx_addBT, ih]
      simp

private theorem SigmaB_PB_all (t : BT) : SigmaB (PB t) = t := by
  rcases t with ⟨ps⟩
  simp only [PB, untrm, SigmaB]
  congr 1
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [untrm, ih]

theorem flatIdx_SigmaB_take_PB_subset (t : BT) (k : ℕ) :
    flatIdx (SigmaB ((PB t).take k)) ⊆ flatIdx t := by
  intro v hv
  rw [flatIdx_SigmaB] at hv
  simp only [Set.mem_iUnion] at hv
  rcases hv with ⟨c, hcTake, hvc⟩
  have hcPB : c ∈ PB t := List.mem_of_mem_take hcTake
  have hvall : v ∈ flatIdx (SigmaB (PB t)) := by
    rw [flatIdx_SigmaB]
    refine Set.mem_iUnion_of_mem c ?_
    exact Set.mem_iUnion_of_mem hcPB hvc
  simpa [SigmaB_PB_all] using hvall

theorem flatIdx_PB_getD_subset (t : BT) (k : ℕ) :
    flatIdx ((PB t).getD k BZero) ⊆ flatIdx t := by
  by_cases hk : k < (PB t).length
  · have hmem : (PB t).getD k BZero ∈ PB t := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      exact List.getElem_mem _
    intro v hv
    have hvall : v ∈ flatIdx (SigmaB (PB t)) := by
      rw [flatIdx_SigmaB]
      refine Set.mem_iUnion_of_mem ((PB t).getD k BZero) ?_
      exact Set.mem_iUnion_of_mem hmem hv
    simpa [SigmaB_PB_all] using hvall
  · have hget : (PB t).getD k BZero = BZero := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff, hk]
    change flatIdx ((PB t).getD k BZero) ⊆ flatIdx t
    rw [hget]
    simp

theorem flatIdx_bpHeadT_subset (t : BT) :
    flatIdx (bpHeadT t) ⊆ flatIdx t := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => simp [bpHeadT, BZero]
  | cons p ps =>
      rcases p with ⟨v, a⟩
      cases ps with
      | nil =>
          intro w hw
          simpa [flatIdx, bpHeadT, flatBT, flatBP] using Or.inr hw
      | cons q qs =>
          intro w hw
          simp only [flatIdx, bpHeadT, Set.mem_setOf_eq] at hw ⊢
          simp [flatBT, flatBP, hw]

theorem bpHeadV_mem_flatIdx {t : BT} (ht : t ≠ BZero) :
    bpHeadV t ∈ flatIdx t := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => exact (ht rfl).elim
  | cons p ps =>
      rcases p with ⟨v, a⟩
      cases ps with
      | nil => simp [bpHeadV, flatIdx, flatBT, flatBP]
      | cons q qs => simp [bpHeadV, flatIdx, flatBT, flatBP]

/-- `transC2Core` introduces only its outer index and the two explicit
row-1 indices; all remaining indices come from its body argument. -/
theorem flatIdx_transC2Core_subset (M : PS) (v : ℕ∞) (t₂ : BT) :
    flatIdx (transC2Core M v t₂) ⊆
      insert v (flatIdx t₂ ∪
        {(entry M 1 (lastIdx M) : ℕ∞),
          (entry M 1 (lastParent M) : ℕ∞)}) := by
  let pJ := (PB t₂).getD ((PB t₂).length - 1) BZero
  have hpJsub : flatIdx pJ ⊆ flatIdx t₂ := by
    simpa [pJ] using flatIdx_PB_getD_subset t₂ ((PB t₂).length - 1)
  have hbodySub : flatIdx (bpHeadT pJ) ⊆ flatIdx t₂ :=
    (flatIdx_bpHeadT_subset pJ).trans hpJsub
  have hsigSub :
      flatIdx (SigmaB ((PB t₂).take ((PB t₂).length - 1))) ⊆
        flatIdx t₂ :=
    flatIdx_SigmaB_take_PB_subset t₂ ((PB t₂).length - 1)
  by_cases hA : (transCondI M || transCondIII M || transCondV M) = true
  · intro x hx
    simp only [transC2Core, hA, if_true] at hx
    simp only [flatIdx_Dprin, flatIdx_addBT, flatIdx_BZero,
      Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff] at hx ⊢
    aesop
  · by_cases hVI : transCondVI M = true
    · intro x hx
      simp only [transC2Core, hA, if_false, hVI, if_true] at hx
      simp only [flatIdx_Dprin, flatIdx_BZero,
        Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff] at hx ⊢
      aesop
    · by_cases hz : t₂ = BZero
      · intro x hx
        simp only [transC2Core, hA, if_false, hVI,
          beq_iff_eq, hz, if_true] at hx
        simp only [flatIdx_Dprin, flatIdx_BZero,
          Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff] at hx ⊢
        aesop
      · by_cases hleft : bpHeadV pJ = (entry M 1 (lastParent M) : ℕ∞)
        · intro x hx
          have hpJraw :
              (PB t₂).getD ((PB t₂).length - 1) BZero = pJ := rfl
          simp only [transC2Core, hA, if_false, hVI, beq_iff_eq,
            hz, hpJraw, hleft, if_true] at hx
          simp only [flatIdx_Dprin, flatIdx_addBT, flatIdx_BZero,
            Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff] at hx ⊢
          aesop
        · intro x hx
          have hpJraw :
              (PB t₂).getD ((PB t₂).length - 1) BZero = pJ := rfl
          simp only [transC2Core, hA, if_false, hVI, beq_iff_eq,
            hz, hpJraw, hleft] at hx
          simp only [flatIdx_Dprin, flatIdx_addBT, flatIdx_BZero,
            Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff] at hx ⊢
          aesop

theorem flatIdx_transC2_subset (M : PS) (hc₁ : transC1 M ≠ BZero) :
    flatIdx (transC2 M) ⊆ flatIdx (transC1 M) ∪
      {(entry M 1 (transJ1 M) : ℕ∞),
        (entry M 1 (transJ0 M) : ℕ∞)} := by
  have hv : transV M ∈ flatIdx (transC1 M) := by
    simpa [transV] using bpHeadV_mem_flatIdx hc₁
  have ht₂ : flatIdx (transT2 M) ⊆ flatIdx (transC1 M) := by
    simpa [transT2] using flatIdx_bpHeadT_subset (transC1 M)
  intro x hx
  have hcore := flatIdx_transC2Core_subset M (transV M) (transT2 M) hx
  simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff] at hcore ⊢
  rcases hcore with rfl | hx | rfl | rfl
  · exact .inl hv
  · exact .inl (ht₂ hx)
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

/-- Replacing a flat principal occurrence can introduce only indices from the
replacement; an all-right-parenthesis suffix contributes no index. -/
theorem flatIdx_scb_replacement_subset {t c₀ c₁ c : BT}
    {s b b₀ : List Sym}
    (ht : flatBT t = s ++ flatBT c ++ b)
    (hc₀ : flatBT c₀ = s ++ flatBT c₁ ++ b₀)
    (hb : ∀ x ∈ b, x = .rp) :
    flatIdx t ⊆ flatIdx c₀ ∪ flatIdx c := by
  intro v hv
  change .dsym v ∈ flatBT t at hv
  rw [ht] at hv
  simp only [List.mem_append] at hv
  rcases hv with (hs | hc) | hbmem
  · apply Set.mem_union_left
    change .dsym v ∈ flatBT c₀
    rw [hc₀]
    simp [hs]
  · exact Set.mem_union_right _ hc
  · have heq := hb (.dsym v) hbmem
    simp at heq

/-! ## Suffix bounds for translated indices -/

/-- Maximum row-1 entry from `m` through the final column (zero for an empty
interval). -/
def row1Bound (M : PS) (m : ℕ) : ℕ :=
  (Finset.Icc m (Lng M - 1)).sup (entry M 1)

theorem entry_le_row1Bound (M : PS) {m j : ℕ}
    (hmj : m ≤ j) (hj : j ≤ Lng M - 1) :
    entry M 1 j ≤ row1Bound M m := by
  exact Finset.le_sup (f := entry M 1) (Finset.mem_Icc.mpr ⟨hmj, hj⟩)

theorem Marked_index_le_last {M : PS} {m : ℕ} (hm : Marked M m) :
    m ≤ Lng M - 1 := by
  have hle : le0 M m (Lng M - 1) = true := by
    simpa [leR] using hm.2.2
  exact le0_index_fseq hle

theorem row1Bound_Pred_le (M : PS) {m i : ℕ}
    (hlen : 1 < Lng M) (hmi : m ≤ i) (hi : i ≤ Lng M - 2) :
    row1Bound (Pred M) i ≤ row1Bound M m := by
  apply Finset.sup_le
  intro j hj
  have hjI := Finset.mem_Icc.mp hj
  have hPL : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hjLastM : j ≤ Lng M - 1 := by omega
  have hjLt : j < Lng M - 1 := by rw [hPL] at hjI; omega
  calc
    entry (Pred M) 1 j = entry M 1 j := entry_Pred M 1 j hjLt
    _ ≤ row1Bound M m := entry_le_row1Bound M (hmi.trans hjI.1) hjLastM

private theorem row0_parent_max (M : PS) {k p j : ℕ}
    (hp : hasParent M 0 j = true)
    (hpj : nextR M 0 p j = true)
    (hkj : leR M 0 k j = true) (hklt : k < j) :
    k ≤ p := by
  have hle0 : le0 M k j = true := by simpa [leR] using hkj
  have hh := hle0
  simp only [le0, Bool.and_eq_true] at hh
  cases hL : Lng M with
  | zero => simp [hL] at hh
  | succ fuel =>
      have haux := hh.2
      rw [hL] at haux
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq,
        List.any_eq_true, Bool.and_eq_true, List.mem_range] at haux
      rcases haux with heq | ⟨q, hqj, hqnext, hkq⟩
      · omega
      · have hqnextR : nextR M 0 q j = true := by
          simpa [nextR] using hqnext
        have hqp : q = p := row0_parent_unique M q p j hqnextR hpj
        subst q
        exact le0Aux_index_fseq hkq

theorem marked_le_lastParent (M : PS) {m : ℕ}
    (hm : Marked M m) (hmono : monoT M = true)
    (hlen : 1 < Lng M) (hmlt : m < Lng M - 1) :
    m ≤ parent M 0 (Lng M - 1) := by
  have hM : TPS M := hm.1
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  apply row0_parent_max M hp (hasParent_next_fseq M 0 (Lng M - 1) hp)
  · exact hm.2.2
  · exact hmlt

private theorem coe_entry_le_row1Bound (M : PS) {m j : ℕ}
    (hmj : m ≤ j) (hj : j ≤ Lng M - 1) :
    (entry M 1 j : ℕ∞) ≤ (row1Bound M m : ℕ∞) := by
  exact_mod_cast entry_le_row1Bound M hmj hj

/-- Every index occurring in a marked translation is bounded by the maximum
row-1 entry on the suffix beginning at the marked column. -/
theorem Mark_flatIdx_bound (N : PS) (m : ℕ)
    (hR : RTPS N) (hm : Marked N m) :
    ∀ v ∈ flatIdx (Mark N m), v ≤ (row1Bound N m : ℕ∞) := by
  generalize hn : Lng N = n
  induction n using Nat.strong_induction_on generalizing N m with
  | h n ih =>
      have hN : TPS N := RTPS_TPS N hR
      have hmLast : m ≤ Lng N - 1 := Marked_index_le_last hm
      by_cases hOne : Lng N = 1
      · obtain ⟨u, hNu⟩ := (one_column N hN).1 ⟨hOne, hR⟩
        subst N
        have hm0 : m = 0 := by simpa using hmLast
        subst m
        have hR' : RTPS [(u, u)] := hR
        have hMark : Mark [(u, u)] 0 =
            if u = 0 then BZero else Dprin (u : ℕ∞) BZero := by
          rw [Mark_eq_lengthAux [(u, u)] 0 hR']
          have hred : reduced [(u, u)] = true := hR'
          simp [MarkAux, lastIdx, entry, hred, BZero]
        intro v hv
        by_cases hu : u = 0
        · have hMarkZero : Mark [(u, u)] 0 = BZero := by
            simpa [hu] using hMark
          rw [hMarkZero, flatIdx_BZero] at hv
          exact hv.elim
        · have hvu : v = (u : ℕ∞) := by
            have hMarkD : Mark [(u, u)] 0 = Dprin (u : ℕ∞) BZero := by
              simpa [hu] using hMark
            rw [hMarkD] at hv
            simpa only [flatIdx_Dprin, flatIdx_BZero, Set.mem_insert_iff,
              Set.mem_empty_iff_false, or_false] using hv
          subst v
          exact coe_entry_le_row1Bound [(u, u)] (m := 0) (j := 0)
            (le_refl _) (by simp)
      · have hlen : 1 < Lng N := by
          have hpos := List.length_pos_of_ne_nil hN
          change N.length ≠ 1 at hOne
          change 1 < N.length
          omega
        by_cases hmono : monoT N = true
        · let j₁ := lastIdx N
          let jp := lastParent N
          let jm := Adm N jp
          let t₁ := Trans (Pred N)
          let c₁ := Mark (Pred N) jm
          let c₂ := transC2Core N (bpHeadV c₁) (bpHeadT c₁)
          let db := Dprin (entry N 1 j₁ : ℕ∞) BZero
          have hPR : RTPS (Pred N) := RTPS_Pred N hR
          have hPL : Lng (Pred N) < Lng N := by
            rw [length_Pred N hlen]
            omega
          have hIH : ∀ k, Marked (Pred N) k →
              ∀ v ∈ flatIdx (Mark (Pred N) k),
                v ≤ (row1Bound (Pred N) k : ℕ∞) := by
            intro k hk
            exact ih (Lng (Pred N)) (by omega) (Pred N) k hPR hk rfl
          have heq := Trans_Mark_mono_equations N hR hlen hmono
          by_cases ht₁zero : t₁ = BZero
          · have hMark : Mark N m =
                if m == 0 then Dprin 0 db else db := by
              simpa [j₁, jp, jm, t₁, c₁, c₂, db, ht₁zero] using heq.2 m
            intro v hv
            by_cases hm0 : m = 0
            · subst m
              have hMark0 : Mark N 0 = Dprin 0 db := by
                simpa using hMark
              rw [hMark0] at hv
              simp only [flatIdx_Dprin, db, flatIdx_BZero,
                Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] at hv
              rcases hv with rfl | hv
              · exact bot_le
              · have hvlast : v = (entry N 1 j₁ : ℕ∞) := by
                  simpa only [db, flatIdx_Dprin, flatIdx_BZero,
                    Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] using hv
                subst v
                exact coe_entry_le_row1Bound N (m := 0) (j := j₁)
                  (Nat.zero_le _) (by simp [j₁, lastIdx])
            · have hvlast : v = (entry N 1 j₁ : ℕ∞) := by
                have hMarkDb : Mark N m = db := by simpa [hm0] using hMark
                rw [hMarkDb] at hv
                simpa only [db, flatIdx_Dprin, flatIdx_BZero,
                  Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] using hv
              subst v
              exact coe_entry_le_row1Bound N (m := m) (j := j₁)
                (by simpa [j₁, lastIdx] using hmLast)
                (by simp [j₁, lastIdx])
          · have hp : hasParent N 0 (Lng N - 1) = true :=
              mono_hasParent_row0 N hN hmono (Lng N - 1) (by omega) (by omega)
            have hjpLt : jp < j₁ := by
              simpa [jp, j₁, lastParent, lastIdx] using
                parent_lt_of_hasParent N 0 (Lng N - 1) hp
            have hjpLast : jp ≤ Lng N - 1 := by
              simpa [j₁, lastIdx] using hjpLt.le
            have hjmLe : jm ≤ jp := by exact Adm_le N jp
            have hjmLast : jm ≤ Lng N - 2 := by
              simp [j₁, lastIdx] at hjpLt
              omega
            have hmj₁ : m ≤ j₁ := by simpa [j₁, lastIdx] using hmLast
            have hc₁Marked : Marked (Pred N) jm := by
              simpa [jm, jp, lastParent] using Marked_Pred_Adm N hN hlen hp
            have hc₁TB : c₁ ∈ T_B := by
              simpa [c₁] using Mark_mem_T_B (Pred N) jm hPR hc₁Marked
            have ht₁c₁ : (t₁, c₁) ∈ MarkedB := by
              simpa [t₁, c₁] using
                Trans_Mark_mem_MarkedB (Pred N) jm hPR hc₁Marked
            have hc₁P : ∃ p, c₁ = .trm [p] :=
              marked_component_principal ht₁zero ht₁c₁
            have hc₁ne : c₁ ≠ BZero := by
              obtain ⟨p, hpform⟩ := hc₁P
              rw [hpform]
              simp [BZero]
            have hc₂facts := transC2Core_properties N c₁ hc₁TB hc₁P
            have hc₂TB : c₂ ∈ T_B := by simpa [c₂] using hc₂facts.1
            have hc₂P : ∃ p, c₂ = .trm [p] := by simpa [c₂] using hc₂facts.2
            by_cases hmlt : m < j₁
            · have hmPred : Marked (Pred N) m := by
                apply Marked_Pred N m hN hlen hm
                simpa [j₁, lastIdx] using hmlt
              have hmjp : m ≤ jp := by
                simpa [jp] using marked_le_lastParent N hm hmono hlen
                  (by simpa [j₁, lastIdx] using hmlt)
              have hmjm : m ≤ jm := Adm_max N m jp hm.2.1 hmjp
              have hc₀TB := Mark_mem_T_B (Pred N) m hPR hmPred
              have ht₁c₀ := Trans_Mark_mem_MarkedB (Pred N) m hPR hmPred
              have hc₀P : ∃ p, Mark (Pred N) m = .trm [p] :=
                marked_component_principal ht₁zero ht₁c₀
              cases hhead :
                  (scbContexts (Mark (Pred N) m) (flatBT c₁)).head? with
              | none =>
                  have hMark : Mark N m = db := by
                    simpa [j₁, jp, jm, t₁, c₁, c₂, db,
                      ht₁zero, hmlt, hhead] using heq.2 m
                  intro v hv
                  have hvlast : v = (entry N 1 j₁ : ℕ∞) := by
                    rw [hMark] at hv
                    simpa only [db, flatIdx_Dprin, flatIdx_BZero,
                      Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] using hv
                  subst v
                  exact coe_entry_le_row1Bound N hmj₁
                    (by simp [j₁, lastIdx])
              | some sb =>
                  rcases sb with ⟨s, b⟩
                  have hMark : Mark N m =
                      replaceScb (Mark (Pred N) m) c₁ c₂ := by
                    simpa [j₁, jp, jm, t₁, c₁, c₂, db,
                      ht₁zero, hmlt, hhead, replaceScb] using heq.2 m
                  obtain ⟨so, bo, hdec, hout, _⟩ :=
                    replaceScb_spec hc₀TB hc₁TB hc₁P hc₂TB hc₂P
                      (by
                        have hc₁ptb := (principal_flat_properties hc₁TB hc₁P).1
                        exact ⟨s, b, scbContexts_head_decomp hc₁ptb hhead⟩)
                  have hsub : flatIdx (Mark N m) ⊆
                      flatIdx (Mark (Pred N) m) ∪ flatIdx c₂ := by
                    rw [hMark]
                    exact flatIdx_scb_replacement_subset hout hdec.1 hdec.2.2
                  have hc₀bound : ∀ v ∈ flatIdx (Mark (Pred N) m),
                      v ≤ (row1Bound N m : ℕ∞) := by
                    intro v hv
                    exact (hIH m hmPred v hv).trans (by
                      exact_mod_cast row1Bound_Pred_le N hlen (le_refl m)
                        (by simp [j₁, lastIdx] at hmlt; omega))
                  have hc₁bound : ∀ v ∈ flatIdx c₁,
                      v ≤ (row1Bound N m : ℕ∞) := by
                    intro v hv
                    have hv' : v ∈ flatIdx (Mark (Pred N) jm) := by
                      simpa [c₁] using hv
                    exact (hIH jm hc₁Marked v hv').trans (by
                      exact_mod_cast row1Bound_Pred_le N hlen hmjm hjmLast)
                  have hc₂bound : ∀ v ∈ flatIdx c₂,
                      v ≤ (row1Bound N m : ℕ∞) := by
                    intro v hv
                    have hidx := flatIdx_transC2_subset N (by
                      simpa [transC1, transJm1, transJ0, lastParent, c₁, jm, jp]
                        using hc₁ne) (by simpa [transC2, c₂, transV, transT2,
                          transC1, transJm1, transJ0, lastParent, jm, jp] using hv)
                    simp only [Set.mem_union, Set.mem_insert_iff,
                      Set.mem_singleton_iff] at hidx
                    rcases hidx with hc₁idx | rfl | rfl
                    · exact hc₁bound _ hc₁idx
                    · exact coe_entry_le_row1Bound N hmj₁
                        (by simp [transJ1, lastIdx])
                    · exact coe_entry_le_row1Bound N hmjp
                        (by simpa [transJ0, lastParent, jp] using hjpLast)
                  intro v hv
                  rcases hsub hv with hv | hv
                  · exact hc₀bound v hv
                  · exact hc₂bound v hv
            · have hMark : Mark N m = db := by
                simpa [j₁, jp, jm, t₁, c₁, c₂, db,
                  ht₁zero, hmlt] using heq.2 m
              intro v hv
              have hvlast : v = (entry N 1 j₁ : ℕ∞) := by
                rw [hMark] at hv
                simpa only [db, flatIdx_Dprin, flatIdx_BZero,
                  Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] using hv
              subst v
              exact coe_entry_le_row1Bound N hmj₁
                (by simp [j₁, lastIdx])
        · have hzero : zeroT N = false := by
            simp [zeroT]
            omega
          have hmulti : multiT N = true := by simp [multiT, hzero, hmono]
          let J := N.drop (Pcut N)
          have hcut := Pcut_props N hlen
          have hlast := (trans_multi_last_component N hN hmulti).1
          have hPne : P N ≠ [] := P_nonempty N
          have hidx : (P N).length - 1 < (P N).length := by
            have := List.length_pos_of_ne_nil hPne
            omega
          have hJR : RTPS J := by
            have hh := (RTPS_iff_P_components N hN).1 hR
              ((P N).length - 1) hidx
            dsimp [J]
            rw [← hlast]
            exact hh
          have hmParts := multi_Marked_last_component N m hN hmulti hm
          have hmJ : Marked J (m - Pcut N) := by simpa [J] using hmParts.2
          have hJL : Lng J < Lng N := by
            simp [J]
            exact ⟨List.length_pos_of_ne_nil hN, hcut.1⟩
          have hIHJ := ih (Lng J) (by omega) J (m - Pcut N) hJR hmJ rfl
          have heq := Trans_Mark_multi_equations N hR hmulti
          by_cases hJzero : J = [(0, 0)]
          · have hMark : Mark N m = Dprin 0 BZero := by
              simpa [J, hJzero] using heq.2 m
            intro v hv
            have : v = 0 := by simpa [hMark] using hv
            subst v
            exact bot_le
          · have hMark : Mark N m = Mark J (m - Pcut N) := by
              simpa [J, hJzero] using heq.2 m
            have hboundJ : row1Bound J (m - Pcut N) ≤ row1Bound N m := by
              apply Finset.sup_le
              intro k hk
              have hkI := Finset.mem_Icc.mp hk
              have hJLval : Lng J = Lng N - Pcut N := by simp [J]
              have hklt : k < Lng J := by omega
              have hmshift : m ≤ Pcut N + k := by omega
              have hklast : Pcut N + k ≤ Lng N - 1 := by
                rw [hJLval] at hklt
                omega
              calc
                entry J 1 k = entry N 1 (Pcut N + k) := by
                  simp [J, entry_drop, Nat.add_comm]
                _ ≤ row1Bound N m :=
                  entry_le_row1Bound N hmshift hklast
            intro v hv
            have hvJ : v ∈ flatIdx (Mark J (m - Pcut N)) := by
              simpa [hMark] using hv
            exact (hIHJ v hvJ).trans (by exact_mod_cast hboundJ)

/-- Between the admissible predecessor of a column and that column, row 1 is
monotone.  This is the numerical content of the consecutive non-admissible
links used in condition (VI). -/
theorem entry_le_of_Adm_le (M : PS) {j a : ℕ}
    (hjL : j < Lng M) (ha : Adm M j ≤ a) (haj : a ≤ j) :
    entry M 1 a ≤ entry M 1 j := by
  have hstep : ∀ k, Adm M j ≤ k → k < j →
      entry M 1 k < entry M 1 (k + 1) := by
    intro k hak hkj
    have hkadm : adm M (k + 1) = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hk
      have hmax := Adm_max M (k + 1) j hk (by omega)
      omega
    have hnadm : nadm M (k + 1) = true := by
      simpa [adm] using hkadm
    have hkL : k + 1 < Lng M := by omega
    have hpair : nextR M 1 k (k + 1) = true ∧
        nextR M 1 (k + 1) (k + 2) = true := by
      have hn := hnadm
      simp only [nadm, Bool.or_eq_true, decide_eq_true_eq,
        Bool.and_eq_true] at hn
      rcases hn with hn | hn
      · omega
      · simpa only [Nat.add_sub_cancel] using hn
    have hn : nextrel1 M k (k + 1) = true := by
      simpa [nextR] using hpair.1
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hn
    exact hn.1.1.2
  apply (Nat.le_induction (m := a)
    (P := fun k _ => k ≤ j → entry M 1 a ≤ entry M 1 k))
  · intro _
    exact le_rfl
  · intro k hak ih hksucc
    exact (ih (by omega)).trans (hstep k (ha.trans hak) (by omega)).le
  · exact haj
  · exact le_rfl

/-- A nonzero term is below a principal zero-body term as soon as its first
principal index is smaller. -/
theorem lessBT_Dprin_of_bpHeadV_lt {t : BT} {v : ℕ∞}
    (ht : t ≠ BZero) (hv : bpHeadV t < v) :
    lessBT t (Dprin v BZero) = true := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => exact (ht rfl).elim
  | cons p ps =>
      rcases p with ⟨u, a⟩
      simp only [bpHeadV] at hv
      simp only [lessBT, Dprin, lessBPList, lessBP, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact Or.inl (Or.inl hv)

/-- The body comparison required by the condition-(VI) branch.  All indices
inside `t₂` come from the marked predecessor translation and are bounded by
the row-1 value immediately before the final column. -/
theorem transCondVI_body_bound (M : PS)
    (hR : RTPS M) (hmono : monoT M = true)
    (hj₁ : 0 < transJ1 M) (hVI : transCondVI M = true) :
    lessBT (transT2 M)
      (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero) = true := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by simpa [transJ1, lastIdx] using hj₁
  have hVI' := hVI
  simp only [transCondVI, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hVI'
  have hjpLast : lastParent M = Lng M - 2 := by
    have hs := hVI'.2
    simp only [lastIdx] at hs
    omega
  have hentrySucc :
      entry M 1 (lastParent M) + 1 = entry M 1 (lastIdx M) := hVI'.1.2
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hmarked : Marked (Pred M) (Adm M (lastParent M)) :=
    Marked_Pred_Adm M hM hlen hp
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hrow : row1Bound (Pred M) (Adm M (lastParent M)) ≤
      entry M 1 (lastParent M) := by
    apply Finset.sup_le
    intro k hk
    have hkI := Finset.mem_Icc.mp hk
    have hpredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
    have hkLt : k < Lng M - 1 := by
      rw [hpredLen] at hkI
      omega
    have hkParent : k ≤ lastParent M := by
      rw [hpredLen] at hkI
      omega
    calc
      entry (Pred M) 1 k = entry M 1 k := entry_Pred M 1 k hkLt
      _ ≤ entry M 1 (lastParent M) :=
        entry_le_of_Adm_le M (by omega) hkI.1 hkParent
  by_cases ht₂ : transT2 M = BZero
  · simp [ht₂, BZero, Dprin, lessBT, lessBPList]
  · have hbodyMem : bpHeadV (transT2 M) ∈ flatIdx (transC1 M) :=
      flatIdx_bpHeadT_subset (transC1 M) (bpHeadV_mem_flatIdx ht₂)
    have hmarkMem : bpHeadV (transT2 M) ∈
        flatIdx (Mark (Pred M) (Adm M (lastParent M))) := by
      simpa [transC1, transJm1, transJ0] using hbodyMem
    have hidxBound : bpHeadV (transT2 M) ≤
        (row1Bound (Pred M) (Adm M (lastParent M)) : ℕ∞) :=
      Mark_flatIdx_bound (Pred M) (Adm M (lastParent M))
        hpredR hmarked _ hmarkMem
    have hrowCoe :
        (row1Bound (Pred M) (Adm M (lastParent M)) : ℕ∞) ≤
          (entry M 1 (lastParent M) : ℕ∞) := by
      exact_mod_cast hrow
    have hentryLt : entry M 1 (lastParent M) <
        entry M 1 (lastIdx M) := by omega
    have hidxLt : bpHeadV (transT2 M) <
        (entry M 1 (lastIdx M) : ℕ∞) :=
      lt_of_le_of_lt (hidxBound.trans hrowCoe) (by exact_mod_cast hentryLt)
    apply lessBT_Dprin_of_bpHeadV_lt ht₂
    simpa [transJ1] using hidxLt

/-- Full strict comparison of the two principal terms in the recursive mono
translation branch. -/
theorem transC1_lessBT_transC2_full (M : PS)
    (hR : RTPS M) (hmono : monoT M = true)
    (hj₁ : 0 < transJ1 M) (ht₁ : transT1 M ≠ BZero) :
    lessBT (transC1 M) (transC2 M) = true := by
  apply transC1_lessBT_transC2_of_condVI M hR hmono hj₁ ht₁
  exact transCondVI_body_bound M hR hmono hj₁

/-- The three claims of the article's `c₁`/`c₂` proposition. -/
theorem c1_c2_order (M : PS)
    (hR : RTPS M) (hmono : monoT M = true)
    (hj₁ : 0 < transJ1 M) (ht₁ : transT1 M ≠ BZero) :
    (PB (transC1 M)).length = 1 ∧
      (PB (transC2 M)).length = 1 ∧
      lessBT (transC1 M) (transC2 M) = true := by
  exact ⟨transC1_single_principal M hR hmono hj₁ ht₁,
    transC2_single_principal M,
    transC1_lessBT_transC2_full M hR hmono hj₁ ht₁⟩

#print axioms transC2_single_principal
#print axioms isPTB_str_imp_PB_length_one
#print axioms transC1_single_principal
#print axioms principal_reconstruct
#print axioms lessBT_addBT_self
#print axioms transC1_lessBT_transC2_of_condVI
#print axioms flatIdx_transC2Core_subset
#print axioms Mark_flatIdx_bound
#print axioms entry_le_of_Adm_le
#print axioms transCondVI_body_bound
#print axioms transC1_lessBT_transC2_full
#print axioms c1_c2_order

end PSS
