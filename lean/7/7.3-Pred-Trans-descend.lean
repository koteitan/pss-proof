import «7».«7.3-c1-c2-order»
import «7».«7.3-Trans-preserves-zeroT»

/-!
# §7.3 命題（`Pred` による `Trans` の降下）

- 原文: `tmp/content.md` の同名命題
- Isabelle: `Trans_Pred_multi_last`, `m_7_3_Pred_Trans_descend`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-! ## scb 文脈における狭義単調性 -/

private def flatBPSeqLt : List BP → List Sym
  | [] => []
  | p :: ps => flatBP p ++ flatBPTail ps

private def parenWeightLt : Sym → ℤ
  | .lp => 1
  | .rp => -1
  | _ => 0

private def parenSumLt (xs : List Sym) : ℤ :=
  (xs.map parenWeightLt).sum

@[simp] private theorem parenSumLt_nil : parenSumLt [] = 0 := rfl

@[simp] private theorem parenSumLt_cons (x : Sym) (xs : List Sym) :
    parenSumLt (x :: xs) = parenWeightLt x + parenSumLt xs := by
  simp [parenSumLt]

@[simp] private theorem parenSumLt_append (xs ys : List Sym) :
    parenSumLt (xs ++ ys) = parenSumLt xs + parenSumLt ys := by
  simp [parenSumLt]

private def PrefixNonnegLt (xs : List Sym) : Prop :=
  ∀ pre rest, xs = pre ++ rest → 0 ≤ parenSumLt pre

private def BalancedLt (xs : List Sym) : Prop :=
  parenSumLt xs = 0 ∧ PrefixNonnegLt xs

private theorem balancedLt_nil : BalancedLt [] := by
  refine ⟨rfl, ?_⟩
  intro pre rest h
  simp at h
  simp [h.1, parenSumLt]

private theorem prefixNonnegLt_append {xs ys : List Sym}
    (hxs : PrefixNonnegLt xs) (hsum : parenSumLt xs = 0)
    (hys : PrefixNonnegLt ys) : PrefixNonnegLt (xs ++ ys) := by
  intro pre rest h
  rcases List.append_eq_append_iff.mp h with
      ⟨mid, hpre, hysplit⟩ | ⟨mid, hxsplit, _⟩
  · rw [hpre, parenSumLt_append, hsum, zero_add]
    exact hys mid rest hysplit
  · exact hxs pre mid hxsplit

private theorem balancedLt_append {xs ys : List Sym}
    (hxs : BalancedLt xs) (hys : BalancedLt ys) :
    BalancedLt (xs ++ ys) :=
  ⟨by simp [hxs.1, hys.1],
    prefixNonnegLt_append hxs.2 hxs.1 hys.2⟩

private theorem prefixNonnegLt_cons (x : Sym) (xs : List Sym)
    (hx : 0 ≤ parenWeightLt x) (hxs : PrefixNonnegLt xs) :
    PrefixNonnegLt (x :: xs) := by
  intro pre rest h
  cases pre with
  | nil => simp [parenSumLt]
  | cons y pre =>
      have hy : y = x := by simpa using (congrArg List.head? h).symm
      subst y
      have htail : xs = pre ++ rest := by simpa using h
      have hp := hxs pre rest htail
      simp only [parenSumLt_cons]
      omega

private theorem balancedLt_cons_zero (x : Sym) (xs : List Sym)
    (hx : parenWeightLt x = 0) (hxs : BalancedLt xs) :
    BalancedLt (x :: xs) := by
  refine ⟨by simp [hx, hxs.1], ?_⟩
  exact prefixNonnegLt_cons x xs (by omega) hxs.2

private theorem balancedLt_singleton_zero (x : Sym)
    (hx : parenWeightLt x = 0) : BalancedLt [x] := by
  simpa using balancedLt_cons_zero x [] hx balancedLt_nil

private theorem prefixNonnegLt_wrap {xs : List Sym}
    (hxs : BalancedLt xs) : PrefixNonnegLt (.lp :: xs ++ [.rp]) := by
  have hfront : PrefixNonnegLt (.lp :: xs) :=
    prefixNonnegLt_cons .lp xs (by simp [parenWeightLt]) hxs.2
  intro pre rest h
  rcases List.append_eq_append_iff.mp h with
      ⟨mid, hpre, hone⟩ | ⟨mid, hfrontSplit, _⟩
  · cases mid with
    | nil =>
        rw [hpre]
        simp [hxs.1, parenWeightLt]
    | cons a as =>
        cases as with
        | nil =>
            have ha : a = .rp := by
              simpa using (congrArg List.head? hone).symm
            subst a
            have hpre' : pre = (.lp :: xs) ++ [.rp] := by
              simpa using hpre
            rw [hpre']
            simp [hxs.1, parenWeightLt]
        | cons z zs => simp at hone
  · exact hfront pre mid hfrontSplit

private theorem balancedLt_wrap {xs : List Sym} (hxs : BalancedLt xs) :
    BalancedLt (.lp :: xs ++ [.rp]) := by
  refine ⟨by simp [hxs.1, parenWeightLt], prefixNonnegLt_wrap hxs⟩

private def FlatListBalancedLt (ps : List BP) : Prop :=
  BalancedLt (flatBPTail ps) ∧ BalancedLt (flatBPSeqLt ps)

private theorem flatBalancedLt (t : BT) : BalancedLt (flatBT t) := by
  exact BT.rec
    (motive_1 := fun t => BalancedLt (flatBT t))
    (motive_2 := fun p => BalancedLt (flatBP p))
    (motive_3 := FlatListBalancedLt)
    (fun ps hps => by
      cases ps with
      | nil =>
          simpa [flatBT] using balancedLt_singleton_zero .zero rfl
      | cons p ps =>
          cases ps with
          | nil => simpa [flatBT, flatBPSeqLt, flatBPTail] using hps.2
          | cons q qs =>
              simpa [flatBT, flatBPSeqLt] using balancedLt_wrap hps.2)
    (fun u a ha => by
      simpa [flatBP] using balancedLt_cons_zero (.dsym u) (flatBT a) rfl ha)
    ⟨balancedLt_nil, balancedLt_nil⟩
    (fun p ps hp hps => by
      have hcm := balancedLt_singleton_zero .cm rfl
      refine ⟨?_, ?_⟩
      · simpa [flatBPTail, List.append_assoc] using
          balancedLt_append hcm (balancedLt_append hp hps.1)
      · simpa [flatBPSeqLt] using balancedLt_append hp hps.1)
    t

private theorem flatBPSeqBalancedLt (ps : List BP) :
    BalancedLt (flatBPSeqLt ps) := by
  cases ps with
  | nil => exact balancedLt_nil
  | cons p ps =>
      rcases p with ⟨u, a⟩
      have hp : BalancedLt (flatBP (.db u a)) := by
        simpa [flatBP] using
          balancedLt_cons_zero (.dsym u) (flatBT a) rfl (flatBalancedLt a)
      have htail : BalancedLt (flatBPTail ps) := by
        induction ps with
        | nil => exact balancedLt_nil
        | cons q qs ih =>
            rcases q with ⟨v, c⟩
            have hq : BalancedLt (flatBP (.db v c)) := by
              simpa [flatBP] using
                balancedLt_cons_zero (.dsym v) (flatBT c) rfl (flatBalancedLt c)
            have hcm := balancedLt_singleton_zero .cm rfl
            simpa [flatBPTail, List.append_assoc] using
              balancedLt_append hcm (balancedLt_append hq ih)
      simpa [flatBPSeqLt] using balancedLt_append hp htail

private theorem flatBPBalancedLt (p : BP) : BalancedLt (flatBP p) := by
  rcases p with ⟨u, a⟩
  simpa [flatBP] using
    balancedLt_cons_zero (.dsym u) (flatBT a) rfl (flatBalancedLt a)

private def ReplaceLtBT (t : BT) : Prop :=
  ∀ pr pr' s b,
    flatBT t = s ++ flatBP pr ++ b →
    lessBP pr pr' = true →
    ∃ t', flatBT t' = s ++ flatBP pr' ++ b ∧
      lessBT t t' = true

private def ReplaceLtBP (p : BP) : Prop :=
  ∀ pr pr' s b,
    flatBP p = s ++ flatBP pr ++ b →
    lessBP pr pr' = true →
    ∃ p', flatBP p' = s ++ flatBP pr' ++ b ∧
      lessBP p p' = true

private def ReplaceLtList (ps : List BP) : Prop :=
  ∀ pr pr' s b,
    flatBPSeqLt ps = s ++ flatBP pr ++ b →
    lessBP pr pr' = true →
    ∃ ps', flatBPSeqLt ps' = s ++ flatBP pr' ++ b ∧
      ps'.length = ps.length ∧ lessBPList ps ps' = true

/-- Replacing a complete principal-code occurrence by a strictly larger
principal code strictly increases the enclosing Buchholz term.  This is
stronger than the scb-specialized extension lemma: no condition on the common
suffix is needed once unique readability has localized the occurrence. -/
theorem flat_principal_replacement_lt (t : BT) : ReplaceLtBT t := by
  exact BT.rec
    (motive_1 := ReplaceLtBT)
    (motive_2 := ReplaceLtBP)
    (motive_3 := ReplaceLtList)
    (fun ps ih pr pr' s b hflat hlt => by
      cases ps with
      | nil =>
          rcases pr with ⟨u, a⟩
          cases s <;> simp [flatBT, flatBP] at hflat
      | cons p ps =>
          cases ps with
          | nil =>
              have hseq : flatBPSeqLt [p] = s ++ flatBP pr ++ b := by
                simpa [flatBPSeqLt, flatBPTail] using hflat
              rcases ih pr pr' s b hseq hlt with
                ⟨ps', hps'flat, hps'len, hps'lt⟩
              cases ps' with
              | nil => simp at hps'len
              | cons p' rest =>
                  cases rest with
                  | nil =>
                      refine ⟨.trm [p'], ?_, ?_⟩
                      · simpa [flatBT, flatBPSeqLt, flatBPTail] using hps'flat
                      · simpa [lessBT] using hps'lt
                  | cons q' qs' => simp at hps'len
          | cons q qs =>
              have hmulti :
                  .lp :: flatBPSeqLt (p :: q :: qs) ++ [.rp] =
                    s ++ flatBP pr ++ b := by
                simpa [flatBT, flatBPSeqLt] using hflat
              cases s with
              | nil =>
                  rcases pr with ⟨u, a⟩
                  simp [flatBP] at hmulti
              | cons x s' =>
                  have hx : x = .lp := by
                    simpa using (congrArg List.head? hmulti).symm
                  subst x
                  have htail :
                      flatBPSeqLt (p :: q :: qs) ++ [.rp] =
                        s' ++ flatBP pr ++ b := by
                    simpa using hmulti
                  have hbne : b ≠ [] := by
                    intro hb
                    subst b
                    have hbodyBal := flatBPSeqBalancedLt (p :: q :: qs)
                    have hsplit :
                        flatBPSeqLt (p :: q :: qs) ++ [.rp] =
                          s' ++ (flatBP pr ++ []) := by
                      simpa [List.append_assoc] using htail
                    rcases List.append_eq_append_iff.mp hsplit with
                        ⟨mid, _, hone⟩ | ⟨mid, hbodySplit, _⟩
                    · rcases pr with ⟨v, c⟩
                      cases mid <;> simp [flatBP] at hone
                    · have hsnonneg := hbodyBal.2 s' mid hbodySplit
                      have hprBal := flatBPBalancedLt pr
                      have hsum := congrArg parenSumLt htail
                      simp [hbodyBal.1, hprBal.1, parenWeightLt] at hsum
                      omega
                  let b' := b.dropLast
                  let z := b.getLast hbne
                  have hb : b' ++ [z] = b := List.dropLast_append_getLast hbne
                  have hlast : z = .rp := by
                    have hlastEq := congrArg List.getLast? htail
                    rw [← hb] at hlastEq
                    simpa [b', z] using hlastEq.symm
                  have hbRP : b' ++ [.rp] = b := by simpa [hlast] using hb
                  have hsnoc :
                      flatBPSeqLt (p :: q :: qs) ++ [.rp] =
                        (s' ++ flatBP pr ++ b') ++ [.rp] := by
                    rw [← hbRP] at htail
                    simpa [List.append_assoc] using htail
                  have hbody : flatBPSeqLt (p :: q :: qs) =
                      s' ++ flatBP pr ++ b' :=
                    List.append_cancel_right hsnoc
                  rcases ih pr pr' s' b' hbody hlt with
                    ⟨ps', hps'flat, hps'len, hps'lt⟩
                  cases ps' with
                  | nil => simp at hps'len
                  | cons p' rest =>
                      cases rest with
                      | nil => simp at hps'len
                      | cons q' qs' =>
                          refine ⟨.trm (p' :: q' :: qs'), ?_, ?_⟩
                          · rw [← hbRP]
                            change
                              .lp :: (flatBP p' ++ flatBPTail (q' :: qs')) ++ [.rp] =
                                (.lp :: s') ++ flatBP pr' ++ (b' ++ [.rp])
                            have hpsExplicit :
                                flatBP p' ++ flatBPTail (q' :: qs') =
                                  s' ++ flatBP pr' ++ b' := by
                              simpa [flatBPSeqLt] using hps'flat
                            rw [hpsExplicit]
                            simp [List.append_assoc]
                          · simpa [lessBT] using hps'lt)
    (fun u a ih pr pr' s b hflat hlt => by
      cases s with
      | nil =>
          have hcancel : flatBP (.db u a) ++ [] = flatBP pr ++ b := by
            simpa [flatBP] using hflat
          rcases flatBP_cancel hcancel with ⟨hp, hb⟩
          have hpeq : .db u a = pr := flatBP_injective hp
          subst pr
          subst b
          exact ⟨pr', by simp, hlt⟩
      | cons x s' =>
          have hx : x = .dsym u := by
            simpa [flatBP] using (congrArg List.head? hflat).symm
          subst x
          have hchild : flatBT a = s' ++ flatBP pr ++ b := by
            simpa [flatBP] using hflat
          rcases ih pr pr' s' b hchild hlt with ⟨a', ha'flat, ha'lt⟩
          refine ⟨.db u a', ?_, ?_⟩
          · simpa [flatBP] using congrArg (fun xs => .dsym u :: xs) ha'flat
          · simp [lessBP, ha'lt])
    (by
      intro pr pr' s b hflat
      rcases pr with ⟨u, a⟩
      simp [flatBPSeqLt, flatBP] at hflat)
    (fun p ps ihp ihps pr pr' s b hflat hlt => by
      have hseq : flatBP p ++ flatBPTail ps =
          s ++ flatBP pr ++ b := by
        simpa [flatBPSeqLt] using hflat
      rcases flatBP_localize_append hseq with
          ⟨inside, hpflat, rfl⟩ | ⟨after, rfl, htail⟩
      · rcases ihp pr pr' s inside hpflat hlt with
          ⟨p', hp'flat, hp'lt⟩
        refine ⟨p' :: ps, ?_, by simp, ?_⟩
        · simp [flatBPSeqLt, hp'flat, List.append_assoc]
        · simp [lessBPList, hp'lt]
      · cases ps with
        | nil =>
            rcases pr with ⟨v, c⟩
            cases after <;> simp [flatBPTail, flatBP] at htail
        | cons q qs =>
            cases after with
            | nil =>
                rcases pr with ⟨v, c⟩
                simp [flatBPTail, flatBP] at htail
            | cons x after' =>
                have hx : x = .cm := by
                  simpa [flatBPTail] using (congrArg List.head? htail).symm
                subst x
                have hrest : flatBPSeqLt (q :: qs) =
                    after' ++ flatBP pr ++ b := by
                  simpa [flatBPTail, flatBPSeqLt] using htail
                rcases ihps pr pr' after' b hrest hlt with
                  ⟨ps', hps'flat, hps'len, hps'lt⟩
                have hps'ne : ps' ≠ [] := by
                  intro hz
                  subst ps'
                  simp at hps'len
                have htail' : flatBPTail ps' = .cm :: flatBPSeqLt ps' := by
                  cases ps' with
                  | nil => exact (hps'ne rfl).elim
                  | cons q' qs' => simp [flatBPTail, flatBPSeqLt]
                refine ⟨p :: ps', ?_, by simp [hps'len], ?_⟩
                · change
                    flatBP p ++ flatBPTail ps' =
                      (flatBP p ++ (.cm :: after')) ++ flatBP pr' ++ b
                  rw [htail', hps'flat]
                  simp [List.append_assoc]
                · simp [lessBPList, hps'lt])
    t

/-- Strict monotonicity at a fixed scb position. -/
theorem scbext_lessBT {t t' : BT} {s b : List Sym} {cp cp' : BP}
    (ht : flatBT t = s ++ flatBP cp ++ b)
    (ht' : flatBT t' = s ++ flatBP cp' ++ b)
    (_hrp : ∀ x ∈ b, x = .rp)
    (hlt : lessBP cp cp' = true) :
    lessBT t t' = true := by
  rcases flat_principal_replacement_lt t cp cp' s b ht hlt with
    ⟨u, hu, htu⟩
  have hut' : u = t' := flatBT_injective (hu.trans ht'.symm)
  simpa [hut'] using htu

/-! ## 複項分岐における `Pred` の評価 -/

/-- If the final `P` component has more than one column, `Pred` acts inside
that component and the multi recursion for `Trans` keeps the same prefix. -/
theorem Trans_Pred_multi_last (M : PS) (hR : RTPS M)
    (hmulti : multiT M = true)
    (hJlen : 1 < Lng (M.drop (Pcut M))) :
    let A := M.take (Pcut M)
    let J := M.drop (Pcut M)
    Trans (Pred M) = addBT (Trans A)
      (if Pred J == [(0, 0)] then Dprin 0 BZero else Trans (Pred J)) := by
  dsimp only
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
  have hpredSplit : Pred M = A ++ Pred J := by
    have hJlength : Lng J = Lng M - Pcut M := by simp [J]
    have hJlen' := hJlen
    rw [hJlength] at hJlen'
    have hcutLast : Pcut M < Lng M - 1 := by omega
    have hsum : Pcut M + (Lng J - 1) = Lng M - 1 := by
      rw [hJlength]
      omega
    have hpredM : Pred M = M.take (Lng M - 1) := Pred_eq_take M hlen
    have hpredJ : Pred J = J.take (Lng J - 1) := Pred_eq_take J hJlen
    rw [hpredM, hpredJ]
    symm
    change M.take (Pcut M) ++
        (M.drop (Pcut M)).take (Lng J - 1) = M.take (Lng M - 1)
    rw [← List.take_add]
    rw [hsum]
  have hPpred : P (Pred M) = P A ++ [Pred J] := by
    have hlastLenNe : Lng ((P M).getLastD []) ≠ 1 := by
      rw [hlastJ]
      exact Nat.ne_of_gt hJlen
    rw [P_Pred_multi M hM hmulti]
    rw [if_neg hlastLenNe]
    rw [hlastJ, hbutA]
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
    have happ :
        (Pred M).take (Pcut (Pred M)) ++
            (Pred M).drop (Pcut (Pred M)) = Pred M :=
      List.take_append_drop (Pcut (Pred M)) (Pred M)
    rw [hdropPred] at happ
    have happ' :
        (Pred M).take (Pcut (Pred M)) ++ Pred J = A ++ Pred J :=
      happ.trans hpredSplit
    exact List.append_cancel_right happ'
  have heq := (Trans_Mark_multi_equations (Pred M) hpredR hpredMulti).1
  rw [htakePred, hdropPred] at heq
  by_cases hz : Pred J = [(0, 0)]
  · simpa [hz, A, J] using heq
  · simpa [hz, A, J] using heq

/-! ## `Pred` による狭義降下 -/

/-- On reduced pair sequences of length at least two, deleting the final
column strictly decreases the Buchholz translation. -/
theorem Pred_Trans_descend_RTPS (M : PS) (hR : RTPS M)
    (hlen : 1 < Lng M) :
    lessBT (Trans (Pred M)) (Trans M) = true := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      have hM : TPS M := RTPS_TPS M hR
      have hzero : zeroT M = false := by
        simp [zeroT]
        omega
      by_cases hmono : monoT M = true
      · have hmonoEq := (Trans_Mark_mono_equations M hR hlen hmono).1
        by_cases ht₁zero : Trans (Pred M) = BZero
        · have hTrans : Trans M =
              Dprin 0 (Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero) := by
            simpa [ht₁zero] using hmonoEq
          rw [ht₁zero, hTrans]
          simp [BZero, Dprin, lessBT, lessBPList]
        · have hp : hasParent M 0 (Lng M - 1) = true :=
            mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
          have hmarked : Marked (Pred M)
              (Adm M (parent M 0 (Lng M - 1))) :=
            Marked_Pred_Adm M hM hlen hp
          have hpredR : RTPS (Pred M) := RTPS_Pred M hR
          have ht₁TB : Trans (Pred M) ∈ T_B :=
            Trans_mem_T_B (Pred M) hpredR
          have hc₁TB : transC1 M ∈ T_B := by
            simpa [transC1, transJm1, transJ0, lastParent] using
              Mark_mem_T_B (Pred M) _ hpredR hmarked
          have ht₁c₁ : (Trans (Pred M), transC1 M) ∈ MarkedB := by
            simpa [transC1, transJm1, transJ0, lastParent] using
              Trans_Mark_mem_MarkedB (Pred M) _ hpredR hmarked
          have hc₁P : ∃ p, transC1 M = .trm [p] :=
            marked_component_principal ht₁zero ht₁c₁
          have hc₂facts := transC2Core_properties M (transC1 M) hc₁TB hc₁P
          have hc₂TB : transC2 M ∈ T_B := by
            simpa [transC2, transV, transT2] using hc₂facts.1
          have hc₂P : ∃ p, transC2 M = .trm [p] := by
            simpa [transC2, transV, transT2] using hc₂facts.2
          have hTrans : Trans M =
              replaceScb (Trans (Pred M)) (transC1 M) (transC2 M) := by
            simpa [ht₁zero, transC1, transC2, transV, transT2,
              transJm1, transJ0, lastParent] using hmonoEq
          rcases replaceScb_spec ht₁TB hc₁TB hc₁P hc₂TB hc₂P ht₁c₁ with
            ⟨s, b, hd, hout, _⟩
          rcases hc₁P with ⟨p₁, hp₁⟩
          rcases hc₂P with ⟨p₂, hp₂⟩
          have hj₁ : 0 < transJ1 M := by
            simp [transJ1, lastIdx]
            omega
          have hprincipal :=
            transC1_lessBT_transC2_full M hR hmono hj₁
              (by simpa [transT1] using ht₁zero)
          have hp₁p₂ : lessBP p₁ p₂ = true := by
            simpa [hp₁, hp₂, lessBT, lessBPList] using hprincipal
          rw [hTrans]
          apply scbext_lessBT
          · simpa [hp₁, flatBT] using hd.1
          · simpa [hp₂, flatBT] using hout
          · exact hd.2.2
          · exact hp₁p₂
      · have hmonoFalse : monoT M = false :=
          Bool.eq_false_of_not_eq_true hmono
        have hmulti : multiT M = true := by
          simp [multiT, hzero, hmonoFalse]
        let A := M.take (Pcut M)
        let J := M.drop (Pcut M)
        have hcut := Pcut_props M hlen
        have hJlength : Lng J = Lng M - Pcut M := by simp [J]
        have hJpos : 0 < Lng J := by
          rw [hJlength]
          omega
        have hJlt : Lng J < Lng M := by
          rw [hJlength]
          omega
        have hlast := trans_multi_last_component M hM hmulti
        have hPne : P M ≠ [] := P_nonempty M
        have hidx : (P M).length - 1 < (P M).length := by
          have := List.length_pos_of_ne_nil hPne
          omega
        have hlastR := (RTPS_iff_P_components M hM).1 hR
            ((P M).length - 1) hidx
        have hJR : RTPS J := by
          rw [hlast.1] at hlastR
          simpa [J] using hlastR
        have hJT : TPS J := RTPS_TPS J hJR
        have hTransEq := (Trans_Mark_multi_equations M hR hmulti).1
        by_cases hJgt : 1 < Lng J
        · have hJne : J ≠ [(0, 0)] := by
            intro hz
            rw [hz] at hJgt
            simp at hJgt
          have hTrans : Trans M = addBT (Trans A) (Trans J) := by
            simpa [A, J, hJne] using hTransEq
          have hPredTrans := Trans_Pred_multi_last M hR hmulti
            (by simpa [J] using hJgt)
          have hPredTrans' : Trans (Pred M) = addBT (Trans A)
              (if Pred J == [(0, 0)] then Dprin 0 BZero
               else Trans (Pred J)) := by
            simpa [A, J] using hPredTrans
          have hinner : lessBT
              (if Pred J == [(0, 0)] then Dprin 0 BZero
               else Trans (Pred J)) (Trans J) = true := by
            by_cases hPredZero : Pred J = [(0, 0)]
            · have hpredJT : TPS (Pred J) := Pred_TPS J hJT
              have hpredZeroT : zeroT (Pred J) = true := by
                simp [hPredZero, zeroT, entry]
              have htPredZero : Trans (Pred J) = BZero :=
                (Trans_preserves_zeroT (Pred J) hpredJT).mp hpredZeroT
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
                rcases hJnonmulti with hz | hm
                · rw [hJzeroFalse] at hz
                  contradiction
                · exact hm
              have hJEq := (Trans_Mark_mono_equations J hJR hJgt hJmono).1
              have hTransJ : Trans J =
                  Dprin 0 (Dprin (entry J 1 (lastIdx J) : ℕ∞) BZero) := by
                simpa [htPredZero] using hJEq
              rw [hTransJ]
              simp [hPredZero, BZero, Dprin, lessBT, lessBPList, lessBP]
            · have hih : lessBT (Trans (Pred J)) (Trans J) = true := by
                exact ih (Lng J) (by simpa [hn] using hJlt) J hJR hJgt rfl
              simpa [hPredZero] using hih
          rw [hPredTrans', hTrans]
          exact addBT_lt_right_bf _ _ _ hinner
        · have hJone : Lng J = 1 := by omega
          have hcutLast : Pcut M = Lng M - 1 := by
            rw [hJlength] at hJone
            omega
          have hPredA : Pred M = A := by
            rw [Pred_eq_take M hlen]
            simp [A, hcutLast]
          by_cases hJzero : J = [(0, 0)]
          · have hTrans : Trans M = addBT (Trans A) (Dprin 0 BZero) := by
              simpa [A, J, hJzero] using hTransEq
            rw [hPredA, hTrans]
            exact lessBT_addBT_self _ _ (by simp [Dprin, BZero])
          · have hzeroJ : zeroT J = false := by
              apply Bool.eq_false_of_not_eq_true
              intro hz
              obtain ⟨v, hv⟩ := (one_column J hJT).1 ⟨hJone, hJR⟩
              have hv0 : v = 0 := by
                simpa [hv, zeroT, entry] using hz
              exact hJzero (by simpa [hv0] using hv)
            have hTransJne : Trans J ≠ BZero := by
              intro ht
              have hz := (Trans_preserves_zeroT J hJT).mpr ht
              rw [hzeroJ] at hz
              contradiction
            have hTrans : Trans M = addBT (Trans A) (Trans J) := by
              simpa [A, J, hJzero] using hTransEq
            rw [hPredA, hTrans]
            exact lessBT_addBT_self _ _ hTransJne

/-- Article statement: the descent holds for every pair sequence, after
transporting the reduced proof along the two-step reduction fixed point. -/
theorem Pred_Trans_descend (M : PS) (hM : TPS M)
    (hlen : 1 < Lng M) :
    lessBT (Trans (Pred M)) (Trans M) = true := by
  have hRM : TPS (Red M) := Red_TPS M hM
  have hRR : RTPS (Red (Red M)) := Red2 M hM
  have hRRlen : 1 < Lng (Red (Red M)) := by
    rw [Lng_Red_invariance (Red M) hRM, Lng_Red_invariance M hM]
    exact hlen
  have hdesc := Pred_Trans_descend_RTPS (Red (Red M)) hRR hRRlen
  have hPredM : TPS (Pred M) := Pred_TPS M hM
  have hPredRM : TPS (Pred (Red M)) := Pred_TPS (Red M) hRM
  have hleft : Trans (Pred M) = Trans (Pred (Red (Red M))) := by
    calc
      Trans (Pred M) = Trans (Red (Pred M)) := Trans_Red (Pred M) hPredM
      _ = Trans (Pred (Red M)) := by rw [Red_Pred M hM]
      _ = Trans (Red (Pred (Red M))) :=
        Trans_Red (Pred (Red M)) hPredRM
      _ = Trans (Pred (Red (Red M))) := by rw [Red_Pred (Red M) hRM]
  have hright : Trans M = Trans (Red (Red M)) := by
    calc
      Trans M = Trans (Red M) := Trans_Red M hM
      _ = Trans (Red (Red M)) := Trans_Red (Red M) hRM
  rw [hleft, hright]
  exact hdesc

/-- Isabelle-compatible name of the preceding proposition. -/
theorem m_7_3_Pred_Trans_descend (M : PS) (hM : TPS M)
    (hlen : 1 < Lng M) :
    lessBT (Trans (Pred M)) (Trans M) = true :=
  Pred_Trans_descend M hM hlen

#print axioms flat_principal_replacement_lt
#print axioms scbext_lessBT
#print axioms Trans_Pred_multi_last
#print axioms Pred_Trans_descend_RTPS
#print axioms Pred_Trans_descend
#print axioms m_7_3_Pred_Trans_descend

end PSS
