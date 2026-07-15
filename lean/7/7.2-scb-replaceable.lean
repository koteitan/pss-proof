import PSS.Flat

/-!
# §7.2 命題（scb 分解の置換可能性）

Isabelle の `gensurg_main`, `gensurg_image_BT`,
`y3u_p_7_2_scb_replaceable` に対応する。原文命題のゼロ項での欠落
（A12）を反例で固定し、訂正版を証明する。
-/

namespace PSS

private def flatBPSeq : List BP → List Sym
  | [] => []
  | p :: ps => flatBP p ++ flatBPTail ps

private def parenWeight : Sym → ℤ
  | .lp => 1
  | .rp => -1
  | _ => 0

private def parenSum (xs : List Sym) : ℤ :=
  (xs.map parenWeight).sum

@[simp] private theorem parenSum_nil : parenSum [] = 0 := rfl

@[simp] private theorem parenSum_cons (x : Sym) (xs : List Sym) :
    parenSum (x :: xs) = parenWeight x + parenSum xs := by
  simp [parenSum]

@[simp] private theorem parenSum_append (xs ys : List Sym) :
    parenSum (xs ++ ys) = parenSum xs + parenSum ys := by
  simp [parenSum]

private def PrefixNonneg (xs : List Sym) : Prop :=
  ∀ pre rest, xs = pre ++ rest → 0 ≤ parenSum pre

private def Balanced (xs : List Sym) : Prop :=
  parenSum xs = 0 ∧ PrefixNonneg xs

private theorem balanced_nil : Balanced [] := by
  refine ⟨rfl, ?_⟩
  intro pre rest h
  simp at h
  simp [h.1]

private theorem prefixNonneg_append {xs ys : List Sym}
    (hxs : PrefixNonneg xs) (hsum : parenSum xs = 0)
    (hys : PrefixNonneg ys) : PrefixNonneg (xs ++ ys) := by
  intro pre rest h
  rcases List.append_eq_append_iff.mp h with
      ⟨mid, hpre, hysplit⟩ | ⟨mid, hxsplit, hrest⟩
  · rw [hpre, parenSum_append, hsum, zero_add]
    exact hys mid rest hysplit
  · exact hxs pre mid hxsplit

private theorem balanced_append {xs ys : List Sym}
    (hxs : Balanced xs) (hys : Balanced ys) : Balanced (xs ++ ys) := by
  exact ⟨by simp [hxs.1, hys.1],
    prefixNonneg_append hxs.2 hxs.1 hys.2⟩

private theorem prefixNonneg_cons (x : Sym) (xs : List Sym)
    (hx : 0 ≤ parenWeight x) (hxs : PrefixNonneg xs) :
    PrefixNonneg (x :: xs) := by
  intro pre rest h
  cases pre with
  | nil => simp
  | cons y pre =>
      have hy : y = x := by simpa using (congrArg List.head? h).symm
      subst y
      have htail : xs = pre ++ rest := by simpa using h
      have hp := hxs pre rest htail
      simp only [parenSum_cons]
      omega

private theorem balanced_cons_zero (x : Sym) (xs : List Sym)
    (hx : parenWeight x = 0) (hxs : Balanced xs) :
    Balanced (x :: xs) := by
  refine ⟨by simp [hx, hxs.1], prefixNonneg_cons x xs (by omega) hxs.2⟩

private theorem balanced_singleton_zero (x : Sym) (hx : parenWeight x = 0) :
    Balanced [x] := by
  simpa using balanced_cons_zero x [] hx balanced_nil

private theorem prefixNonneg_wrap {xs : List Sym} (hxs : Balanced xs) :
    PrefixNonneg (.lp :: xs ++ [.rp]) := by
  have hfront : PrefixNonneg (.lp :: xs) :=
    prefixNonneg_cons .lp xs (by simp [parenWeight]) hxs.2
  intro pre rest h
  rcases List.append_eq_append_iff.mp h with
      ⟨mid, hpre, hone⟩ | ⟨mid, hfrontSplit, hrest⟩
  · cases mid with
    | nil =>
        rw [hpre]
        simp [hxs.1, parenWeight]
    | cons a as =>
        cases as with
        | nil =>
            have ha : a = .rp := by simpa using (congrArg List.head? hone).symm
            subst a
            have hpre' : pre = (.lp :: xs) ++ [.rp] := by simpa using hpre
            rw [hpre']
            simp [hxs.1, parenWeight]
        | cons z zs => simp at hone
  · exact hfront pre mid hfrontSplit

private theorem balanced_wrap {xs : List Sym} (hxs : Balanced xs) :
    Balanced (.lp :: xs ++ [.rp]) := by
  refine ⟨?_, prefixNonneg_wrap hxs⟩
  simp [hxs.1, parenWeight]

private def FlatListBalanced (ps : List BP) : Prop :=
  Balanced (flatBPTail ps) ∧ Balanced (flatBPSeq ps)

private theorem flat_balanced (t : BT) : Balanced (flatBT t) := by
  exact BT.rec
    (motive_1 := fun t => Balanced (flatBT t))
    (motive_2 := fun p => Balanced (flatBP p))
    (motive_3 := FlatListBalanced)
    (fun ps hps => by
      cases ps with
      | nil => simpa [flatBT] using balanced_singleton_zero .zero rfl
      | cons p ps =>
          cases ps with
          | nil => simpa [flatBT, flatBPSeq, flatBPTail] using hps.2
          | cons q qs => simpa [flatBT, flatBPSeq] using balanced_wrap hps.2)
    (fun u a ha => by
      simpa [flatBP] using balanced_cons_zero (.dsym u) (flatBT a) rfl ha)
    ⟨balanced_nil, balanced_nil⟩
    (fun p ps hp hps => by
      have hcm := balanced_singleton_zero .cm rfl
      refine ⟨?_, ?_⟩
      · simpa [flatBPTail, List.append_assoc] using
          balanced_append hcm (balanced_append hp hps.1)
      · simpa [flatBPSeq] using balanced_append hp hps.1)
    t

private theorem flatBP_balanced (p : BP) : Balanced (flatBP p) := by
  rcases p with ⟨u, a⟩
  simpa [flatBP] using balanced_cons_zero (.dsym u) (flatBT a) rfl (flat_balanced a)

private theorem flatBPTail_balanced (ps : List BP) : Balanced (flatBPTail ps) := by
  induction ps with
  | nil => exact balanced_nil
  | cons p ps ih =>
      have hcm := balanced_singleton_zero .cm rfl
      simpa [flatBPTail, List.append_assoc] using
        balanced_append hcm (balanced_append (flatBP_balanced p) ih)

private theorem flatBPSeq_balanced (ps : List BP) : Balanced (flatBPSeq ps) := by
  cases ps with
  | nil => exact balanced_nil
  | cons p ps =>
      simpa [flatBPSeq] using balanced_append (flatBP_balanced p) (flatBPTail_balanced ps)

private theorem flatBP_nonempty (p : BP) : flatBP p ≠ [] := by
  rcases p with ⟨u, a⟩
  simp [flatBP]

/-- In a multi-term, a complete principal occurrence cannot consume the
outer closing parenthesis. -/
private theorem multi_occurrence_body {body s b : List Sym} {pr : BP}
    (hbody : Balanced body)
    (h : .lp :: body ++ [.rp] = s ++ flatBP pr ++ b) :
    ∃ s' b',
      s = .lp :: s' ∧ b = b' ++ [.rp] ∧
        body = s' ++ flatBP pr ++ b' := by
  cases s with
  | nil =>
      rcases pr with ⟨u, a⟩
      simp [flatBP] at h
  | cons x s' =>
      have hx : x = .lp := by
        simpa using (congrArg List.head? h).symm
      subst x
      have htail : body ++ [.rp] = s' ++ flatBP pr ++ b := by
        simpa using h
      have hbne : b ≠ [] := by
        intro hb
        subst b
        have hsplit : body ++ [.rp] = s' ++ (flatBP pr ++ []) := by
          simpa [List.append_assoc] using htail
        rcases List.append_eq_append_iff.mp hsplit with
            ⟨mid, hs', hone⟩ | ⟨mid, hbodySplit, hpr⟩
        · rcases pr with ⟨u, a⟩
          cases mid <;> simp [flatBP] at hone
        · have hsnonneg : 0 ≤ parenSum s' :=
            hbody.2 s' mid hbodySplit
          have hsum := congrArg parenSum htail
          simp [hbody.1, (flatBP_balanced pr).1, parenWeight] at hsum
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
          body ++ [.rp] = (s' ++ flatBP pr ++ b') ++ [.rp] := by
        rw [← hbRP] at htail
        simpa [List.append_assoc] using htail
      have hbodyEq : body = s' ++ flatBP pr ++ b' :=
        List.append_cancel_right hsnoc
      exact ⟨s', b', rfl, hbRP.symm, hbodyEq⟩

private def SurgBT (t : BT) : Prop :=
  ∀ pr pr' s b,
    flatBT t = s ++ flatBP pr ++ b →
    dfree_BT t = true → dfree_BP pr' = true →
    ∃ t', flatBT t' = s ++ flatBP pr' ++ b ∧ dfree_BT t' = true

private def SurgBP (p : BP) : Prop :=
  ∀ pr pr' s b,
    flatBP p = s ++ flatBP pr ++ b →
    dfree_BP p = true → dfree_BP pr' = true →
    ∃ p', flatBP p' = s ++ flatBP pr' ++ b ∧ dfree_BP p' = true

private def SurgList (ps : List BP) : Prop :=
  ∀ pr pr' s b,
    flatBPSeq ps = s ++ flatBP pr ++ b →
    dfree_BPList ps = true → dfree_BP pr' = true →
    ∃ ps', flatBPSeq ps' = s ++ flatBP pr' ++ b ∧
      dfree_BPList ps' = true ∧ ps'.length = ps.length

/-- Generalized principal replacement surgery. -/
private theorem generalized_surgery_BT (t : BT) : SurgBT t := by
  exact BT.rec
    (motive_1 := SurgBT)
    (motive_2 := SurgBP)
    (motive_3 := SurgList)
    (fun ps ih pr pr' s b hflat hdf hpr' => by
      cases ps with
      | nil =>
          rcases pr with ⟨u, a⟩
          cases s <;> simp [flatBT, flatBP] at hflat
      | cons p ps =>
          cases ps with
          | nil =>
              have hseq : flatBPSeq [p] = s ++ flatBP pr ++ b := by
                simpa [flatBPSeq, flatBPTail] using hflat
              have hdfList : dfree_BPList [p] = true := by
                simpa [dfree_BT] using hdf
              rcases ih pr pr' s b hseq hdfList hpr' with
                ⟨ps', hps'flat, hps'df, hps'len⟩
              cases ps' with
              | nil => simp at hps'len
              | cons p' rest =>
                  cases rest with
                  | nil =>
                      refine ⟨.trm [p'], ?_, ?_⟩
                      · simpa [flatBT, flatBPSeq, flatBPTail] using hps'flat
                      · simpa [dfree_BT] using hps'df
                  | cons q' qs' => simp at hps'len
          | cons q qs =>
              have hbodyBal : Balanced (flatBPSeq (p :: q :: qs)) :=
                flatBPSeq_balanced (p :: q :: qs)
              have hmulti :
                  .lp :: flatBPSeq (p :: q :: qs) ++ [.rp] =
                    s ++ flatBP pr ++ b := by
                simpa [flatBT, flatBPSeq] using hflat
              rcases multi_occurrence_body hbodyBal hmulti with
                ⟨s', b', rfl, rfl, hbody⟩
              have hdfList : dfree_BPList (p :: q :: qs) = true := by
                simpa [dfree_BT] using hdf
              rcases ih pr pr' s' b' hbody hdfList hpr' with
                ⟨ps', hps'flat, hps'df, hps'len⟩
              cases ps' with
              | nil => simp at hps'len
              | cons p' rest =>
                  cases rest with
                  | nil => simp at hps'len
                  | cons q' qs' =>
                      refine ⟨.trm (p' :: q' :: qs'), ?_, ?_⟩
                      · change
                          .lp :: (flatBP p' ++ flatBPTail (q' :: qs')) ++ [.rp] =
                            (.lp :: s') ++ flatBP pr' ++ (b' ++ [.rp])
                        have hpsExplicit :
                            flatBP p' ++ flatBPTail (q' :: qs') =
                              s' ++ flatBP pr' ++ b' := by
                          simpa [flatBPSeq] using hps'flat
                        rw [hpsExplicit]
                        simp [List.append_assoc]
                      · simpa [dfree_BT] using hps'df)
    (fun u a ih pr pr' s b hflat hdf hpr' => by
      cases s with
      | nil =>
          have hcancel : flatBP (.db u a) ++ [] = flatBP pr ++ b := by
            simpa [flatBP] using hflat
          rcases flatBP_cancel hcancel with ⟨_, hb⟩
          subst b
          exact ⟨pr', by simp, hpr'⟩
      | cons x s' =>
          have hx : x = .dsym u := by
            simpa [flatBP] using (congrArg List.head? hflat).symm
          subst x
          have hchild : flatBT a = s' ++ flatBP pr ++ b := by
            simpa [flatBP] using hflat
          have hdfa : dfree_BT a = true := by
            simp [dfree_BP] at hdf
            exact hdf.2
          rcases ih pr pr' s' b hchild hdfa hpr' with ⟨a', ha'flat, ha'df⟩
          refine ⟨.db u a', ?_, ?_⟩
          · simpa [flatBP] using congrArg (fun xs => .dsym u :: xs) ha'flat
          · simp [dfree_BP] at hdf ⊢
            exact ⟨hdf.1, ha'df⟩)
    (by
      intro pr pr' s b hflat
      rcases pr with ⟨u, a⟩
      simp [flatBPSeq, flatBP] at hflat)
    (fun p ps ihp ihps pr pr' s b hflat hdf hpr' => by
      have hseq : flatBP p ++ flatBPTail ps = s ++ flatBP pr ++ b := by
        simpa [flatBPSeq] using hflat
      rcases flatBP_localize_append hseq with
          ⟨inside, hpflat, rfl⟩ | ⟨after, rfl, htail⟩
      · have hdfSplit : dfree_BP p = true ∧ dfree_BPList ps = true := by
          simpa [dfree_BPList] using hdf
        have hdfp : dfree_BP p = true := hdfSplit.1
        rcases ihp pr pr' s inside hpflat hdfp hpr' with
          ⟨p', hp'flat, hp'df⟩
        refine ⟨p' :: ps, ?_, ?_, by simp⟩
        · simp [flatBPSeq, hp'flat, List.append_assoc]
        · simp [dfree_BPList, hp'df, hdfSplit.2]
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
                have hrest : flatBPSeq (q :: qs) =
                    after' ++ flatBP pr ++ b := by
                  simpa [flatBPTail, flatBPSeq] using htail
                have hdftail : dfree_BPList (q :: qs) = true := by
                  have hdfSplit :
                      dfree_BP p = true ∧ dfree_BPList (q :: qs) = true := by
                    simpa [dfree_BPList] using hdf
                  exact hdfSplit.2
                rcases ihps pr pr' after' b hrest hdftail hpr' with
                  ⟨ps', hps'flat, hps'df, hps'len⟩
                have hps'ne : ps' ≠ [] := by
                  intro hz
                  subst ps'
                  simp at hps'len
                have htail' : flatBPTail ps' = .cm :: flatBPSeq ps' := by
                  cases ps' with
                  | nil => exact (hps'ne rfl).elim
                  | cons q' qs' => simp [flatBPTail, flatBPSeq]
                refine ⟨p :: ps', ?_, ?_, ?_⟩
                · change
                    flatBP p ++ flatBPTail ps' =
                      (flatBP p ++ (.cm :: after')) ++ flatBP pr' ++ b
                  rw [htail', hps'flat]
                  simp [List.append_assoc]
                · simp [dfree_BPList] at hdf ⊢
                  exact ⟨hdf.1, hps'df⟩
                · simp [hps'len])
    t

/-- Replacing any complete principal-code occurrence in a `D_ω`-free term by
another `D_ω`-free principal code again yields a `D_ω`-free term. -/
theorem principal_replacement_image {t : BT} {pr pr' : BP}
    {s b : List Sym} (ht : t ∈ T_B) (hpr' : dfree_BP pr' = true)
    (hflat : flatBT t = s ++ flatBP pr ++ b) :
    ∃ t', t' ∈ T_B ∧ flatBT t' = s ++ flatBP pr' ++ b := by
  have hdft : dfree_BT t = true := ht
  rcases generalized_surgery_BT t pr pr' s b hflat hdft hpr' with
    ⟨t', ht'flat, ht'df⟩
  exact ⟨t', ht'df, ht'flat⟩

private theorem flatBT_nonempty (t : BT) : flatBT t ≠ [] := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => simp [flatBT]
  | cons p ps =>
      cases ps with
      | nil => rcases p with ⟨u, a⟩; simp [flatBT, flatBP]
      | cons q qs => simp [flatBT]

private theorem principal_of_isPTB_flat {c : BT}
    (h : isPTB_str (flatBT c)) :
    ∃ p, c = .trm [p] ∧ dfree_BP p = true := by
  rcases h with ⟨p, hp, hflat⟩
  refine ⟨p, ?_, hp⟩
  apply flatBT_injective
  simpa [flatBT] using hflat

private theorem scb_decomp_of_image {t : BT} {s c b : List Sym}
    (hflat : flatBT t = s ++ c ++ b)
    (hrp : ∀ x ∈ b, x = .rp)
    (hside : isPTB_str c ∨ s ++ c ++ b = [.zero]) :
    scb_decomp t s c b := by
  refine ⟨hflat, ?_, hrp⟩
  intro ht
  rcases hside with hp | hz
  · exact hp
  · exfalso
    apply ht
    apply flatBT_injective
    rw [hflat, hz]
    rfl

/-- Corrected A12 form.  The replacement string must itself be principal,
unless the whole replacement result is the zero string. -/
theorem scb_replaceable_corrected (c₀ c₁ t₀ : BT) (s b : List Sym)
    (_hc₀ : c₀ ∈ T_B) (hc₁ : c₁ ∈ T_B) (ht₀ : t₀ ∈ T_B)
    (hd : scb_decomp t₀ s (flatBT c₀) b)
    (hside : isPTB_str (flatBT c₁) ∨
      s ++ flatBT c₁ ++ b = [.zero]) :
    ∃ t₁, t₁ ∈ T_B ∧ flatBT t₁ = s ++ flatBT c₁ ++ b ∧
      scb_decomp t₁ s (flatBT c₁) b := by
  have hrp := hd.2.2
  have image : ∃ t₁, t₁ ∈ T_B ∧ flatBT t₁ = s ++ flatBT c₁ ++ b := by
    by_cases hz : t₀ = BZero
    · subst t₀
      have hlen := congrArg List.length hd.1
      have hcpos : 0 < (flatBT c₀).length := by
        cases hfc : flatBT c₀ with
        | nil => exact (flatBT_nonempty c₀ hfc).elim
        | cons x xs => simp
      simp [BZero, flatBT] at hlen
      have hslen : s.length = 0 := by omega
      have hblen : b.length = 0 := by omega
      have hs : s = [] := by
        cases s with
        | nil => rfl
        | cons x xs => simp at hslen
      have hb : b = [] := by
        cases b with
        | nil => rfl
        | cons x xs => simp at hblen
      exact ⟨c₁, hc₁, by simp [hs, hb]⟩
    · have hc₀ptb : isPTB_str (flatBT c₀) := hd.2.1 hz
      rcases principal_of_isPTB_flat hc₀ptb with ⟨p₀, hc₀eq, _⟩
      rcases hside with hc₁ptb | hzero
      · rcases principal_of_isPTB_flat hc₁ptb with ⟨p₁, hc₁eq, hp₁⟩
        have hocc : flatBT t₀ = s ++ flatBP p₀ ++ b := by
          simpa [hc₀eq, flatBT] using hd.1
        rcases principal_replacement_image ht₀ hp₁ hocc with
          ⟨t₁, ht₁, ht₁flat⟩
        exact ⟨t₁, ht₁, by simpa [hc₁eq, flatBT] using ht₁flat⟩
      · exact ⟨BZero, by simp [T_B, BZero, dfree_BT, dfree_BPList],
          by simpa [BZero, flatBT] using hzero.symm⟩
  rcases image with ⟨t₁, ht₁, ht₁flat⟩
  exact ⟨t₁, ht₁, ht₁flat,
    scb_decomp_of_image ht₁flat hrp hside⟩

private theorem explicit_multi_not_isPTB :
    ¬isPTB_str
      (flatBT (.trm [.db 0 BZero, .db 1 BZero])) := by
  rintro ⟨p, _, hp⟩
  rcases p with ⟨u, a⟩
  simp [BZero, flatBT, flatBP, flatBPTail] at hp

/-- The literal statement is false at the zero host: its left disjunct places
no restriction on the multi-term replacement. -/
theorem scb_replaceable_original_false :
    let c₀ : BT := BZero
    let c₁ : BT := .trm [.db 0 BZero, .db 1 BZero]
    let t₀ : BT := BZero
    c₀ ∈ T_B ∧ c₁ ∈ T_B ∧
      (¬(∃ p, c₀ = .trm [p]) ∨ ∃ p, c₁ = .trm [p]) ∧
      t₀ ∈ T_B ∧ flatBT t₀ = [] ++ flatBT c₀ ++ [] ∧
      scb_decomp t₀ [] (flatBT c₀) [] ∧
      ¬∃ t₁, t₁ ∈ T_B ∧ flatBT t₁ = [] ++ flatBT c₁ ++ [] ∧
        scb_decomp t₁ [] (flatBT c₁) [] := by
  dsimp
  refine ⟨by simp [T_B, BZero, dfree_BT, dfree_BPList],
    by simp [T_B, BZero, dfree_BT, dfree_BP, dfree_BPList],
    Or.inl (by simp [BZero]),
    by simp [T_B, BZero, dfree_BT, dfree_BPList], by simp, ?_, ?_⟩
  · simp [scb_decomp, BZero, flatBT]
  · rintro ⟨t₁, _, ht₁flat, ht₁scb⟩
    have ht₁eq : t₁ = .trm [.db 0 BZero, .db 1 BZero] :=
      flatBT_injective (by simpa using ht₁flat)
    have ht₁ne : t₁ ≠ BZero := by simp [ht₁eq, BZero]
    exact explicit_multi_not_isPTB (ht₁scb.2.1 ht₁ne)

#print axioms principal_replacement_image
#print axioms scb_replaceable_corrected
#print axioms scb_replaceable_original_false


end PSS
