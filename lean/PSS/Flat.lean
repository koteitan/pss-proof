import PSS.Scb

/-!
# PSS.Flat — `flatBT` の一意可読性

`flatBT` / `flatBP` の文字列は prefix-free な符号である。Isabelle の
`flatinj_*` 群と `m_7_flatBT_inj` に対応する。
-/

namespace PSS

private def flatWeight : Sym → ℤ
  | .lp => 1
  | .cm => 1
  | .rp => -1
  | .zero => -1
  | .dsym _ => 0

private def flatSum (xs : List Sym) : ℤ :=
  (xs.map flatWeight).sum

@[simp] private theorem flatSum_nil : flatSum [] = 0 := rfl

@[simp] private theorem flatSum_cons (x : Sym) (xs : List Sym) :
    flatSum (x :: xs) = flatWeight x + flatSum xs := by
  simp [flatSum]

@[simp] private theorem flatSum_append (xs ys : List Sym) :
    flatSum (xs ++ ys) = flatSum xs + flatSum ys := by
  simp [flatSum]

private def ProperNonneg (xs : List Sym) : Prop :=
  ∀ pre rest, xs = pre ++ rest → rest ≠ [] → 0 ≤ flatSum pre

private def PrefixNonneg (xs : List Sym) : Prop :=
  ∀ pre rest, xs = pre ++ rest → 0 ≤ flatSum pre

private def FlatGood (xs : List Sym) : Prop :=
  flatSum xs = -1 ∧ ProperNonneg xs

private def FlatNeutral (xs : List Sym) : Prop :=
  flatSum xs = 0 ∧ PrefixNonneg xs

private theorem prefixNonneg_nil : PrefixNonneg [] := by
  intro pre rest h
  simp at h
  simp [h.1]

private theorem prefixNonneg_append {xs ys : List Sym}
    (hxs : PrefixNonneg xs) (hsum : flatSum xs = 0)
    (hys : PrefixNonneg ys) :
    PrefixNonneg (xs ++ ys) := by
  intro pre rest h
  rcases List.append_eq_append_iff.mp h with ⟨mid, hpre, hysplit⟩ | ⟨mid, hxsplit, hrest⟩
  · rw [hpre, flatSum_append, hsum, zero_add]
    exact hys mid rest hysplit
  · exact hxs pre mid hxsplit

private theorem prefixNonneg_cons_good (x : Sym) (xs : List Sym)
    (hx : flatWeight x = 1) (hxs : FlatGood xs) :
    PrefixNonneg (x :: xs) := by
  intro pre rest h
  cases pre with
  | nil => simp
  | cons y pre =>
      have hy : y = x := by simpa using (congrArg List.head? h).symm
      subst y
      have htail : xs = pre ++ rest := by simpa using h
      by_cases hr : rest = []
      · subst rest
        have hp : pre = xs := by simpa using htail.symm
        simp [hp, hx, hxs.1]
      · have := hxs.2 pre rest htail hr
        simp [hx]
        omega

private theorem neutral_cons_good (x : Sym) (xs : List Sym)
    (hx : flatWeight x = 1) (hxs : FlatGood xs) :
    FlatNeutral (x :: xs) := by
  refine ⟨?_, prefixNonneg_cons_good x xs hx hxs⟩
  simp [hx, hxs.1]

private theorem good_cons_zero (x : Sym) (xs : List Sym)
    (hx : flatWeight x = 0) (hxs : FlatGood xs) :
    FlatGood (x :: xs) := by
  refine ⟨by simp [hx, hxs.1], ?_⟩
  intro pre rest h hr
  cases pre with
  | nil => simp
  | cons y pre =>
      have hy : y = x := by simpa using (congrArg List.head? h).symm
      subst y
      have htail : xs = pre ++ rest := by simpa using h
      simpa [hx] using hxs.2 pre rest htail hr

private theorem good_append_rp {xs : List Sym} (hxs : FlatNeutral xs) :
    FlatGood (xs ++ [.rp]) := by
  refine ⟨by simp [hxs.1, flatWeight], ?_⟩
  intro pre rest h hr
  rcases List.append_eq_append_iff.mp h with ⟨mid, hpre, hone⟩ | ⟨mid, hx, hrest⟩
  · cases mid with
    | nil =>
        simpa [hpre] using hxs.2 xs [] (by simp)
    | cons a as =>
        cases as <;> simp_all
  · exact hxs.2 pre mid hx

private def AllFlatGood : List BP → Prop
  | [] => True
  | p :: ps => FlatGood (flatBP p) ∧ AllFlatGood ps

private theorem flatBPTail_neutral (ps : List BP) (hps : AllFlatGood ps) :
    FlatNeutral (flatBPTail ps) := by
  induction ps with
  | nil => exact ⟨rfl, prefixNonneg_nil⟩
  | cons p ps ih =>
      rcases hps with ⟨hp, hps⟩
      have hseg : FlatNeutral (.cm :: flatBP p) :=
        neutral_cons_good .cm (flatBP p) (by rfl) hp
      have htail := ih hps
      refine ⟨?_, ?_⟩
      · change flatSum ((.cm :: flatBP p) ++ flatBPTail ps) = 0
        rw [flatSum_append, hseg.1, htail.1]
        rfl
      · simpa [flatBPTail, List.append_assoc] using
          prefixNonneg_append hseg.2 hseg.1 htail.2

private theorem flatBT_good (t : BT) : FlatGood (flatBT t) := by
  exact BT.rec
    (motive_1 := fun t => FlatGood (flatBT t))
    (motive_2 := fun p => FlatGood (flatBP p))
    (motive_3 := AllFlatGood)
    (fun ps hps => by
      cases ps with
      | nil =>
          refine ⟨by simp [flatBT, flatSum, flatWeight], ?_⟩
          intro pre rest h hr
          cases pre <;> simp_all [flatBT, flatSum]
      | cons p ps =>
          rcases hps with ⟨hp, hps⟩
          cases ps with
          | nil => simpa [flatBT] using hp
          | cons q qs =>
              have htail : FlatNeutral (flatBPTail (q :: qs)) :=
                flatBPTail_neutral (q :: qs) hps
              have hhead : FlatNeutral (.lp :: flatBP p) :=
                neutral_cons_good .lp (flatBP p) (by rfl) hp
              have hinner : FlatNeutral ((.lp :: flatBP p) ++ flatBPTail (q :: qs)) :=
                ⟨by rw [flatSum_append, hhead.1, htail.1]; rfl,
                  prefixNonneg_append hhead.2 hhead.1 htail.2⟩
              simpa [flatBT, List.append_assoc] using good_append_rp hinner)
    (fun u a ha => good_cons_zero (.dsym u) (flatBT a) (by rfl) ha)
    trivial
    (fun _ _ hp hps => ⟨hp, hps⟩)
    t

private theorem flatBP_good (p : BP) : FlatGood (flatBP p) :=
  match p with
  | .db u a => good_cons_zero (.dsym u) (flatBT a) (by rfl) (flatBT_good a)

/-- `flatBP` は prefix-free。先頭の principal 文字列と残りを同時に消去できる。 -/
theorem flatBP_cancel {p q : BP} {xs ys : List Sym}
    (h : flatBP p ++ xs = flatBP q ++ ys) :
    flatBP p = flatBP q ∧ xs = ys := by
  rcases List.append_eq_append_iff.mp h with ⟨mid, hq, hxs⟩ | ⟨mid, hp, hys⟩
  · have hmid : mid = [] := by
      by_contra hm
      have hnonneg := (flatBP_good q).2 (flatBP p) mid hq hm
      have hminus := (flatBP_good p).1
      omega
    subst mid
    simpa using And.intro hq.symm hxs
  · have hmid : mid = [] := by
      by_contra hm
      have hnonneg := (flatBP_good p).2 (flatBP q) mid hp hm
      have hminus := (flatBP_good q).1
      omega
    subst mid
    simpa using And.intro hp hys.symm

private def AllBPInjective : List BP → Prop
  | [] => True
  | p :: ps => (∀ q, flatBP p = flatBP q → p = q) ∧ AllBPInjective ps

private theorem flatBPTail_injective_of (ps : List BP) (hps : AllBPInjective ps) :
    ∀ qs, flatBPTail ps = flatBPTail qs → ps = qs := by
  induction ps with
  | nil =>
      intro qs h
      cases qs <;> simp_all [flatBPTail, flatBP]
  | cons p ps ih =>
      intro qs h
      rcases hps with ⟨hp, hps⟩
      cases qs with
      | nil => simp [flatBPTail, flatBP] at h
      | cons q qs =>
          have h' : flatBP p ++ flatBPTail ps = flatBP q ++ flatBPTail qs := by
            simpa [flatBPTail] using h
          rcases flatBP_cancel h' with ⟨hpq, htail⟩
          have epq : p = q := hp q hpq
          have eps : ps = qs := ih hps qs htail
          simp [epq, eps]

private theorem flatBT_injective_aux (t : BT) :
    ∀ c, flatBT t = flatBT c → t = c := by
  exact BT.rec
    (motive_1 := fun t => ∀ c, flatBT t = flatBT c → t = c)
    (motive_2 := fun p => ∀ q, flatBP p = flatBP q → p = q)
    (motive_3 := AllBPInjective)
    (fun ps hps c h => by
      rcases c with ⟨cs⟩
      cases ps with
      | nil =>
          cases cs with
          | nil => rfl
          | cons r rs =>
              cases r with
              | db v b => cases rs <;> simp [flatBT, flatBP] at h
      | cons p tail =>
          rcases hps with ⟨hp, htailInj⟩
          cases tail with
          | nil =>
              cases cs with
              | nil =>
                  cases p with
                  | db u a => simp [flatBT, flatBP] at h
              | cons r rs =>
                  cases rs with
                  | nil =>
                      have epr : p = r := hp r (by simpa [flatBT] using h)
                      simp [epr]
                  | cons z zs =>
                      cases p with
                      | db u a => simp [flatBT, flatBP] at h
          | cons q qs =>
              cases cs with
              | nil => simp [flatBT] at h
              | cons r rs =>
                  cases rs with
                  | nil =>
                      cases r with
                      | db v b => simp [flatBT, flatBP] at h
                  | cons z zs =>
                      have hwithRP :
                          (flatBP p ++ flatBPTail (q :: qs)) ++ [.rp] =
                            (flatBP r ++ flatBPTail (z :: zs)) ++ [.rp] := by
                        simpa [flatBT] using congrArg List.tail h
                      have hinner : flatBP p ++ flatBPTail (q :: qs) =
                          flatBP r ++ flatBPTail (z :: zs) :=
                        List.append_cancel_right hwithRP
                      rcases flatBP_cancel hinner with ⟨hpr, htail⟩
                      have epr : p = r := hp r hpr
                      have etail : q :: qs = z :: zs :=
                        flatBPTail_injective_of (q :: qs) htailInj (z :: zs) htail
                      simp [epr, etail])
    (fun u a ih q h => by
      rcases q with ⟨v, b⟩
      have huv : u = v := by simpa [flatBP] using congrArg List.head? h
      subst v
      have hab : flatBT a = flatBT b := by simpa [flatBP] using h
      simp [ih b hab])
    trivial
    (fun _ _ hp hps => ⟨hp, hps⟩)
    t

/-- `flatBT` は単射。 -/
theorem flatBT_injective {t c : BT} (h : flatBT t = flatBT c) : t = c :=
  flatBT_injective_aux t c h

/-- 完全な項文字列の後ろに別の文字列を付けても完全な項文字列になるなら、
その余分な接尾辞は空。 -/
theorem flatBT_append_suffix_nil {t c : BT} {b : List Sym}
    (h : flatBT t = flatBT c ++ b) : b = [] := by
  by_contra hb
  have hnonneg := (flatBT_good t).2 (flatBT c) b h hb
  have hminus := (flatBT_good c).1
  omega

#print axioms flatBP_cancel
#print axioms flatBT_injective
#print axioms flatBT_append_suffix_nil

end PSS
