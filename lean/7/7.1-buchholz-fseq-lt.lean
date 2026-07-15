import «7».«7.1-lessBT-linear-order»

/-!
# §7.1 [Buc1] Lemma 3.2(a): fundamental sequences descend

The source paper cites Buchholz's lemma.  This file proves the executable
`operB` implementation strictly decreases every nonzero `OT_B` term.  The
induction is strengthened from numeral arguments to
`z ∈ domB a ∪ NatSet`, exactly as in the completed Isabelle development.
-/

namespace PSS

private theorem leBT_trans_bf (a b c : BT)
    (hab : leBT a b = true) (hbc : leBT b c = true) :
    leBT a c = true := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq] at hab hbc ⊢
  rcases hab with hab | rfl
  · rcases hbc with hbc | rfl
    · exact Or.inl (lessBT_linear_trans a b c hab hbc)
    · exact Or.inl hab
  · exact hbc

private theorem domTagList_snoc_bf (ps : List BP) (p : BP) :
    domTagList (ps ++ [p]) = domTagBP p := by
  induction ps with
  | nil => simp [domTagList]
  | cons q qs ih =>
      cases qs with
      | nil => simp [domTagList]
      | cons r rs => simpa [domTagList] using ih

@[simp] private theorem zero_addBT_bf (t : BT) : addBT BZero t = t := by
  rcases t with ⟨ps⟩
  rfl

private theorem addBT_assoc_bf (a b c : BT) :
    addBT (addBT a b) c = addBT a (addBT b c) := by
  rcases a with ⟨as⟩
  rcases b with ⟨bs⟩
  rcases c with ⟨cs⟩
  simp [addBT, List.append_assoc]

private theorem bOperCore_list_snoc_bf (ps : List BP) (p : BP) (z : BT) :
    bOperCore (.list (ps ++ [p]) z) =
      addBT (.trm ps) (bOperCore (.princ p z)) := by
  induction ps with
  | nil =>
      rw [bOperCore.eq_def]
      change bOperCore (.princ p z) = addBT BZero (bOperCore (.princ p z))
      exact (zero_addBT_bf _).symm
  | cons q qs ih =>
      cases qs with
      | nil => simp [bOperCore, addBT]
      | cons r rs =>
          rw [bOperCore.eq_def]
          change addBT (.trm [q])
              (bOperCore (.list ((r :: rs) ++ [p]) z)) =
            addBT (.trm (q :: r :: rs)) (bOperCore (.princ p z))
          rw [ih, ← addBT_assoc_bf]
          rfl

private theorem operB_single_bf (p : BP) (z : BT) :
    operB (.trm [p]) z = bOperCore (.princ p z) := by
  simp [operB, bOperCore]

private theorem operB_snoc_bf (ps : List BP) (p : BP) (z : BT) :
    operB (.trm (ps ++ [p])) z =
      addBT (.trm ps) (operB (.trm [p]) z) := by
  rw [operB, bOperCore.eq_def]
  change bOperCore (.list (ps ++ [p]) z) =
    addBT (.trm ps) (operB (.trm [p]) z)
  rw [bOperCore_list_snoc_bf, operB_single_bf]

theorem domTag_snoc_bf (ps : List BP) (p : BP) :
    domTag (.trm (ps ++ [p])) = domTagBP p := by
  simp [domTag, domTagList_snoc_bf]

theorem addBT_lt_right_bf (pre x y : BT)
    (hxy : lessBT x y = true) :
    lessBT (addBT pre x) (addBT pre y) = true := by
  rcases pre with ⟨ps⟩
  rcases x with ⟨xs⟩
  rcases y with ⟨ys⟩
  induction ps with
  | nil => simpa [addBT] using hxy
  | cons p ps ih =>
      change lessBPList (p :: (ps ++ xs)) (p :: (ps ++ ys)) = true
      simp only [lessBPList, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      exact Or.inr ⟨trivial, ih⟩

private theorem lessBP_single_bf (p q : BP) :
    lessBT (.trm [p]) (.trm [q]) = lessBP p q := by
  simp [lessBT, lessBPList]

theorem leBT_single_index_bf (h₁ h₂ : ℕ∞) (c₁ c₂ : BT)
    (h : leBT (Dprin h₁ c₁) (Dprin h₂ c₂) = true) : h₁ ≤ h₂ := by
  have hh :
      ((h₁ < h₂ ∨ h₁ = h₂ ∧ lessBT c₁ c₂ = true) ∨
        (h₁ = h₂ ∧ c₁ = c₂)) := by
    simpa [leBT, Dprin, lessBT, lessBPList, lessBP] using h
  rcases hh with (hlt | ⟨heq, _⟩) | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le
  · exact heq.le

private theorem BZero_mem_TBv_bf (v : ℕ∞) : BZero ∈ TBv v := by
  simp [BZero, TBv]

private theorem NatSet_mem_TBv_bf {z : BT} {w : ℕ}
    (hz : z ∈ NatSet) : z ∈ TBv (w : ℕ∞) := by
  rcases hz with ⟨n, rfl⟩
  simp [numBT, TBv, BZero]

private theorem Dprin_mem_TBv_bf (w : ℕ) (t : BT) :
    Dprin (w : ℕ∞) t ∈ TBv (w : ℕ∞) := by
  simp [Dprin, TBv]

theorem TBv_lt_head_bf {z c : BT} {w : ℕ} {h : ℕ∞} {rest : List BP}
    (hz : z ∈ TBv (w : ℕ∞)) (hwh : (w : ℕ∞) < h) :
    lessBT z (.trm (.db h c :: rest)) = true := by
  rcases z with ⟨zs⟩
  cases zs with
  | nil => simp [lessBT, lessBPList]
  | cons zp zr =>
      rcases zp with ⟨u, bz⟩
      have huw : u ≤ (w : ℕ∞) := by
        have hmem : u ≤ (w : ℕ∞) ∧
            ∀ p ∈ zr, (match p with | .db k _ => decide (k ≤ (w : ℕ∞))) = true := by
          simpa [TBv] using hz
        exact hmem.1
      have huh : u < h := huw.trans_lt hwh
      change lessBPList (.db u bz :: zr) (.db h c :: rest) = true
      simp only [lessBPList, Bool.or_eq_true]
      left
      simp [lessBP, huh]

private theorem multBT_single_bf (q : BP) (n : ℕ) :
    multBT (.trm [q]) n = .trm (List.replicate n q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [multBT, ih]
      simp [addBT, List.replicate_succ']

private theorem lessBT_replicate_snoc_bf (p q : BP) (n : ℕ)
    (hqp : lessBP q p = true) :
    lessBT (.trm (List.replicate n q ++ [q])) (.trm [p]) = true := by
  cases n with
  | zero => simpa [lessBT, lessBPList] using hqp
  | succ n =>
      change lessBPList (q :: (List.replicate n q ++ [q])) [p] = true
      simp [lessBPList, hqp]

private theorem leBT_replicate_snoc_head_bf (q : BP) (n : ℕ) :
    leBT (.trm [q]) (.trm (List.replicate n q ++ [q])) = true := by
  cases n with
  | zero => simp [leBT]
  | succ n =>
      rw [List.replicate_succ]
      change leBT (.trm [q]) (.trm (q :: (List.replicate n q ++ [q]))) = true
      simp only [leBT, Bool.or_eq_true]
      left
      change lessBPList [q] (q :: (List.replicate n q ++ [q])) = true
      simp only [lessBPList, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      right
      refine ⟨trivial, ?_⟩
      generalize List.replicate n q = qs
      cases qs <;> rfl

theorem descP_last_head_bf (p : BP) (ps : List BP)
    (hdesc : descP (p :: ps) = true) :
    leBT (.trm [(p :: ps).getLast (by simp)]) (.trm [p]) = true := by
  induction ps generalizing p with
  | nil => simp [leBT]
  | cons q qs ih =>
      have hh : leBT (.trm [q]) (.trm [p]) = true ∧
          descP (q :: qs) = true := by
        simpa [descP] using hdesc
      have hpq : leBT (.trm [q]) (.trm [p]) = true := by
        exact hh.1
      have htail : descP (q :: qs) = true := by
        exact hh.2
      have hlastq := ih q htail
      have hlast : (p :: q :: qs).getLast (by simp) =
          (q :: qs).getLast (by simp) := by simp
      rw [hlast]
      exact leBT_trans_bf _ _ _ hlastq hpq

private theorem isOT_BPList_mem_bf (ps : List BP)
    (hot : isOT_BPList ps = true) {p : BP} (hp : p ∈ ps) :
    isOT_BP p = true := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      have hsplit : isOT_BP q = true ∧ isOT_BPList qs = true := by
        simpa [isOT_BPList] using hot
      simp only [List.mem_cons] at hp
      rcases hp with hp | hp
      · subst p
        exact hsplit.1
      · exact ih hsplit.2 hp

theorem domTagBP_below_head_bf {h : ℕ∞} {c : BT} {w : ℕ}
    (htag : domTagBP (.db h c) = .below w) : (w : ℕ∞) < h := by
  by_cases hc : c = BZero
  · subst c
    by_cases h0 : h = 0
    · simp [domTagBP, h0] at htag
    by_cases hinf : h = ⊤
    · simp [domTagBP, hinf] at htag
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hinf
    rw [← hk] at h0 htag ⊢
    have hk0 : k ≠ 0 := by simpa using h0
    have hkw : k - 1 = w := by
      simpa [domTagBP, BZero, hk0] using htag
    rw [← hkw]
    exact_mod_cast (Nat.sub_lt (Nat.zero_lt_of_ne_zero hk0) (by omega : 0 < 1))
  · cases hdc : domTag c with
    | empty => simp [domTagBP, hc, hdc] at htag
    | zeroOnly => simp [domTagBP, hc, hdc] at htag
    | naturals => simp [domTagBP, hc, hdc] at htag
    | below k =>
        by_cases hle : h ≤ (k : ℕ∞)
        · simp [domTagBP, hc, hdc, hle] at htag
        · have hkw : k = w := by
            simpa [domTagBP, hc, hdc, hle] using htag
          subst k
          exact lt_of_not_ge hle

theorem TBv_lt_of_OT_tag_below_bf (b z : BT) (w : ℕ)
    (hot : isOT_BT b = true) (htag : domTag b = .below w)
    (hz : z ∈ TBv (w : ℕ∞)) :
    lessBT z b = true := by
  rcases b with ⟨bs⟩
  have hne : bs ≠ [] := by
    intro hnil
    subst bs
    simp [domTag, domTagList] at htag
  cases hlast : bs.getLast hne with
  | db h c =>
  have hsplit : isOT_BPList bs = true ∧ descP bs = true := by
    simpa [isOT_BT] using hot
  have htagp : domTagBP (.db h c) = .below w := by
    rw [← domTag_snoc_bf bs.dropLast (.db h c)]
    have hdecomp : bs.dropLast ++ [.db h c] = bs := by
      rw [← hlast]
      exact List.dropLast_append_getLast hne
    rw [hdecomp]
    simpa [domTag] using htag
  have hwh : (w : ℕ∞) < h := by
    exact domTagBP_below_head_bf htagp
  rcases bs with _ | ⟨q, qs⟩
  · contradiction
  have hle : leBT (.trm [.db h c]) (.trm [q]) = true := by
    have hle0 := descP_last_head_bf q qs hsplit.2
    simpa [hlast] using hle0
  rcases q with ⟨hq, cq⟩
  have hhq : h ≤ hq := leBT_single_index_bf h hq c cq (by simpa [Dprin] using hle)
  have hwq : (w : ℕ∞) < hq := hwh.trans_le hhq
  exact TBv_lt_head_bf hz hwq

private theorem Dw_zero_lt_of_OT_tag_below_bf (b : BT) (w : ℕ)
    (hot : isOT_BT b = true) (htag : domTag b = .below w) :
    lessBT (Dprin (w : ℕ∞) BZero) b = true := by
  apply TBv_lt_of_OT_tag_below_bf b (Dprin (w : ℕ∞) BZero) w hot htag
  exact Dprin_mem_TBv_bf w BZero

private theorem bpWeight_mem_succ_le_bf (p : BP) (ps : List BP)
    (hp : p ∈ ps) : bpWeight p + 1 ≤ bpListWeight ps := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      simp only [List.mem_cons] at hp
      simp only [bpListWeight]
      rcases hp with rfl | hp
      · omega
      · have := ih hp
        omega

private theorem buchholz_descent_general_bf (a z : BT)
    (hot : isOT_BT a = true) (hne : a ≠ BZero)
    (hz : z ∈ domB a ∨ z ∈ NatSet) :
    lessBT (operB a z) a = true := by
  generalize hn : btWeight a = n
  induction n using Nat.strong_induction_on generalizing a z with
  | h n ih =>
      rcases a with ⟨xs⟩
      cases xs with
      | nil => exact (hne rfl).elim
      | cons p ps =>
          cases ps with
          | nil =>
              rcases p with ⟨v, b⟩
              have ha : BT.trm [.db v b] = Dprin v b := rfl
              have hotb : isOT_BT b = true := by
                have hh : (isOT_BT b = true ∧
                    (gatherBT v b).all (fun x => lessBT x b) = true) ∧
                    descP [.db v b] = true := by
                  simpa [isOT_BT, isOT_BPList, isOT_BP] using hot
                exact hh.1.1
              have hbn : btWeight b < n := by
                rw [← hn]
                simp [btWeight, bpListWeight, bpWeight]
                omega
              by_cases hb : b = BZero
              · subst b
                by_cases hv0 : v = 0
                · subst v
                  simp [operB, bOperCore, BZero, lessBT, lessBPList]
                · by_cases hvtop : v = ⊤
                  · subst v
                    simp [operB, bOperCore, Dprin, BZero, lessBT, lessBPList,
                      lessBP, ENat.coe_lt_top]
                  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hvtop
                    rw [← hk] at hv0 hz ⊢
                    have hk0 : k ≠ 0 := by simpa using hv0
                    have hzin : z ∈ TBv ((k - 1 : ℕ) : ℕ∞) := by
                      rcases hz with hz | hz
                      · simpa [domB, domTag, domTagList, domTagBP, Dprin,
                          BZero, hk0, BDom.toSet] using hz
                      · exact NatSet_mem_TBv_bf hz
                    have hlt : ((k - 1 : ℕ) : ℕ∞) < (k : ℕ∞) := by
                      exact_mod_cast (Nat.sub_lt (Nat.zero_lt_of_ne_zero hk0)
                        (by omega : 0 < 1))
                    have hzlt : lessBT z (Dprin (k : ℕ∞) BZero) = true := by
                      simpa [Dprin] using
                        (TBv_lt_head_bf (z := z) (c := BZero) (rest := []) hzin hlt)
                    simpa [operB, bOperCore, Dprin, BZero, hk0] using hzlt
              · have hrec0 : lessBT (operB b BZero) b = true := by
                  exact ih (btWeight b) hbn b BZero hotb hb
                    (Or.inr ⟨0, rfl⟩) rfl
                cases hdb : domTag b with
                | empty =>
                    have hrec : lessBT (operB b z) b = true := by
                      have hzb : z ∈ domB b ∨ z ∈ NatSet := by
                        simpa [domB, domTag, domTagList, domTagBP, Dprin,
                          hb, hdb, BDom.toSet] using hz
                      exact ih (btWeight b) hbn b z hotb hb hzb rfl
                    simpa [operB, bOperCore, Dprin, hb, hdb, lessBT,
                      lessBPList, lessBP, hrec]
                | zeroOnly =>
                    let q : BP := .db v (operB b BZero)
                    have hqp : lessBP q (.db v b) = true := by
                      simp [q, lessBP, hrec0]
                    have hop : operB (Dprin v b) z =
                        .trm (List.replicate (numNat z + 1) q) := by
                      simp [operB, bOperCore, Dprin, hb, hdb, q,
                        multBT_single_bf]
                    have hgoal : lessBT (operB (Dprin v b) z)
                        (Dprin v b) = true := by
                      rw [hop, List.replicate_succ']
                      exact lessBT_replicate_snoc_bf (.db v b) q (numNat z) hqp
                    simpa [Dprin] using hgoal
                | naturals =>
                    have hrec : lessBT (operB b z) b = true := by
                      have hzb : z ∈ domB b ∨ z ∈ NatSet := by
                        simpa [domB, domTag, domTagList, domTagBP, Dprin,
                          hb, hdb, BDom.toSet] using hz
                      exact ih (btWeight b) hbn b z hotb hb hzb rfl
                    simpa [operB, bOperCore, Dprin, hb, hdb, lessBT,
                      lessBPList, lessBP, hrec]
                | below w =>
                    by_cases hvw : v ≤ (w : ℕ∞)
                    · let x := xseq b (w : ℕ∞) (numNat z)
                      have hxmem : x ∈ domB b := by
                        have hxshape : ∃ t, x = Dprin (w : ℕ∞) t := by
                          cases hnum : numNat z with
                          | zero =>
                              exact ⟨BZero, by simp [x, xseq, hnum, bOperCore]⟩
                          | succ i =>
                              exact ⟨bOperCore (.term b
                                (bOperCore (.xseq b (w : ℕ∞) i))), by
                                  simp [x, xseq, hnum, bOperCore]⟩
                        rcases hxshape with ⟨t, ht⟩
                        rw [ht]
                        simpa [domB, hdb, BDom.toSet] using Dprin_mem_TBv_bf w t
                      have hrec : lessBT (operB b x) b = true := by
                        exact ih (btWeight b) hbn b x hotb hb (Or.inl hxmem) rfl
                      simpa [operB, bOperCore, Dprin, hb, hdb, hvw, x,
                        lessBT, lessBPList, lessBP, hrec]
                    · have hrec : lessBT (operB b z) b = true := by
                        have hzb : z ∈ domB b ∨ z ∈ NatSet := by
                          simpa [domB, domTag, domTagList, domTagBP, Dprin,
                            hb, hdb, hvw, BDom.toSet] using hz
                        exact ih (btWeight b) hbn b z hotb hb hzb rfl
                      simpa [operB, bOperCore, Dprin, hb, hdb, hvw,
                        lessBT, lessBPList, lessBP, hrec]
          | cons q qs =>
              let ys : List BP := p :: q :: qs
              have hysne : ys ≠ [] := by simp [ys]
              let lastp := ys.getLast hysne
              have hlastmem : lastp ∈ q :: qs := by
                dsimp [lastp, ys]
                exact List.getLast_mem (by simp)
              have hweightLast : btWeight (.trm [lastp]) < n := by
                have hw := bpWeight_mem_succ_le_bf lastp (q :: qs) hlastmem
                simp only [bpListWeight] at hw
                rw [← hn]
                simp only [btWeight, bpListWeight]
                omega
              have hotsplit : isOT_BPList ys = true ∧ descP ys = true := by
                simpa [ys, isOT_BT] using hot
              have hotlastBP : isOT_BP lastp = true :=
                isOT_BPList_mem_bf ys hotsplit.1 (List.getLast_mem hysne)
              have hotlast : isOT_BT (.trm [lastp]) = true := by
                simpa [isOT_BT, isOT_BPList, descP] using hotlastBP
              have htaglast : domTag (.trm [lastp]) = domTag (.trm ys) := by
                calc
                  domTag (.trm [lastp]) = domTagBP lastp := by
                    simp [domTag, domTagList]
                  _ = domTag (.trm (ys.dropLast ++ [lastp])) :=
                    (domTag_snoc_bf ys.dropLast lastp).symm
                  _ = domTag (.trm ys) := by
                    rw [List.dropLast_append_getLast hysne]
              have hzlast : z ∈ domB (.trm [lastp]) ∨ z ∈ NatSet := by
                change z ∈ domB (.trm ys) ∨ z ∈ NatSet at hz
                rcases hz with hz | hz
                · left
                  rw [domB, htaglast]
                  exact hz
                · exact Or.inr hz
              have hrec : lessBT (operB (.trm [lastp]) z)
                  (.trm [lastp]) = true := by
                exact ih (btWeight (.trm [lastp])) hweightLast
                  (.trm [lastp]) z hotlast (by simp [BZero]) hzlast rfl
              have hopen : operB (.trm ys) z =
                  addBT (.trm ys.dropLast) (operB (.trm [lastp]) z) := by
                rw [← operB_snoc_bf ys.dropLast lastp z,
                  List.dropLast_append_getLast hysne]
              have hrebuild : addBT (.trm ys.dropLast) (.trm [lastp]) =
                  .trm ys := by
                change BT.trm (ys.dropLast ++ [lastp]) = BT.trm ys
                rw [List.dropLast_append_getLast hysne]
              rw [hopen, ← hrebuild]
              exact addBT_lt_right_bf (.trm ys.dropLast)
                (operB (.trm [lastp]) z) (.trm [lastp]) hrec

/-- Strengthened [Buc1] Lemma 3.2(a): every in-domain argument, and every
numeral argument accepted by the executable extension, gives strict descent. -/
theorem buchholz_fseq_descent (a z : BT) (hot : isOT_BT a = true)
    (hne : a ≠ BZero) (hz : z ∈ domB a ∨ z ∈ NatSet) :
    lessBT (operB a z) a = true :=
  buchholz_descent_general_bf a z hot hne hz

/-- [Buc1] Lemma 3.2(a), in the exact numeral form cited by the paper. -/
theorem buchholz_fseq_lt (a : BT) (n : ℕ) (hot : a ∈ OT_B)
    (hne : a ≠ BZero) :
    lessBT (operB a (numBT n)) a = true := by
  apply buchholz_fseq_descent a (numBT n)
  · exact hot.1
  · exact hne
  · exact Or.inr ⟨n, rfl⟩

#print axioms leBT_trans_bf
#print axioms operB_snoc_bf
#print axioms addBT_lt_right_bf
#print axioms buchholz_fseq_descent
#print axioms buchholz_fseq_lt

end PSS
