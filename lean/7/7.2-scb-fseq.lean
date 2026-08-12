import «7».«7.2-add-scb»
import «7».«7.2-scb-unique»

/-!
# §7.2 — scb decomposition and Buchholz fundamental sequences

Lean translation of the three conjuncts of `p_7_2_scb_fseq`, using the A23
correction already built into `Buchholz-rel-ord-6 の xseq`.
-/

namespace PSS

/-! ## The successor-body calculation -/

private theorem domTagList_snoc (ps : List BP) (p : BP) :
    domTagList (ps ++ [p]) = domTagBP p := by
  induction ps with
  | nil => simp [domTagList]
  | cons q qs ih =>
      cases qs with
      | nil => simp [domTagList]
      | cons r rs => simpa [domTagList] using ih

@[simp] private theorem zero_addBT (t : BT) : addBT BZero t = t := by
  rcases t with ⟨ps⟩
  rfl

private theorem addBT_assoc (a b c : BT) :
    addBT (addBT a b) c = addBT a (addBT b c) := by
  rcases a with ⟨as⟩
  rcases b with ⟨bs⟩
  rcases c with ⟨cs⟩
  simp [addBT, List.append_assoc]

private theorem bOperCore_list_snoc (ps : List BP) (p : BP) (z : BT) :
    bOperCore (.list (ps ++ [p]) z) =
      addBT (.trm ps) (bOperCore (.princ p z)) := by
  induction ps with
  | nil =>
      rw [bOperCore.eq_def]
      change bOperCore (.princ p z) = addBT BZero (bOperCore (.princ p z))
      exact (zero_addBT _).symm
  | cons q qs ih =>
      cases qs with
      | nil => simp [bOperCore, addBT]
      | cons r rs =>
          rw [bOperCore.eq_def]
          change addBT (.trm [q])
              (bOperCore (.list ((r :: rs) ++ [p]) z)) =
            addBT (.trm (q :: r :: rs)) (bOperCore (.princ p z))
          rw [ih]
          rw [← addBT_assoc]
          rfl

private theorem domTag_snoc (ps : List BP) (p : BP) :
    domTag (.trm (ps ++ [p])) = domTagBP p := by
  simp [domTag, domTagList_snoc]

private theorem operB_single (p : BP) (z : BT) :
    operB (.trm [p]) z = bOperCore (.princ p z) := by
  simp [operB, bOperCore]

private theorem operB_snoc (ps : List BP) (p : BP) (z : BT) :
    operB (.trm (ps ++ [p])) z =
      addBT (.trm ps) (operB (.trm [p]) z) := by
  rw [operB, bOperCore.eq_def]
  change bOperCore (.list (ps ++ [p]) z) =
    addBT (.trm ps) (operB (.trm [p]) z)
  rw [bOperCore_list_snoc, operB_single]

private theorem operB_dprin_naturals (u : ℕ∞) (a z : BT)
    (ha : a ≠ BZero) (htag : domTag a = .naturals) :
    operB (Dprin u a) z = Dprin u (operB a z) := by
  simp [operB, bOperCore, Dprin, ha, htag]

private theorem domTagBP_below_struct {w : ℕ∞} {a : BT} {m : ℕ}
    (ha : a ≠ BZero) (htag : domTagBP (.db w a) = .below m) :
    domTag a = .below m ∧ (m : ℕ∞) < w := by
  cases hda : domTag a with
  | empty => simp [domTagBP, ha, hda] at htag
  | zeroOnly => simp [domTagBP, ha, hda] at htag
  | naturals => simp [domTagBP, ha, hda] at htag
  | below k =>
      by_cases hle : w ≤ (k : ℕ∞)
      · simp [domTagBP, ha, hda, hle] at htag
      · have hkm : k = m := by
          simpa [domTagBP, ha, hda, hle] using htag
        subst k
        exact ⟨by simp, lt_of_not_ge hle⟩

theorem operB_dprin_below {w : ℕ∞} {a z : BT} {m : ℕ}
    (ha : a ≠ BZero) (htag : domTag a = .below m)
    (hmw : (m : ℕ∞) < w) :
    operB (Dprin w a) z = Dprin w (operB a z) := by
  have hnle : ¬w ≤ (m : ℕ∞) := not_le_of_gt hmw
  simp [operB, bOperCore, Dprin, ha, htag, hnle]

private theorem domTagBP_naturals_of_body (u : ℕ∞) (a : BT)
    (ha : a ≠ BZero) (htag : domTag a = .naturals) :
    domTagBP (.db u a) = .naturals := by
  simp [domTagBP, ha, htag]

private theorem scbOfFlat {t : BT} {p : BP} {s b : List Sym}
    (hflat : flatBT t = s ++ flatBP p ++ b)
    (hb : ∀ x ∈ b, x = .rp) (hdf : dfree_BP p = true) :
    scb_decomp t s (flatBP p) b := by
  refine ⟨hflat, ?_, hb⟩
  intro _
  exact ⟨p, hdf, rfl⟩

/-- Article (1-1): the fundamental sequence of a term ending in
`D_v (t₁ + D_0 0)` replaces that last summand by `n+1` copies of `D_v t₁`. -/
theorem scb_fseq_succ (t₀ t₁ : BT) (v n : ℕ)
    (_ht₀ : t₀ ∈ T_B) (_ht₁ : t₁ ∈ T_B) :
    operB (addBT t₀ (Dprin (v : ℕ∞)
      (addBT t₁ (Dprin 0 BZero)))) (numBT n) =
      addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) (n + 1)) := by
  rcases t₀ with ⟨ps₀⟩
  rcases t₁ with ⟨ps₁⟩
  simp [operB, bOperCore, bOperCore_list_snoc, domTagList_snoc,
    addBT, multBT, numBT, numNat, Dprin, BZero, domTag, domTagBP]

/-! ## Transport along an scb spine -/

/-- If a `NatSet`-domain principal occurrence lies on the scb/right spine,
`operB` transforms that principal and leaves the surrounding flat context
unchanged.  The domain tag of every enclosing spine node is again `naturals`. -/
theorem operB_scb_spine {t : BT} {p p' : BP} {z : BT}
    {s b : List Sym}
    (hocc : flatBT t = s ++ flatBP p ++ b)
    (hb : ∀ x ∈ b, x = .rp)
    (hdfp : dfree_BP p = true)
    (htagp : domTagBP p = .naturals)
    (hop : operB (.trm [p]) z = .trm [p']) :
    domTag t = .naturals ∧
      flatBT (operB t z) = s ++ flatBP p' ++ b := by
  generalize hn : (flatBT t).length = n
  induction n using Nat.strong_induction_on generalizing t s b with
  | h n ih =>
      rcases t with ⟨ys⟩
      cases ys with
      | nil =>
          have hlen := congrArg List.length hocc
          have hpge := flatBP_length_ge_two p
          simp [flatBT] at hlen
          omega
      | cons y ys =>
          let full : List BP := y :: ys
          have hfull : full ≠ [] := by simp [full]
          let init := full.dropLast
          let q := full.getLast hfull
          have hsnoc : init ++ [q] = full :=
            List.dropLast_append_getLast hfull
          have hlist : init ++ [q] = y :: ys := by
            simpa [full] using hsnoc
          have hocc' : flatBT (.trm (init ++ [q])) =
              s ++ flatBP p ++ b := by
            rw [hsnoc]
            simpa [full] using hocc
          have hn' : (flatBT (.trm (init ++ [q]))).length = n := by
            rw [hsnoc]
            simpa [full] using hn
          have horig : scb_decomp (.trm (init ++ [q])) s (flatBP p) b :=
            scbOfFlat hocc' hb hdfp
          cases hi : init with
          | nil =>
              have hsingle : [q] = y :: ys := by
                simpa [hi] using hlist
              have hoccSingle : flatBT (.trm [q]) =
                  s ++ flatBP p ++ b := by
                simpa [hi] using hocc'
              have hnSingle : (flatBT (.trm [q])).length = n := by
                simpa [hi] using hn'
              have hd := scb_last_dichotomy
                (pre := []) (post := []) (q := q) (pp := p)
                (h := by simpa [List.append_assoc] using hoccSingle)
                hb (by simp) (by simp)
              rcases hd with hmax | ⟨u, a, s₂, b₂, hq, haocc, hb₂, _⟩
              · have hpq : p = q := flatBP_injective hmax.2.1
                have hs : s = [] := by
                  cases s with
                  | nil => rfl
                  | cons x xs => simp at hmax
                have hres : domTag (.trm [q]) = .naturals ∧
                    flatBT (operB (.trm [q]) z) =
                      s ++ flatBP p' ++ b := by
                  constructor
                  · rw [← hpq]
                    simpa [domTag, domTagList] using htagp
                  · rw [← hpq, hop]
                    simp [hs, hmax.2.2, flatBT]
                simpa [hsingle] using hres
              · have hlt : (flatBT a).length < n := by
                  rw [← hnSingle, hq]
                  simp [flatBT, flatBP]
                have hane : a ≠ BZero := by
                  intro ha
                  subst a
                  have hlen := congrArg List.length haocc
                  have hpge := flatBP_length_ge_two p
                  simp [BZero, flatBT] at hlen
                  omega
                obtain ⟨htaga, hopa⟩ :=
                  ih (flatBT a).length hlt (t := a) (s := s₂) (b := b₂)
                    haocc hb₂ rfl
                have hopq : operB (.trm [q]) z =
                    Dprin u (operB a z) := by
                  rw [hq]
                  exact operB_dprin_naturals u a z hane htaga
                have hcanflat : flatBT (.trm [q]) =
                    (.dsym u :: s₂) ++ flatBP p ++ b₂ := by
                  rw [hq]
                  simp [flatBT, flatBP, haocc, List.append_assoc]
                have hcan := scbOfFlat hcanflat hb₂ hdfp
                have halign := scb_unique_decomp_unconditional
                  (.trm [q]) s (.dsym u :: s₂) (flatBP p) b b₂
                    (by simpa [hi] using horig) hcan
                have hres : domTag (.trm [q]) = .naturals ∧
                    flatBT (operB (.trm [q]) z) =
                      s ++ flatBP p' ++ b := by
                  constructor
                  · rw [hq]
                    simp [domTag, domTagList,
                      domTagBP_naturals_of_body u a hane htaga]
                  · rw [halign.1, halign.2, hopq]
                    simp [Dprin, flatBT, flatBP, hopa, List.append_assoc]
                simpa [hsingle] using hres
          | cons r rs =>
              have hmulti : (r :: rs) ++ [q] = y :: ys := by
                simpa [hi] using hlist
              have hoccMulti : flatBT (.trm ((r :: rs) ++ [q])) =
                  s ++ flatBP p ++ b := by
                simpa [hi] using hocc'
              have hnMulti : (flatBT (.trm ((r :: rs) ++ [q]))).length = n := by
                simpa [hi] using hn'
              let pre := .lp :: flatComponentRun (r :: rs)
              have hshape : flatBT (.trm ((r :: rs) ++ [q])) =
                  pre ++ flatBP q ++ [.rp] := by
                simpa [pre] using flatBT_multi_snoc r rs q
              have hcut := scb_cut_reaches_last r rs q p s b hoccMulti hb
              have hd := scb_last_dichotomy
                (pre := pre) (post := [.rp]) (q := q) (pp := p)
                (h := hshape.symm.trans hoccMulti) hb (by simp)
                (by simpa only [pre, List.length_cons, Nat.add_comm] using hcut)
              rcases hd with hmax | ⟨u, a, s₂, b₂, hq, haocc, hb₂, _⟩
              · have hpq : p = q := flatBP_injective hmax.2.1
                have hcanflat : flatBT (.trm ((r :: rs) ++ [q])) =
                    pre ++ flatBP p ++ [.rp] := by
                  simpa [hpq] using hshape
                have hcan : scb_decomp (.trm ((r :: rs) ++ [q]))
                    pre (flatBP p) [.rp] :=
                  scbOfFlat hcanflat (by simp) hdfp
                have halign := scb_unique_decomp_unconditional
                  (.trm ((r :: rs) ++ [q])) s pre (flatBP p) b [.rp]
                    (by simpa [hi] using horig) hcan
                have hopen : operB (.trm ((r :: rs) ++ [q])) z =
                    .trm ((r :: rs) ++ [p']) := by
                  rw [← hpq, operB_snoc, hop]
                  rfl
                have hflatop : flatBT (operB (.trm ((r :: rs) ++ [q])) z) =
                    pre ++ flatBP p' ++ [.rp] := by
                  rw [hopen]
                  simpa [pre] using flatBT_multi_snoc r rs p'
                have hres : domTag (.trm ((r :: rs) ++ [q])) = .naturals ∧
                    flatBT (operB (.trm ((r :: rs) ++ [q])) z) =
                      s ++ flatBP p' ++ b := by
                  constructor
                  · rw [← hpq, domTag_snoc]
                    exact htagp
                  · rw [halign.1, halign.2]
                    exact hflatop
                simpa [hmulti] using hres
              · have hlt : (flatBT a).length < n := by
                  rw [← hnMulti, flatBT_multi_snoc, hq]
                  simp [flatBP]
                  omega
                have hane : a ≠ BZero := by
                  intro ha
                  subst a
                  have hlen := congrArg List.length haocc
                  have hpge := flatBP_length_ge_two p
                  simp [BZero, flatBT] at hlen
                  omega
                obtain ⟨htaga, hopa⟩ :=
                  ih (flatBT a).length hlt (t := a) (s := s₂) (b := b₂)
                    haocc hb₂ rfl
                have hopq : operB (.trm [q]) z =
                    Dprin u (operB a z) := by
                  rw [hq]
                  exact operB_dprin_naturals u a z hane htaga
                let canS := pre ++ (.dsym u :: s₂)
                let canB := b₂ ++ [.rp]
                have hcanflat : flatBT (.trm ((r :: rs) ++ [q])) =
                    canS ++ flatBP p ++ canB := by
                  rw [hshape, hq]
                  simp [flatBP, haocc, canS, canB, List.append_assoc]
                have hcan : scb_decomp (.trm ((r :: rs) ++ [q]))
                    canS (flatBP p) canB :=
                  scbOfFlat hcanflat (by
                    intro x hx
                    rcases List.mem_append.mp hx with hx | hx
                    · exact hb₂ x hx
                    · simpa using hx) hdfp
                have halign := scb_unique_decomp_unconditional
                  (.trm ((r :: rs) ++ [q])) s canS (flatBP p) b canB
                    (by simpa [hi] using horig) hcan
                have hopen : operB (.trm ((r :: rs) ++ [q])) z =
                    .trm ((r :: rs) ++ [.db u (operB a z)]) := by
                  rw [operB_snoc, hopq]
                  rfl
                have hflatop : flatBT (operB (.trm ((r :: rs) ++ [q])) z) =
                    canS ++ flatBP p' ++ canB := by
                  rw [hopen, flatBT_multi_snoc]
                  simp [pre, canS, canB, flatComponentRun, flatBP, hopa,
                    List.append_assoc]
                have hres : domTag (.trm ((r :: rs) ++ [q])) = .naturals ∧
                    flatBT (operB (.trm ((r :: rs) ++ [q])) z) =
                      s ++ flatBP p' ++ b := by
                  constructor
                  · rw [hq, domTag_snoc]
                    exact domTagBP_naturals_of_body u a hane htaga
                  · rw [halign.1, halign.2]
                    exact hflatop
                simpa [hmulti] using hres

/-- The `below m` analogue of `operB_scb_spine`.  Here the ambient tag is an
input: it forces every principal strictly above the marked occurrence to take
the plain descent branch of `operB`. -/
theorem operB_scb_spine_below {t : BT} {p p' : BP} {z : BT}
    {s b : List Sym} {m : ℕ}
    (hocc : flatBT t = s ++ flatBP p ++ b)
    (hb : ∀ x ∈ b, x = .rp)
    (hdfp : dfree_BP p = true)
    (htagt : domTag t = .below m)
    (hop : operB (.trm [p]) z = .trm [p']) :
    flatBT (operB t z) = s ++ flatBP p' ++ b := by
  generalize hn : (flatBT t).length = n
  induction n using Nat.strong_induction_on generalizing t s b with
  | h n ih =>
      rcases t with ⟨ys⟩
      cases ys with
      | nil =>
          have hlen := congrArg List.length hocc
          have hpge := flatBP_length_ge_two p
          simp [flatBT] at hlen
          omega
      | cons y ys =>
          let full : List BP := y :: ys
          have hfull : full ≠ [] := by simp [full]
          let init := full.dropLast
          let q := full.getLast hfull
          have hsnoc : init ++ [q] = full :=
            List.dropLast_append_getLast hfull
          have hlist : init ++ [q] = y :: ys := by
            simpa [full] using hsnoc
          have hocc' : flatBT (.trm (init ++ [q])) =
              s ++ flatBP p ++ b := by
            rw [hsnoc]
            simpa [full] using hocc
          have hn' : (flatBT (.trm (init ++ [q]))).length = n := by
            rw [hsnoc]
            simpa [full] using hn
          have horig : scb_decomp (.trm (init ++ [q])) s (flatBP p) b :=
            scbOfFlat hocc' hb hdfp
          cases hi : init with
          | nil =>
              have hsingle : [q] = y :: ys := by
                simpa [hi] using hlist
              have hoccSingle : flatBT (.trm [q]) =
                  s ++ flatBP p ++ b := by
                simpa [hi] using hocc'
              have hnSingle : (flatBT (.trm [q])).length = n := by
                simpa [hi] using hn'
              have htagSingle : domTag (.trm [q]) = .below m := by
                simpa [hsingle] using htagt
              have hd := scb_last_dichotomy
                (pre := []) (post := []) (q := q) (pp := p)
                (h := by simpa [List.append_assoc] using hoccSingle)
                hb (by simp) (by simp)
              rcases hd with hmax | ⟨w, a, s₂, b₂, hq, haocc, hb₂, _⟩
              · have hpq : p = q := flatBP_injective hmax.2.1
                have hs : s = [] := by
                  cases s with
                  | nil => rfl
                  | cons x xs => simp at hmax
                have hres : flatBT (operB (.trm [q]) z) =
                    s ++ flatBP p' ++ b := by
                  rw [← hpq, hop]
                  simp [hs, hmax.2.2, flatBT]
                simpa [hsingle] using hres
              · have hlt : (flatBT a).length < n := by
                  rw [← hnSingle, hq]
                  simp [flatBT, flatBP]
                have hane : a ≠ BZero := by
                  intro ha
                  subst a
                  have hlen := congrArg List.length haocc
                  have hpge := flatBP_length_ge_two p
                  simp [BZero, flatBT] at hlen
                  omega
                have htagq : domTagBP q = .below m := by
                  simpa [domTag, domTagList] using htagSingle
                rw [hq] at htagq
                obtain ⟨htaga, hmw⟩ :=
                  domTagBP_below_struct hane htagq
                have hopa := ih (flatBT a).length hlt
                  (t := a) (s := s₂) (b := b₂)
                  haocc hb₂ htaga rfl
                have hopq : operB (.trm [q]) z =
                    Dprin w (operB a z) := by
                  rw [hq]
                  exact operB_dprin_below hane htaga hmw
                have hcanflat : flatBT (.trm [q]) =
                    (.dsym w :: s₂) ++ flatBP p ++ b₂ := by
                  rw [hq]
                  simp [flatBT, flatBP, haocc, List.append_assoc]
                have hcan := scbOfFlat hcanflat hb₂ hdfp
                have halign := scb_unique_decomp_unconditional
                  (.trm [q]) s (.dsym w :: s₂) (flatBP p) b b₂
                    (by simpa [hi] using horig) hcan
                have hres : flatBT (operB (.trm [q]) z) =
                    s ++ flatBP p' ++ b := by
                  rw [halign.1, halign.2, hopq]
                  simp [Dprin, flatBT, flatBP, hopa, List.append_assoc]
                simpa [hsingle] using hres
          | cons r rs =>
              have hmulti : (r :: rs) ++ [q] = y :: ys := by
                simpa [hi] using hlist
              have hoccMulti : flatBT (.trm ((r :: rs) ++ [q])) =
                  s ++ flatBP p ++ b := by
                simpa [hi] using hocc'
              have hnMulti : (flatBT (.trm ((r :: rs) ++ [q]))).length = n := by
                simpa [hi] using hn'
              have htagMulti : domTag (.trm ((r :: rs) ++ [q])) =
                  .below m := by
                simpa [hmulti] using htagt
              have htagq : domTagBP q = .below m := by
                rw [domTag_snoc] at htagMulti
                exact htagMulti
              let pre := .lp :: flatComponentRun (r :: rs)
              have hshape : flatBT (.trm ((r :: rs) ++ [q])) =
                  pre ++ flatBP q ++ [.rp] := by
                simpa [pre] using flatBT_multi_snoc r rs q
              have hcut := scb_cut_reaches_last r rs q p s b hoccMulti hb
              have hd := scb_last_dichotomy
                (pre := pre) (post := [.rp]) (q := q) (pp := p)
                (h := hshape.symm.trans hoccMulti) hb (by simp)
                (by simpa only [pre, List.length_cons, Nat.add_comm] using hcut)
              rcases hd with hmax | ⟨w, a, s₂, b₂, hq, haocc, hb₂, _⟩
              · have hpq : p = q := flatBP_injective hmax.2.1
                have hcanflat : flatBT (.trm ((r :: rs) ++ [q])) =
                    pre ++ flatBP p ++ [.rp] := by
                  simpa [hpq] using hshape
                have hcan : scb_decomp (.trm ((r :: rs) ++ [q]))
                    pre (flatBP p) [.rp] :=
                  scbOfFlat hcanflat (by simp) hdfp
                have halign := scb_unique_decomp_unconditional
                  (.trm ((r :: rs) ++ [q])) s pre (flatBP p) b [.rp]
                    (by simpa [hi] using horig) hcan
                have hopen : operB (.trm ((r :: rs) ++ [q])) z =
                    .trm ((r :: rs) ++ [p']) := by
                  rw [← hpq, operB_snoc, hop]
                  rfl
                have hflatop : flatBT (operB (.trm ((r :: rs) ++ [q])) z) =
                    pre ++ flatBP p' ++ [.rp] := by
                  rw [hopen]
                  simpa [pre] using flatBT_multi_snoc r rs p'
                rw [halign.1, halign.2]
                simpa [hmulti] using hflatop
              · have hlt : (flatBT a).length < n := by
                  rw [← hnMulti, flatBT_multi_snoc, hq]
                  simp [flatBP]
                  omega
                have hane : a ≠ BZero := by
                  intro ha
                  subst a
                  have hlen := congrArg List.length haocc
                  have hpge := flatBP_length_ge_two p
                  simp [BZero, flatBT] at hlen
                  omega
                rw [hq] at htagq
                obtain ⟨htaga, hmw⟩ :=
                  domTagBP_below_struct hane htagq
                have hopa := ih (flatBT a).length hlt
                  (t := a) (s := s₂) (b := b₂)
                  haocc hb₂ htaga rfl
                have hopq : operB (.trm [q]) z =
                    Dprin w (operB a z) := by
                  rw [hq]
                  exact operB_dprin_below hane htaga hmw
                let canS := pre ++ (.dsym w :: s₂)
                let canB := b₂ ++ [.rp]
                have hcanflat : flatBT (.trm ((r :: rs) ++ [q])) =
                    canS ++ flatBP p ++ canB := by
                  rw [hshape, hq]
                  simp [flatBP, haocc, canS, canB, List.append_assoc]
                have hcan : scb_decomp (.trm ((r :: rs) ++ [q]))
                    canS (flatBP p) canB :=
                  scbOfFlat hcanflat (by
                    intro x hx
                    rcases List.mem_append.mp hx with hx | hx
                    · exact hb₂ x hx
                    · simpa using hx) hdfp
                have halign := scb_unique_decomp_unconditional
                  (.trm ((r :: rs) ++ [q])) s canS (flatBP p) b canB
                    (by simpa [hi] using horig) hcan
                have hopen : operB (.trm ((r :: rs) ++ [q])) z =
                    .trm ((r :: rs) ++ [.db w (operB a z)]) := by
                  rw [operB_snoc, hopq]
                  rfl
                have hflatop : flatBT (operB (.trm ((r :: rs) ++ [q])) z) =
                    canS ++ flatBP p' ++ canB := by
                  rw [hopen, flatBT_multi_snoc]
                  simp [pre, canS, canB, flatComponentRun, flatBP, hopa,
                    List.append_assoc]
                rw [halign.1, halign.2]
                simpa [hmulti] using hflatop

private theorem succBody_naturals (t₀ t₁ : BT) (v : ℕ) :
    domTag (addBT t₀ (Dprin (v : ℕ∞)
      (addBT t₁ (Dprin 0 BZero)))) = .naturals := by
  rcases t₀ with ⟨ps₀⟩
  rcases t₁ with ⟨ps₁⟩
  simp [addBT, Dprin, domTag_snoc, domTagBP, BZero]

private theorem multBT_mem_T_B {a : BT} (ha : a ∈ T_B) :
    ∀ k, multBT a k ∈ T_B
  | 0 => by simp [multBT, T_B, BZero, dfree_BT, dfree_BPList]
  | k + 1 => addBT_mem_T_B (multBT_mem_T_B ha k) ha

/-- Article (1-2): the (1-1) calculation transports through any surrounding
scb/right-spine context. -/
theorem scb_fseq_decomp {t₀ t₁ t : BT} {u v n : ℕ}
    {s b : List Sym}
    (ht₀ : t₀ ∈ T_B) (ht₁ : t₁ ∈ T_B) (_ht : t ∈ T_B)
    (hd : scb_decomp t s
      (flatBT (Dprin (u : ℕ∞)
        (addBT t₀ (Dprin (v : ℕ∞)
          (addBT t₁ (Dprin 0 BZero)))))) b) :
    scb_decomp (operB t (numBT n)) s
      (flatBT (Dprin (u : ℕ∞)
        (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) (n + 1))))) b := by
  let body := addBT t₀ (Dprin (v : ℕ∞)
    (addBT t₁ (Dprin 0 BZero)))
  let body' := addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) (n + 1))
  let p : BP := .db (u : ℕ∞) body
  let p' : BP := .db (u : ℕ∞) body'
  have hbodyne : body ≠ BZero := by
    rcases t₀ with ⟨ps₀⟩
    rcases t₁ with ⟨ps₁⟩
    simp [body, addBT, Dprin, BZero]
  have htagbody : domTag body = .naturals :=
    succBody_naturals t₀ t₁ v
  have htagp : domTagBP p = .naturals :=
    domTagBP_naturals_of_body (u : ℕ∞) body hbodyne htagbody
  have hd0 : Dprin 0 BZero ∈ T_B := by
    simp [T_B, Dprin, BZero, dfree_BT, dfree_BP, dfree_BPList]
  have hinner : addBT t₁ (Dprin 0 BZero) ∈ T_B :=
    addBT_mem_T_B ht₁ hd0
  have hdvinner : Dprin (v : ℕ∞) (addBT t₁ (Dprin 0 BZero)) ∈ T_B := by
    simpa [T_B, Dprin, dfree_BT, dfree_BP, dfree_BPList] using hinner
  have hbodyT : body ∈ T_B := addBT_mem_T_B ht₀ hdvinner
  have hdfp : dfree_BP p = true := by
    simpa [p, dfree_BP] using hbodyT
  have hopbody : operB body (numBT n) = body' := by
    exact scb_fseq_succ t₀ t₁ v n ht₀ ht₁
  have hopp : operB (.trm [p]) (numBT n) = .trm [p'] := by
    rw [show (.trm [p] : BT) = Dprin (u : ℕ∞) body by rfl]
    rw [operB_dprin_naturals (u : ℕ∞) body (numBT n) hbodyne htagbody,
      hopbody]
    rfl
  have hocc : flatBT t = s ++ flatBP p ++ b := by
    simpa [p, Dprin, flatBT] using hd.1
  obtain ⟨_, hflat⟩ := operB_scb_spine hocc hd.2.2 hdfp htagp hopp
  have hdvt₁ : Dprin (v : ℕ∞) t₁ ∈ T_B := by
    simpa [T_B, Dprin, dfree_BT, dfree_BP, dfree_BPList] using ht₁
  have hbody'T : body' ∈ T_B :=
    addBT_mem_T_B ht₀ (multBT_mem_T_B hdvt₁ (n + 1))
  have hdfp' : dfree_BP p' = true := by
    simpa [p', dfree_BP] using hbody'T
  have hout := scbOfFlat hflat hd.2.2 hdfp'
  simpa [p', body', Dprin, flatBT] using hout

/-! ## The kind-1 tower -/

theorem operB_dprin_kind1 {body z : BT} {u : ℕ∞} {m : ℕ}
    (hne : body ≠ BZero) (htag : domTag body = .below m)
    (hle : u ≤ (m : ℕ∞)) :
    operB (Dprin u body) z =
      Dprin u (operB body (xseq body (m : ℕ∞) (numNat z))) := by
  simp [operB, bOperCore, Dprin, hne, htag, hle, xseq]

private theorem operB_Dv_zero_id (v : ℕ) (z : BT) (hv : 0 < v) :
    operB (Dprin (v : ℕ∞) BZero) z = z := by
  have hv0 : (v : ℕ∞) ≠ 0 := by simpa using (Nat.ne_of_gt hv)
  simp [operB, bOperCore, Dprin, BZero, hv0]

private theorem xseq_is_principal (body : BT) (m : ℕ∞) (i : ℕ) :
    ∃ p, xseq body m i = .trm [p] := by
  cases i with
  | zero => exact ⟨.db m BZero, by simp [xseq, bOperCore, Dprin]⟩
  | succ i =>
      exact ⟨.db m (operB body (xseq body m i)), by
        simp [xseq, bOperCore, operB, Dprin]⟩

private theorem flatten_replicate_snoc {α : Type} (xs : List α) (n : ℕ) :
    List.flatten (List.replicate (n + 1) xs) =
      List.flatten (List.replicate n xs) ++ xs := by
  rw [List.replicate_add, List.flatten_append]
  simp

private theorem flatten_replicate_shift {α : Type}
    (xs ys : List α) (n : ℕ) :
    xs ++ List.flatten (List.replicate n (ys ++ xs)) =
      List.flatten (List.replicate n (xs ++ ys)) ++ xs := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.replicate_succ, List.flatten_cons, List.append_assoc]
      rw [ih]

private theorem tower_readback {α : Type} (s b : List α) (d z : α) (n : ℕ) :
    s ++ (List.flatten (List.replicate n ([d] ++ s)) ++ [d, z] ++
      List.flatten (List.replicate n b)) ++ b =
      List.flatten (List.replicate (n + 1) (s ++ [d])) ++ [z] ++
      List.flatten (List.replicate (n + 1) b) := by
  rw [flatten_replicate_snoc b n,
    flatten_replicate_snoc (s ++ [d]) n]
  have hshift := flatten_replicate_shift s [d] n
  simp only [List.append_assoc]
  calc
    s ++ ((List.replicate n ([d] ++ s)).flatten ++
        ([d, z] ++ ((List.replicate n b).flatten ++ b))) =
        (s ++ (List.replicate n ([d] ++ s)).flatten) ++
          ([d, z] ++ ((List.replicate n b).flatten ++ b)) := by
            rw [List.append_assoc]
    _ = ((List.replicate n (s ++ [d])).flatten ++ s) ++
          ([d, z] ++ ((List.replicate n b).flatten ++ b)) := by
            rw [hshift]
    _ = (List.replicate n (s ++ [d])).flatten ++
          (s ++ ([d] ++ ([z] ++ ((List.replicate n b).flatten ++ b)))) := by
            simp [List.append_assoc]

/-- Flat form of the corrected A23 auxiliary tower over a body whose final
scb occurrence is `D_v 0`. -/
private theorem xseq_body_tower_flat {body : BT} {v i : ℕ}
    {s₀ b₀ : List Sym}
    (hv : 0 < v)
    (htag : domTag body = .below (v - 1))
    (hscb : scb_decomp body s₀
      (flatBT (Dprin (v : ℕ∞) BZero)) b₀) :
    flatBT (xseq body ((v - 1 : ℕ) : ℕ∞) i) =
      List.flatten (List.replicate i
        ([.dsym ((v - 1 : ℕ) : ℕ∞)] ++ s₀)) ++
      [.dsym ((v - 1 : ℕ) : ℕ∞), .zero] ++
      List.flatten (List.replicate i b₀) := by
  induction i with
  | zero => simp [xseq, bOperCore, Dprin, BZero, flatBT, flatBP]
  | succ j ih =>
      let m : ℕ∞ := ((v - 1 : ℕ) : ℕ∞)
      let marked : BP := .db (v : ℕ∞) BZero
      let xj := xseq body m j
      obtain ⟨rp, hxj⟩ := xseq_is_principal body m j
      have hxj' : xj = .trm [rp] := by simpa [xj, m] using hxj
      have hmarkedDf : dfree_BP marked = true := by
        simp [marked, dfree_BP, BZero, dfree_BT, dfree_BPList]
      have himage : operB (.trm [marked]) xj = .trm [rp] := by
        rw [show (.trm [marked] : BT) = Dprin (v : ℕ∞) BZero by rfl]
        rw [operB_Dv_zero_id v xj hv, hxj']
      have hocc : flatBT body = s₀ ++ flatBP marked ++ b₀ := by
        simpa [marked, Dprin, flatBT] using hscb.1
      have htransport : flatBT (operB body xj) =
          s₀ ++ flatBT xj ++ b₀ := by
        have h := operB_scb_spine_below hocc hscb.2.2 hmarkedDf
          htag himage
        simpa [hxj', flatBT] using h
      have hstep : xseq body m (j + 1) =
          Dprin m (operB body xj) := by
        simp [xseq, bOperCore, m, xj, operB]
      change flatBT (xseq body m (j + 1)) = _
      rw [hstep]
      simp only [Dprin, flatBT, flatBP]
      rw [htransport, ih]
      rw [flatten_replicate_snoc b₀ j]
      simp [m, List.replicate_succ, List.append_assoc]

/-- General kind-1 engine.  The `below (v-1)` hypothesis is the tag form of
the article's `domB body = T_{v-1}` condition. -/
theorem scb_fseq_kind1_general {t body : BT} {u v n : ℕ}
    {s₀ s₁ b₀ b₁ : List Sym}
    (_ht : t ∈ T_B) (huv : u < v) (hbodyT : body ∈ T_B)
    (htag : domTag body = .below (v - 1))
    (hbodyne : body ≠ BZero)
    (hinner : scb_decomp body s₀
      (flatBT (Dprin (v : ℕ∞) BZero)) b₀)
    (hk1 : scb_kind1 t s₁
      (flatBT (Dprin (u : ℕ∞) body)) b₁) :
    v > u ∧
      flatBT (operB t (numBT n)) =
        s₁ ++ (.dsym (u : ℕ∞) ::
          List.flatten (List.replicate (n + 1)
            (s₀ ++ [.dsym ((v - 1 : ℕ) : ℕ∞)])) ++
          [.zero] ++ List.flatten (List.replicate (n + 1) b₀)) ++ b₁ := by
  have hv : 0 < v := by omega
  have hleNat : u ≤ v - 1 := by omega
  have hle : (u : ℕ∞) ≤ ((v - 1 : ℕ) : ℕ∞) := by
    exact ENat.coe_le_coe.mpr hleNat
  have hle' : (u : ℕ∞) ≤ (v : ℕ∞) - 1 := by
    calc
      (u : ℕ∞) ≤ ((v - 1 : ℕ) : ℕ∞) := hle
      _ = (v : ℕ∞) - 1 := ENat.coe_sub v 1
  let m : ℕ∞ := ((v - 1 : ℕ) : ℕ∞)
  let xn := xseq body m n
  let core := operB body xn
  let p : BP := .db (u : ℕ∞) body
  let p' : BP := .db (u : ℕ∞) core
  have hdfp : dfree_BP p = true := by
    simpa [p, dfree_BP] using hbodyT
  have htagp : domTagBP p = .naturals := by
    simp [p, domTagBP, hbodyne, htag, hle']
  have hopp : operB (.trm [p]) (numBT n) = .trm [p'] := by
    have heval := operB_dprin_kind1 (body := body) (z := numBT n)
      (u := (u : ℕ∞)) (m := v - 1) hbodyne htag hle
    simpa [p, p', core, xn, numBT, numNat] using heval
  have houtOcc : flatBT t = s₁ ++ flatBP p ++ b₁ := by
    simpa [p, Dprin, flatBT] using hk1.1.1
  obtain ⟨_, hout⟩ := operB_scb_spine houtOcc hk1.1.2.2
    hdfp htagp hopp
  have houter : flatBT (operB t (numBT n)) =
      s₁ ++ (.dsym (u : ℕ∞) :: flatBT core) ++ b₁ := by
    simpa [p', core, flatBP] using hout
  let marked : BP := .db (v : ℕ∞) BZero
  obtain ⟨rp, hxnp⟩ := xseq_is_principal body m n
  have hxnPrincipal : xn = .trm [rp] := by
    simpa [xn, m] using hxnp
  have hmarkedDf : dfree_BP marked = true := by
    simp [marked, dfree_BP, BZero, dfree_BT, dfree_BPList]
  have hmarkedImage : operB (.trm [marked]) xn = .trm [rp] := by
    rw [show (.trm [marked] : BT) = Dprin (v : ℕ∞) BZero by rfl]
    rw [operB_Dv_zero_id v xn hv, hxnPrincipal]
  have hinnerOcc : flatBT body = s₀ ++ flatBP marked ++ b₀ := by
    simpa [marked, Dprin, flatBT] using hinner.1
  have hcore : flatBT core = s₀ ++ flatBT xn ++ b₀ := by
    have h := operB_scb_spine_below hinnerOcc hinner.2.2 hmarkedDf
      htag hmarkedImage
    simpa [core, hxnPrincipal, flatBT] using h
  have hxn := xseq_body_tower_flat hv htag hinner (i := n)
  have hcoreFinal : flatBT core =
      List.flatten (List.replicate (n + 1)
        (s₀ ++ [.dsym ((v - 1 : ℕ) : ℕ∞)])) ++
      [.zero] ++ List.flatten (List.replicate (n + 1) b₀) := by
    rw [hcore]
    rw [show flatBT xn = flatBT (xseq body ((v - 1 : ℕ) : ℕ∞) n) by
      rfl, hxn]
    simpa [List.append_assoc] using
      (tower_readback s₀ b₀ (.dsym ((v - 1 : ℕ) : ℕ∞)) .zero n)
  constructor
  · exact huv
  · rw [houter, hcoreFinal]
    simp [List.append_assoc]

private theorem dprin_of_flat_dsym {c : BT} {u : ℕ∞} {xs : List Sym}
    (h : flatBT c = .dsym u :: xs) :
    ∃ body, c = Dprin u body ∧ flatBT body = xs := by
  rcases c with ⟨ps⟩
  cases ps with
  | nil => simp [flatBT] at h
  | cons p ps =>
      cases ps with
      | nil =>
          rcases p with ⟨w, body⟩
          simp [flatBT, flatBP] at h
          exact ⟨body, by simp [Dprin, h.1], h.2⟩
      | cons q qs => simp [flatBT] at h

private theorem rightNodes_ends_at_marked_zero {body : BT} {v : ℕ}
    {s b : List Sym}
    (hocc : flatBT body = s ++ flatBT (Dprin (v : ℕ∞) BZero) ++ b)
    (hb : ∀ x ∈ b, x = .rp) :
    ∃ a, RightNodes body = a ++ [v] := by
  have hocc' : flatBT body = s ++ flatBP (.db (v : ℕ∞) BZero) ++ b := by
    simpa [Dprin, flatBT] using hocc
  obtain ⟨k, hk⟩ := scb_occurrence_rightNodes_suffix hocc' hb
  refine ⟨(RightNodes body).take k, ?_⟩
  calc
    RightNodes body = (RightNodes body).take k ++
        (RightNodes body).drop k := (List.take_append_drop k _).symm
    _ = (RightNodes body).take k ++ [v] := by
      rw [← hk]
      simp [RightNodes, rightNodesList, rightNodesBP, BZero]

private theorem rnDom_snoc_of_ge (a : List ℕ) (v : ℕ)
    (hv : 0 < v) (hge : ∀ x ∈ a, v ≤ x) :
    rnDom (a ++ [v]) = .below (v - 1) := by
  induction a with
  | nil => simp [rnDom, Nat.ne_of_gt hv]
  | cons x xs ih =>
      have hx : v ≤ x := hge x (by simp)
      have hxs : ∀ y ∈ xs, v ≤ y := by
        intro y hy
        exact hge y (by simp [hy])
      have hi := ih hxs
      cases htail : xs ++ [v] with
      | nil => simp at htail
      | cons w ws =>
          have hi' : rnDom (w :: ws) = .below (v - 1) := by
            rw [← htail]
            exact hi
          have hnle : ¬x ≤ v - 1 := by omega
          simp [rnDom, htail, hi', hnle]

private theorem getD_snoc_last {α : Type} (xs : List α) (x d : α) :
    (xs ++ [x]).getD ((xs ++ [x]).length - 1) d = x := by
  simp [List.getD_eq_getElem?_getD]

private theorem scb_kind1_spine_bounds (u v : ℕ) (a : List ℕ)
    (hshape :
      let r := (u :: a) ++ [v]
      let j₁ := r.length - 1
      1 ≤ j₁ ∧ r.getD 0 0 < r.getD j₁ 0 ∧
        ∀ j, 0 < j → j < j₁ → r.getD j₁ 0 ≤ r.getD j 0) :
    u < v ∧ ∀ x ∈ a, v ≤ x := by
  let r := (u :: a) ++ [v]
  let j₁ := r.length - 1
  have hs : 1 ≤ j₁ ∧ r.getD 0 0 < r.getD j₁ 0 ∧
      ∀ j, 0 < j → j < j₁ → r.getD j₁ 0 ≤ r.getD j 0 := by
    simpa [r, j₁] using hshape
  have hfirst : r.getD 0 0 = u := by simp [r]
  have hlast : r.getD j₁ 0 = v := by
    simp [r, j₁, List.getD_eq_getElem?_getD]
  constructor
  · rw [hfirst, hlast] at hs
    exact hs.2.1
  · intro x hx
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
    let j := i + 1
    have hjpos : 0 < j := by omega
    have hjlt : j < j₁ := by simp [j, j₁, r] at hi ⊢; omega
    have hjr : j < r.length := by omega
    have hget : r.getD j 0 = a[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjr]
      simpa [r, j] using
        (List.getElem_append_left (bs := [v]) hi)
    have hbound := hs.2.2 j hjpos hjlt
    rw [hlast, hget, hix] at hbound
    exact hbound

/-- Article (2), with only the hypotheses printed in the paper.  The proof
recovers the marked principal body, the strict inequality `u < v`, and its
`T_{v-1}` domain tag from the two nested scb decompositions, then applies the
general A23 tower engine. -/
theorem scb_fseq_kind1 {t c₂ : BT} {u v n : ℕ}
    {s₀ s₁ b₀ b₁ : List Sym}
    (ht : t ∈ T_B)
    (hk1 : scb_kind1 t s₁ (flatBT c₂) b₁)
    (hinner : scb_decomp c₂ (.dsym (u : ℕ∞) :: s₀)
      (flatBT (Dprin (v : ℕ∞) BZero)) b₀) :
    v > u ∧
      flatBT (operB t (numBT n)) =
        s₁ ++ (.dsym (u : ℕ∞) ::
          List.flatten (List.replicate (n + 1)
            (s₀ ++ [.dsym ((v - 1 : ℕ) : ℕ∞)])) ++
          [.zero] ++ List.flatten (List.replicate (n + 1) b₀)) ++ b₁ := by
  have hcflat : flatBT c₂ = .dsym (u : ℕ∞) ::
      (s₀ ++ flatBT (Dprin (v : ℕ∞) BZero) ++ b₀) := by
    rw [hinner.1]
    simp [List.append_assoc]
  obtain ⟨body, hc₂, hbodyflat⟩ := dprin_of_flat_dsym hcflat
  have htne : t ≠ BZero := by
    intro hz
    subst t
    have hlen := congrArg List.length hk1.1.1
    rw [hcflat] at hlen
    simp [BZero, flatBT, Dprin, flatBP] at hlen
    omega
  rcases hk1.1.2.1 htne with ⟨p, hdfp, hpflat⟩
  have hcprincipal : flatBT c₂ = flatBP (.db (u : ℕ∞) body) := by
    rw [hc₂]
    rfl
  have hp : p = .db (u : ℕ∞) body :=
    flatBP_injective (hpflat.symm.trans hcprincipal)
  rw [hp] at hdfp
  have hbodyT : body ∈ T_B := by
    simpa [T_B, dfree_BP] using hdfp
  have hbodyne : body ≠ BZero := by
    intro hz
    subst body
    have hlen := congrArg List.length hbodyflat
    simp [BZero, flatBT, Dprin, flatBP] at hlen
    omega
  have hinnerBody : scb_decomp body s₀
      (flatBT (Dprin (v : ℕ∞) BZero)) b₀ := by
    refine ⟨hbodyflat, ?_, hinner.2.2⟩
    intro _
    exact ⟨.db (v : ℕ∞) BZero, by
      simp [dfree_BP, BZero, dfree_BT, dfree_BPList], rfl⟩
  obtain ⟨a, hrn⟩ :=
    rightNodes_ends_at_marked_zero hbodyflat hinner.2.2
  have hrfull : RightNodes (.trm [.db (u : ℕ∞) body]) =
      (u :: a) ++ [v] := by
    simp [RightNodes, rightNodesList, rightNodesBP, hrn]
  have hshape := hk1.2 (.db (u : ℕ∞) body) hcprincipal
  have hshape' :
      let r := (u :: a) ++ [v]
      let j₁ := r.length - 1
      1 ≤ j₁ ∧ r.getD 0 0 < r.getD j₁ 0 ∧
        ∀ j, 0 < j → j < j₁ → r.getD j₁ 0 ≤ r.getD j 0 := by
    simpa [hrfull] using hshape
  obtain ⟨huv, hge⟩ := scb_kind1_spine_bounds u v a hshape'
  have hv : 0 < v := by omega
  have htagbody : domTag body = .below (v - 1) := by
    rw [domTag_eq_rnDom body hbodyT, hrn]
    exact rnDom_snoc_of_ge a v hv hge
  have hk1body : scb_kind1 t s₁
      (flatBT (Dprin (u : ℕ∞) body)) b₁ := by
    simpa [hc₂] using hk1
  exact scb_fseq_kind1_general ht huv hbodyT htagbody hbodyne
    hinnerBody hk1body

#print axioms scb_fseq_succ
#print axioms scb_fseq_decomp
#print axioms scb_fseq_kind1_general
#print axioms scb_fseq_kind1

end PSS
