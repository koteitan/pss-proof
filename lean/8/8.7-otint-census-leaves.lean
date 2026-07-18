import «8».«8.7-otint-setle-assembly»
import «8».«8.7-otint-uncond»

/-!
# PSS.«8».«8.7-otint-census-leaves» — discharging the `otSetleCore` census leaves

The BUILT `«8».«8.7-otint-setle-assembly»` reduces the termination field `otSetleCore`
to the four named leaves via `otSetleCore_of_leaves`:

  `OixCoreTri → A0OTNub → Tri0Census → OTintIIIIV_setleCensus → OTintIIIIV_otSetleCore`.

This file attacks those leaves, largest green subset first.

## `OixCoreTri` — the tri-carrying transport core (Isabelle `otx3_core_tri`, `pss_scratch.thy`:2517)

`OixCoreTri` (`«8».«8.7-otint-a0ot»`) is the **tri0-direct** variant of `oix_transport`
(`«8».«8.7-otint-transport»`): instead of the body-level `setle` premise it takes the
hole-level G-control `tri = b1x_triG (D_∞ aLo) a' aHi` directly.  This is strictly
STRONGER than `oix_transport` (`setle ⟹ tri` but not conversely), so it cannot be
derived from the built `oix_transport` interface; it must be re-derived from the same
machinery.

The built `«8».«8.7-otint-transport»` keeps its `otx3_*` assembly (`core_oix` /
`level_oix` / `pOT_oix` / `triG_lift_oix` and the order/`G` bricks) **private**, so we
re-derive the recursion here with the private suffix `_cl`, feeding `tri` directly in
place of `setle`.  The only difference from `core_oix` is that the leaf case A uses the
given `tri` instead of `setle_triG_oix setle`, and the descent case B carries `tri`
unchanged (the replaced cores `aLo a' aHi` are fixed through the whole recursion).

The four generic Buchholz residuals are discharged from the PUBLIC holders in
`«8».«8.7-otint-uncond»`: `OixAlign3_holds` (Isabelle `otx2_align3`) /
`OixGControl_holds` (`b1x_G_control`, [Buc1] Lemma 3.4, `G_control_bc` twin) /
`OixSandwichPrefix_holds` (`sandwich_prefix_bc`) / `OixSandwichDpt_holds`
(`sandwich_Dprin_bc`).  Hence **`OixCoreTri_holds`** is unconditional.

## Dependencies (built modules only, committed at 44ce106)

- `«8».«8.7-otint-setle-assembly»`: `OixCoreTri` / `A0OTNub` / `Tri0Census` /
  `OTintIIIIV_setleCensus` / `otSetleCore_of_leaves` and (transitively) the residual
  `def`s `OixGControl` / `OixSandwichPrefix` / `OixSandwichDpt` / `OixAlign3`, plus the
  `b1x_*` primitives.
- `«8».«8.7-otint-uncond»`: the PUBLIC residual holders `OixAlign3_holds` /
  `OixGControl_holds` / `OixSandwichPrefix_holds` / `OixSandwichDpt_holds`.

## Status

🤖 GREEN-MODULO (`sorry` 0, axioms = `[propext, Classical.choice, Quot.sound]`).
Private suffix `_cl`.  `OixCoreTri_holds : OixCoreTri` lands unconditionally; the
remaining `otSetleCore` leaves (`Tri0Census`, `A0OTNub`, `OTintIIIIV_setleCensus`) stay
as named residuals.
-/

namespace PSS

/-! ## 1. Pure `BT` order bricks (`otx3_core`'s `otx2_` layer, private twins) -/

private theorem lessBP_irrefl_cl (p : BP) : lessBP p p = false := by
  cases p with
  | db u b => simp [lessBP, lessBT_linear_irrefl]

/-- Isabelle `otx2_lessBT_snocsnoc`. -/
private theorem lessBT_snocsnoc_cl (qs : List BP) (p q : BP) :
    lessBT (BT.trm (qs ++ [p])) (BT.trm (qs ++ [q])) = lessBP p q := by
  induction qs with
  | nil => simp [lessBT, lessBPList]
  | cons a qs' ih =>
    have h1 : lessBP a a = false := lessBP_irrefl_cl a
    have h2 : (a == a) = true := by simp
    simp only [List.cons_append, lessBT, lessBPList, h1, h2, Bool.false_or,
      Bool.true_and]
    simpa [lessBT] using ih

/-- Isabelle `otx2_leBT_snocsnoc`. -/
private theorem leBT_snocsnoc_cl {x y : BT} (w : ℕ∞) (qs : List BP)
    (h : leBT x y = true) :
    leBT (BT.trm (qs ++ [BP.db w x])) (BT.trm (qs ++ [BP.db w y])) = true := by
  by_cases hxy : x = y
  · subst hxy; simp [leBT]
  · have hne_beq : (x == y) = false := by
      simp only [beq_eq_false_iff_ne]; exact hxy
    have hlt : lessBT x y = true := by
      have he : leBT x y = lessBT x y := by simp [leBT, hne_beq]
      rw [he] at h; exact h
    have hlp : lessBP (BP.db w x) (BP.db w y) = true := by
      simp [lessBP, hlt]
    have hlt2 : lessBT (BT.trm (qs ++ [BP.db w x])) (BT.trm (qs ++ [BP.db w y]))
        = true := by rw [lessBT_snocsnoc_cl]; exact hlp
    simp [leBT, hlt2]

/-- Isabelle `otx2_descP_prefix`. -/
private theorem descP_prefix_cl : ∀ (xs ys : List BP),
    descP (xs ++ ys) = true → descP xs = true
  | [], _, _ => by simp [descP]
  | [_], _, _ => by simp [descP]
  | p :: q :: ps, ys, h => by
    have hsplit : leBT (BT.trm [q]) (BT.trm [p]) = true ∧
        descP ((q :: ps) ++ ys) = true := by
      simpa [descP, List.cons_append] using h
    have hIH := descP_prefix_cl (q :: ps) ys hsplit.2
    simp [descP, hsplit.1, hIH]

/-- Isabelle `descP_last_le`. -/
private theorem descP_snoc_last_le_cl : ∀ (qs : List BP) (c : BP) (hne : qs ≠ []),
    descP (qs ++ [c]) = true →
    leBT (BT.trm [c]) (BT.trm [qs.getLast hne]) = true
  | [], _, hne, _ => absurd rfl hne
  | [d], c, _, h => by
    have : leBT (BT.trm [c]) (BT.trm [d]) = true := by
      simpa [descP] using h
    simpa using this
  | d :: e :: es, c, _, h => by
    have hne' : (e :: es) ≠ [] := by simp
    have hsplit : leBT (BT.trm [e]) (BT.trm [d]) = true ∧
        descP ((e :: es) ++ [c]) = true := by
      simpa [descP, List.cons_append] using h
    have hIH := descP_snoc_last_le_cl (e :: es) c hne' hsplit.2
    have hlast : (d :: e :: es).getLast (by simp) = (e :: es).getLast hne' := by
      simp [List.getLast_cons]
    rw [hlast]; exact hIH

private theorem gatherBPList_append_cl (u : ℕ∞) (xs ys : List BP) :
    gatherBPList u (xs ++ ys) = gatherBPList u xs ++ gatherBPList u ys := by
  induction xs with
  | nil => simp [gatherBPList]
  | cons a as ih => simp [gatherBPList, ih, List.append_assoc]

/-- Isabelle `otx2_GBT_snoc`. -/
private theorem GBT_snoc_cl (u : ℕ∞) (qs : List BP) (p : BP) :
    GBT u (BT.trm (qs ++ [p])) = GBT u (BT.trm qs) ∪ GBP u p := by
  ext x
  simp only [GBT, GBP, gatherBT, gatherBPList_append_cl, gatherBPList,
    List.append_nil, List.contains_append, Set.mem_setOf_eq, Set.mem_union,
    Bool.or_eq_true]

/-- Isabelle `otx2_GBP_inf` (`GBT` form). -/
private theorem GBT_Dprin_inf_cl (u : ℕ∞) (x : BT) :
    GBT u (Dprin (⊤ : ℕ∞) x) = insert x (GBT u x) := by
  ext y
  simp only [GBT, Dprin, gatherBT, gatherBPList, gatherBP, le_top,
    decide_true, if_true, List.append_nil, List.contains_cons, Set.mem_setOf_eq,
    Set.mem_insert_iff, Bool.or_eq_true, beq_iff_eq]

/-! ## 2. Order / `G` helpers -/

private theorem leBT_iff_cl (a b : BT) :
    leBT a b = true ↔ (lessBT a b = true ∨ a = b) := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq]

private theorem leBT_refl_cl (x : BT) : leBT x x = true := by simp [leBT]

private theorem leBT_trans_cl {a b c : BT}
    (h1 : leBT a b = true) (h2 : leBT b c = true) : leBT a c = true := by
  rw [leBT_iff_cl] at h1 h2 ⊢
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (lessBT_linear_trans a b c h1 h2)
  · subst h2; exact Or.inl h1
  · subst h1; exact Or.inl h2
  · subst h1; subst h2; exact Or.inr rfl

private theorem less_le_trans_cl {a b c : BT}
    (hab : lessBT a b = true) (hbc : leBT b c = true) : lessBT a c = true := by
  rw [leBT_iff_cl] at hbc
  rcases hbc with h | h
  · exact lessBT_linear_trans a b c hab h
  · subst h; exact hab

private theorem GBT_lessBT_of_isOT_BP_cl {w : ℕ∞} {b : BT}
    (h : isOT_BP (BP.db w b) = true) : ∀ x ∈ GBT w b, lessBT x b = true := by
  intro x hx
  simp only [isOT_BP, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 x (by simpa [GBT, List.contains_iff_mem] using hx)

private theorem GBP_db_le_cl {u w : ℕ∞} (x : BT) (h : u ≤ w) :
    GBP u (BP.db w x) = insert x (GBT u x) := by
  have hd : decide (u ≤ w) = true := decide_eq_true h
  ext y
  simp only [GBP, GBT, gatherBP, hd, if_true, Set.mem_setOf_eq,
    List.contains_iff_mem, List.mem_cons, Set.mem_insert_iff]

private theorem GBP_db_not_le_cl {u w : ℕ∞} (x : BT) (h : ¬ u ≤ w) :
    GBP u (BP.db w x) = ∅ := by
  have hd : decide (u ≤ w) = false := decide_eq_false h
  ext y
  simp only [GBP, gatherBP, hd, if_false, Set.mem_setOf_eq,
    List.contains_nil, Set.mem_empty_iff_false, Bool.false_eq_true]

private theorem GBP_subset_GBT_mem_cl {u : ℕ∞} {p : BP} :
    ∀ (ps : List BP), p ∈ ps → GBP u p ⊆ GBT u (BT.trm ps)
  | q :: qs, hmem => by
    intro x hx
    simp only [List.mem_cons] at hmem
    simp only [GBT, GBP, gatherBT, gatherBPList, Set.mem_setOf_eq,
      List.contains_append, Bool.or_eq_true] at hx ⊢
    rcases hmem with hmem | hmem
    · subst hmem; exact Or.inl hx
    · have hsub := GBP_subset_GBT_mem_cl (u := u) (p := p) qs hmem
      have hx2 : x ∈ GBT u (BT.trm qs) := hsub hx
      simp only [GBT, gatherBT, Set.mem_setOf_eq] at hx2
      exact Or.inr hx2

/-! ## 3. per-level principal guard: `otx3_pOT` -/

/-- Isabelle `otx3_pOT`. -/
private theorem pOT_cl (hGC : OixGControl)
    {w : ℕ∞} {xLo x' xHi : BT}
    (loP : isOT_BP (BP.db w xLo) = true) (hiP : isOT_BP (BP.db w xHi) = true)
    (xOT : isOT_BT x' = true)
    (o1 : leBT xLo x' = true) (o2 : leBT x' xHi = true)
    (tri : b1x_triG (Dprin (⊤ : ℕ∞) xLo) x' xHi) :
    isOT_BP (BP.db w x') = true := by
  by_cases hx' : x' = xLo
  · subst hx'; exact loP
  · have lo_lt : lessBT xLo x' = true := by
      rw [leBT_iff_cl] at o1
      rcases o1 with h | h
      · exact h
      · exact absurd h.symm hx'
    have GLo : ∀ y ∈ GBT w xLo, lessBT y xLo = true := GBT_lessBT_of_isOT_BP_cl loP
    have Ga : ∀ x ∈ GBT w xHi, lessBT x xHi = true := GBT_lessBT_of_isOT_BP_cl hiP
    have Gz : ∀ x ∈ GBT w (Dprin (⊤ : ℕ∞) xLo), lessBT x x' = true := by
      intro x hx
      rw [GBT_Dprin_inf_cl, Set.mem_insert_iff] at hx
      rcases hx with hx | hx
      · subst hx; exact lo_lt
      · exact less_le_trans_cl (GLo x hx) o1
    have G : ∀ x ∈ GBT w x', lessBT x x' = true :=
      hGC (Dprin (⊤ : ℕ∞) xLo) x' xHi w tri o2 Ga Gz
    simp only [isOT_BP, Bool.and_eq_true, List.all_eq_true]
    refine ⟨xOT, ?_⟩
    intro x hx
    exact G x (by simpa [GBT, List.contains_iff_mem] using hx)

/-! ## 4. `◁` level lift: `otx3_triG_lift` -/

/-- Isabelle `otx3_triG_lift`. -/
private theorem triG_lift_cl (hSP : OixSandwichPrefix) (hSD : OixSandwichDpt)
    {w : ℕ∞} {xLo x' xHi : BT} (qs : List BP)
    (tri : b1x_triG (Dprin (⊤ : ℕ∞) xLo) x' xHi) :
    b1x_triG (Dprin (⊤ : ℕ∞) (BT.trm (qs ++ [BP.db w xLo])))
      (BT.trm (qs ++ [BP.db w x'])) (BT.trm (qs ++ [BP.db w xHi])) := by
  apply b1x_triG_I
  intro u c l1 l2
  obtain ⟨cs, ceq, s1, s2⟩ := hSP qs [BP.db w x'] [BP.db w xHi] c l1 l2
  obtain ⟨c0, c1, cseq, xc0, c0hi⟩ :=
    hSD (v := w) (x := x') (y := xHi) (c := BT.trm cs)
      (show leBT (Dprin w x') (BT.trm cs) = true from s1)
      (show leBT (BT.trm cs) (Dprin w xHi) = true from s2)
  have cse : cs = BP.db w c0 :: c1 := by injection cseq
  have snocLo : GBT u (BT.trm (qs ++ [BP.db w xLo]))
      = GBT u (BT.trm qs) ∪ GBP u (BP.db w xLo) := GBT_snoc_cl u qs (BP.db w xLo)
  have snocX : GBT u (BT.trm (qs ++ [BP.db w x']))
      = GBT u (BT.trm qs) ∪ GBP u (BP.db w x') := GBT_snoc_cl u qs (BP.db w x')
  have tLoZ : GBT u (BT.trm (qs ++ [BP.db w xLo]))
      ⊆ GBT u (Dprin (⊤ : ℕ∞) (BT.trm (qs ++ [BP.db w xLo]))) := by
    rw [GBT_Dprin_inf_cl]; exact Set.subset_insert _ _
  have part1 : b1x_setle (GBT u (BT.trm qs))
      (GBT u c ∪ GBT u (Dprin (⊤ : ℕ∞) (BT.trm (qs ++ [BP.db w xLo]))) ∪ {BZero}) := by
    apply b1x_setle_subset
    intro z hz
    have h1 : z ∈ GBT u (BT.trm (qs ++ [BP.db w xLo])) := by
      rw [snocLo]; exact Or.inl hz
    exact Or.inl (Or.inr (tLoZ h1))
  have part2 : b1x_setle (GBP u (BP.db w x'))
      (GBT u c ∪ GBT u (Dprin (⊤ : ℕ∞) (BT.trm (qs ++ [BP.db w xLo]))) ∪ {BZero}) := by
    by_cases hle : u ≤ w
    · have hmem : BP.db w c0 ∈ qs ++ cs := by
        rw [cse]; simp
      have hc0GBP : c0 ∈ GBP u (BP.db w c0) := by
        rw [GBP_db_le_cl c0 hle]; exact Set.mem_insert _ _
      have hGBPsub : GBP u (BP.db w c0) ⊆ GBT u c := by
        rw [ceq]; exact GBP_subset_GBT_mem_cl (u := u) (p := BP.db w c0) (qs ++ cs) hmem
      have c0in : c0 ∈ GBT u c := hGBPsub hc0GBP
      have Gc0sub : GBT u c0 ⊆ GBT u c := by
        have hins : GBT u c0 ⊆ GBP u (BP.db w c0) := by
          rw [GBP_db_le_cl c0 hle]; exact Set.subset_insert _ _
        exact hins.trans hGBPsub
      have hmemLo : BP.db w xLo ∈ qs ++ [BP.db w xLo] := by simp
      have sub2 : GBT u (Dprin (⊤ : ℕ∞) xLo)
          ⊆ GBT u (Dprin (⊤ : ℕ∞) (BT.trm (qs ++ [BP.db w xLo]))) := by
        have heq : GBT u (Dprin (⊤ : ℕ∞) xLo) = GBP u (BP.db w xLo) := by
          rw [GBT_Dprin_inf_cl, GBP_db_le_cl xLo hle]
        rw [heq]
        exact (GBP_subset_GBT_mem_cl (u := u) (p := BP.db w xLo)
          (qs ++ [BP.db w xLo]) hmemLo).trans tLoZ
      have deep : b1x_setle (GBT u x')
          (GBT u c0 ∪ GBT u (Dprin (⊤ : ℕ∞) xLo) ∪ {BZero}) :=
        b1x_triG_D (u := u) tri xc0 c0hi
      have hZsub : GBT u c0 ∪ GBT u (Dprin (⊤ : ℕ∞) xLo) ∪ {BZero}
          ⊆ GBT u c ∪ GBT u (Dprin (⊤ : ℕ∞) (BT.trm (qs ++ [BP.db w xLo]))) ∪ {BZero} := by
        intro z hz
        rcases hz with (hz | hz) | hz
        · exact Or.inl (Or.inl (Gc0sub hz))
        · exact Or.inl (Or.inr (sub2 hz))
        · exact Or.inr hz
      have deep' := b1x_setle_widen deep hZsub
      rw [GBP_db_le_cl x' hle]
      intro z hz
      rw [Set.mem_insert_iff] at hz
      rcases hz with hz | hz
      · subst hz
        exact ⟨c0, Or.inl (Or.inl c0in), xc0⟩
      · exact deep' z hz
    · rw [GBP_db_not_le_cl x' hle]
      intro z hz
      simp only [Set.mem_empty_iff_false] at hz
  rw [snocX]
  exact b1x_setle_union part1 part2

/-! ## 5. `isOT_BT` snoc lemmas (`m_8_7_isOT_BT_snoc_leBT`) -/

private theorem isOT_BPList_snoc_cl (xs : List BP) (pn : BP) :
    isOT_BPList (xs ++ [pn]) = (isOT_BPList xs && isOT_BP pn) := by
  induction xs with
  | nil => simp [isOT_BPList]
  | cons p ps ih => simp [isOT_BPList, ih, Bool.and_assoc]

private theorem descP_snoc_cl : ∀ (xs : List BP) (pn : BP),
    descP xs = true →
    (∀ (h : xs ≠ []), leBT (BT.trm [pn]) (BT.trm [xs.getLast h]) = true) →
    descP (xs ++ [pn]) = true
  | [], _, _, _ => by simp [descP]
  | [d], pn, _, hle => by
    have hd : leBT (BT.trm [pn]) (BT.trm [d]) = true := by
      have := hle (by simp); simpa using this
    simp [descP, hd]
  | d :: e :: es, pn, hd, hle => by
    have hsplit : leBT (BT.trm [e]) (BT.trm [d]) = true ∧ descP (e :: es) = true := by
      simpa [descP] using hd
    have hle' : ∀ (h : (e :: es) ≠ []),
        leBT (BT.trm [pn]) (BT.trm [(e :: es).getLast h]) = true := by
      intro h
      have hne : (d :: e :: es) ≠ [] := by simp
      have hg : (d :: e :: es).getLast hne = (e :: es).getLast h := by
        simp [List.getLast_cons]
      have := hle hne; rwa [hg] at this
    have hIH := descP_snoc_cl (e :: es) pn hsplit.2 hle'
    have hrw : (d :: e :: es) ++ [pn] = d :: e :: (es ++ [pn]) := by simp
    rw [hrw]
    have hIH' : descP (e :: (es ++ [pn])) = true := by
      have hcast : e :: (es ++ [pn]) = (e :: es) ++ [pn] := by simp
      rw [hcast]; exact hIH
    show (leBT (BT.trm [e]) (BT.trm [d]) && descP (e :: (es ++ [pn]))) = true
    simp only [hsplit.1, hIH', Bool.and_self]

/-- Isabelle `m_8_7_isOT_BT_snoc_leBT`. -/
private theorem isOT_snoc_leBT_cl (xs : List BP) (pn : BP)
    (hxs : isOT_BT (BT.trm xs) = true) (hpn : isOT_BP pn = true)
    (hle : ∀ (h : xs ≠ []), leBT (BT.trm [pn]) (BT.trm [xs.getLast h]) = true) :
    isOT_BT (BT.trm (xs ++ [pn])) = true := by
  have hsp : isOT_BPList xs = true ∧ descP xs = true := by
    simpa [isOT_BT, Bool.and_eq_true] using hxs
  simp only [isOT_BT, Bool.and_eq_true]
  refine ⟨?_, descP_snoc_cl xs pn hsp.2 hle⟩
  simp only [isOT_BPList_snoc_cl, hsp.1, hpn, Bool.and_self]

private theorem isOT_BT_of_isOT_BP_cl {w : ℕ∞} {b : BT}
    (h : isOT_BP (BP.db w b) = true) : isOT_BT b = true := by
  simp only [isOT_BP, Bool.and_eq_true] at h; exact h.1

private theorem isOT_BP_last_of_snoc_cl {qs : List BP} {w : ℕ∞} {lb : BT}
    (h : isOT_BT (BT.trm (qs ++ [BP.db w lb])) = true) : isOT_BP (BP.db w lb) = true := by
  simp only [isOT_BT, isOT_BPList_snoc_cl, Bool.and_eq_true] at h
  exact h.1.2

/-! ## 6. measure: `btWeight` snoc monotonicity -/

private theorem bpListWeight_snoc_cl (qs : List BP) (p : BP) :
    bpListWeight (qs ++ [p]) = bpListWeight qs + bpWeight p + 1 := by
  induction qs with
  | nil => simp [bpListWeight]
  | cons q qs' ih => simp only [List.cons_append, bpListWeight, ih]; omega

private theorem btWeight_lt_snoc_cl (qs : List BP) (w : ℕ∞) (lb : BT) :
    btWeight lb < btWeight (BT.trm (qs ++ [BP.db w lb])) := by
  simp only [btWeight, bpListWeight_snoc_cl, bpWeight]
  omega

/-! ## 7. one level assembly: `otx3_level` -/

/-- Isabelle `otx3_level`. -/
private theorem level_cl (hSP : OixSandwichPrefix)
    (hSD : OixSandwichDpt) {w : ℕ∞} {xLo x' xHi : BT} (qs : List BP)
    (LoOT : isOT_BT (BT.trm (qs ++ [BP.db w xLo])) = true)
    (HiOT : isOT_BT (BT.trm (qs ++ [BP.db w xHi])) = true)
    (pOT : isOT_BP (BP.db w x') = true)
    (o1 : leBT xLo x' = true) (o2 : leBT x' xHi = true)
    (tri : b1x_triG (Dprin (⊤ : ℕ∞) xLo) x' xHi) :
    isOT_BT (BT.trm (qs ++ [BP.db w x'])) = true ∧
    leBT (BT.trm (qs ++ [BP.db w xLo])) (BT.trm (qs ++ [BP.db w x'])) = true ∧
    leBT (BT.trm (qs ++ [BP.db w x'])) (BT.trm (qs ++ [BP.db w xHi])) = true ∧
    b1x_triG (Dprin (⊤ : ℕ∞) (BT.trm (qs ++ [BP.db w xLo])))
      (BT.trm (qs ++ [BP.db w x'])) (BT.trm (qs ++ [BP.db w xHi])) := by
  have descLo : descP (qs ++ [BP.db w xLo]) = true := by
    have := LoOT; simp only [isOT_BT, Bool.and_eq_true] at this; exact this.2
  have qsBP : isOT_BPList qs = true := by
    have h1 : isOT_BPList (qs ++ [BP.db w xLo]) = true := by
      have := LoOT; simp only [isOT_BT, Bool.and_eq_true] at this; exact this.1
    rw [isOT_BPList_snoc_cl, Bool.and_eq_true] at h1
    exact h1.1
  have qsD : descP qs = true := descP_prefix_cl qs [BP.db w xLo] descLo
  have qsOT : isOT_BT (BT.trm qs) = true := by
    simp only [isOT_BT, Bool.and_eq_true]; exact ⟨qsBP, qsD⟩
  have lelast : ∀ (hne : qs ≠ []),
      leBT (BT.trm [BP.db w x']) (BT.trm [qs.getLast hne]) = true := by
    intro hne
    have descHi : descP (qs ++ [BP.db w xHi]) = true := by
      have := HiOT; simp only [isOT_BT, Bool.and_eq_true] at this; exact this.2
    have hi_last : leBT (BT.trm [BP.db w xHi]) (BT.trm [qs.getLast hne]) = true :=
      descP_snoc_last_le_cl qs (BP.db w xHi) hne descHi
    have mid : leBT (BT.trm [BP.db w x']) (BT.trm [BP.db w xHi]) = true := by
      have := leBT_snocsnoc_cl (x := x') (y := xHi) w [] o2; simpa using this
    exact leBT_trans_cl mid hi_last
  have OT : isOT_BT (BT.trm (qs ++ [BP.db w x'])) = true :=
    isOT_snoc_leBT_cl qs (BP.db w x') qsOT pOT lelast
  have le1 := leBT_snocsnoc_cl (x := xLo) (y := x') w qs o1
  have le2 := leBT_snocsnoc_cl (x := x') (y := xHi) w qs o2
  have triL := triG_lift_cl hSP hSD (w := w) qs tri
  exact ⟨OT, le1, le2, triL⟩

/-! ## 8. context recursion: `otx3_core_tri` -/

/-- Isabelle `otx3_core_tri` (`pss_scratch.thy`:2517): the tri-carrying context
recursion.  Identical to the built `core_oix` except that the leaf case A consumes the
given `tri` directly (there is no `setle_triG_oix` step) and case B carries `tri`
unchanged. -/
private theorem core_tri_cl (hAlign : OixAlign3) (hGC : OixGControl)
    (hSP : OixSandwichPrefix) (hSD : OixSandwichDpt) :
    ∀ (n : ℕ) (t' tLo tHi : BT) (s b : List Sym) (h : ℕ) (aLo a' aHi : BT),
      btWeight t' = n →
      flatBT tLo = s ++ flatBP (BP.db (h : ℕ∞) aLo) ++ b →
      flatBT t' = s ++ flatBP (BP.db (h : ℕ∞) a') ++ b →
      flatBT tHi = s ++ flatBP (BP.db (h : ℕ∞) aHi) ++ b →
      (∀ x ∈ b, x = Sym.rp) →
      isOT_BT tLo = true → isOT_BT tHi = true →
      isOT_BP (BP.db (h : ℕ∞) a') = true →
      leBT aLo a' = true → leBT a' aHi = true →
      b1x_triG (Dprin (⊤ : ℕ∞) aLo) a' aHi →
      isOT_BT t' = true ∧ leBT tLo t' = true ∧ leBT t' tHi = true ∧
        b1x_triG (Dprin (⊤ : ℕ∞) tLo) t' tHi := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t' tLo tHi s b h aLo a' aHi hn F1 F2 F3 BR loOT hiOT newOT o1 o2 tri
    rcases hAlign tLo t' tHi s b (BP.db (h : ℕ∞) aLo) (BP.db (h : ℕ∞) a')
        (BP.db (h : ℕ∞) aHi) F1 F2 F3 BR with
      ⟨qs, hTLo, hT', hTHi⟩ |
      ⟨qs, w, lbLo, lb', lbHi, sc, bc, hTLo, hT', hTHi, F1', F2', F3', BC⟩
    · -- case A: the cores are the last top-level components over a shared `qs`
      subst hTLo; subst hT'; subst hTHi
      exact level_cl hSP hSD qs loOT hiOT newOT o1 o2 tri
    · -- case B: descend through a shared last component into aligned bodies
      subst hTLo; subst hT'; subst hTHi
      have loP : isOT_BP (BP.db w lbLo) = true := isOT_BP_last_of_snoc_cl loOT
      have hiP : isOT_BP (BP.db w lbHi) = true := isOT_BP_last_of_snoc_cl hiOT
      have loBT : isOT_BT lbLo = true := isOT_BT_of_isOT_BP_cl loP
      have hiBT : isOT_BT lbHi = true := isOT_BT_of_isOT_BP_cl hiP
      have sz : btWeight lb' < n := by
        rw [← hn]; exact btWeight_lt_snoc_cl qs w lb'
      obtain ⟨ih1, ih2, ih3, ih4⟩ :=
        ih (btWeight lb') sz lb' lbLo lbHi sc bc h aLo a' aHi rfl F1' F2' F3' BC
          loBT hiBT newOT o1 o2 tri
      have pOT : isOT_BP (BP.db w lb') = true := pOT_cl hGC loP hiP ih1 ih2 ih3 ih4
      exact level_cl hSP hSD qs loOT hiOT pOT ih2 ih3 ih4

/-! ## 9. `OixCoreTri` discharge -/

/-- **`OixCoreTri` (Isabelle `otx3_core_tri`).**  The tri-carrying transport core,
discharged unconditionally by feeding the PUBLIC residual holders of
`«8».«8.7-otint-uncond»` into the re-derived recursion. -/
theorem OixCoreTri_holds : OixCoreTri := by
  intro tLo t' tHi s b h aLo a' aHi F1 F2 F3 BR loOT hiOT newOT o1 o2 tri
  exact (core_tri_cl OixAlign3_holds OixGControl_holds OixSandwichPrefix_holds
    OixSandwichDpt_holds (btWeight t') t' tLo tHi s b h aLo a' aHi rfl
    F1 F2 F3 BR loOT hiOT newOT o1 o2 tri).1

#print axioms OixCoreTri_holds

/-! ## 10. field reduction: one census leaf closed

Since `OixCoreTri` is now unconditional, the termination field `OTintIIIIV_otSetleCore`
(`«8».«8.7-otint-setle-assembly»`) reduces from FOUR named leaves to the THREE remaining
deep census leaves — `A0OTNub` (Isabelle `ot1_A0OT`, `pss_scratch.thy`:4762, §6 Red/slice),
`Tri0Census` (`ot1_tri0_census`, :4081, condIII/IV mnform CRUX), and
`OTintIIIIV_setleCensus` (the oi5 pkg facts `0 < v₁` / wrapper existence + the open surgery
gap `SpineSurgeryTransport_kk`).  Each of these is stated over the census-mapped hypothesis
bundle and needs the concrete provenance (`A₀ = bpHeadT(Trans(Pred(s84x_N N)))`,
`v₁ = entry N 1 (Lng N − 1)`, …) that is deliberately absent from the abstract interface,
so none is derivable here without the deeper §8.4 producer / §6 Red machinery. -/

/-- **Field reduction (one leaf closed).**  `OTintIIIIV_otSetleCore` reduces to the three
remaining census leaves, with `OixCoreTri` discharged unconditionally by
`OixCoreTri_holds`. -/
theorem otSetleCore_of_3leaves (hnub : A0OTNub) (htri0 : Tri0Census)
    (hc : OTintIIIIV_setleCensus) : OTintIIIIV_otSetleCore :=
  otSetleCore_of_leaves OixCoreTri_holds hnub htri0 hc

#print axioms otSetleCore_of_3leaves

end PSS
