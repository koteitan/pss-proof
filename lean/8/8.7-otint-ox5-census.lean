import «8».«8.7-otint-uncond»

/-!
# §8.7 `ox5` census leaf — the census body driver

Discharges the `ox5` hypothesis consumed by the BUILT `«8».«8.7-otint-ox-close»`
(`ox10_SETLE1_close_oc`): the census body driver

  `∀ u, b1x_setle (GBT u A₀) (insert X₁ (GBT u X₁))`,

with `A₀ = bpHeadT (Trans (Pred (s84x_N N)))` and `X₁ = ins 0_B` the census hole
insertion.  Blueprint: the `ox5` chain around `isabelle/layerC/pss_scratch.thy`
:4936–4974 (`ox5_body_driver` + `ox5_body_driver_census`) and the `tri0`
generator `crx_tri0_of_nest`/`cnv_tri0_of_nest` (:2711–3050, = `scbext_triG` lift
of `ot1_triG_grow`).

## What lands here (all `sorry` 0, axioms `[propext, Classical.choice, Quot.sound]`)

The census `tri0`/body-driver reduces, faithful to the Isabelle blueprint, to
PURE Buchholz machinery, all ported here:

- `b1x_triG_addBT_x5` / `b1x_triG_Dpt_x5` — [Buc1] Lemma 3.5 (G-control is a
  congruence for left `+_B` and for `D_v`; Isabelle `b1x_triG_addBT` /
  `b1x_triG_Dpt`, `layerB/pss_wip.thy`:50486/50515).  Re-derived from the PUBLIC
  `sandwich_prefix_bc` / `sandwich_Dprin_bc` (`«Buchholz-1986».«Buchholz-1986-3.3»`),
  since the `triG_add_bc` / `triG_Dprin_bc` twins there are `private`.
- `ot1_triG_grow_x5` — the trivial-base principal growth control
  `b1x_triG z (D_v t₂) (D_v (t₂ +_B c'))` (Isabelle `ot1_triG_grow`, :2765).
- `scbext_triG_x5` — the FIXED-`z` wrapper lift of a principal-level `b1x_triG`
  through a shared right-spine scb context `(s,b)` (Isabelle `scbext_triG`, :2711),
  via the built `OixAlign3_holds` (Isabelle `otx2_align3`) right-spine peel.
- `ox5_body_driver_x5` — the CLEAN piece (Isabelle `ox5_body_driver`, :4936):
  from the `tri0` G-control (at `z = 0_B`) and `base₁ : A₀ < X₁` alone.
- `ox5_census_x5` — the assembly producing the exact `ox5` shape from the census
  wrapper flat data `fA0`/`fX1` (`A₀`, `X₁` share a scb wrapper `(s,b)`, `b`
  all-`RP`, differing only at the hole principal `D_tv t₂` vs `D_tv (t₂ +_B c')`)
  and `base₁`.

## The residual (`needs`, not our own gap)

`ox5_census_x5`'s hypotheses `fA0`/`fX1`/`bRP`/`base1` are the census wrapper
decomposition (`crx_base1_of_nest` / `oi5_IIIIV_pkg`, `pss_scratch.thy`:1213,
2784+) — census geometry that belongs to a separate deep leaf and is supplied by
the transport/nest package, not re-derived here.

private suffix `_x5`.
-/

namespace PSS

/-! ## `GBT` split infrastructure (re-derived; the `«7».«7.1»` twins are private) -/

/-- `gatherBPList` distributes over `++` (Isabelle append lemma). -/
private theorem gatherBPList_append_x5 (u : ℕ∞) (as bs : List BP) :
    gatherBPList u (as ++ bs) = gatherBPList u as ++ gatherBPList u bs := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [gatherBPList, ih, List.append_assoc]

/-- `GBT u (a +_B b) = GBT u a ∪ GBT u b` (Isabelle `m_8_7_GBT_addBT`). -/
private theorem GBT_add_x5 (u : ℕ∞) (a b : BT) :
    GBT u (addBT a b) = GBT u a ∪ GBT u b := by
  rcases a with ⟨as⟩
  rcases b with ⟨bs⟩
  ext x
  simp [GBT, addBT, gatherBT, gatherBPList_append_x5]

/-- `GBT u (D_v b) = if u ≤ v then {b} ∪ GBT u b else ∅`. -/
private theorem GBT_Dprin_x5 (u v : ℕ∞) (b : BT) :
    GBT u (Dprin v b) = if u ≤ v then ({b} ∪ GBT u b) else (∅ : Set BT) := by
  ext x
  by_cases huv : u ≤ v <;>
    simp [GBT, Dprin, gatherBT, gatherBPList, gatherBP, huv]

/-- `GBT u 0_B = ∅`. -/
private theorem GBT_BZero_x5 (u : ℕ∞) : GBT u BZero = (∅ : Set BT) := by
  ext x
  simp [GBT, BZero, gatherBT, gatherBPList]

/-! ## `GBT` transitivity (re-derived; the `«7».«7.1»` twin is private) -/

mutual
  private theorem gatherBT_trans_mem_x5 (u : ℕ∞) (y : BT) :
      ∀ t x : BT, x ∈ gatherBT u t → y ∈ gatherBT u x → y ∈ gatherBT u t
    | .trm ps, x, hx, hy => gatherBPList_trans_mem_x5 u y ps x hx hy

  private theorem gatherBP_trans_mem_x5 (u : ℕ∞) (y : BT) :
      ∀ p : BP, ∀ x : BT, x ∈ gatherBP u p → y ∈ gatherBT u x → y ∈ gatherBP u p
    | .db v b, x, hx, hy => by
        by_cases huv : u ≤ v
        · simp only [gatherBP, huv, decide_true, if_true, List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inr hy
          · exact Or.inr (gatherBT_trans_mem_x5 u y b x hx hy)
        · simp [gatherBP, huv] at hx

  private theorem gatherBPList_trans_mem_x5 (u : ℕ∞) (y : BT) :
      ∀ ps : List BP, ∀ x : BT,
        x ∈ gatherBPList u ps → y ∈ gatherBT u x → y ∈ gatherBPList u ps
    | [], x, hx, _ => by simp [gatherBPList] at hx
    | p :: ps, x, hx, hy => by
        simp only [gatherBPList, List.mem_append] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (gatherBP_trans_mem_x5 u y p x hx hy)
        · exact Or.inr (gatherBPList_trans_mem_x5 u y ps x hx hy)
end

private theorem GBT_trans_x5 {u : ℕ∞} {x t : BT}
    (hx : x ∈ GBT u t) : GBT u x ⊆ GBT u t := by
  intro y hy
  have hout := gatherBT_trans_mem_x5 u y t x
    (by simpa [GBT] using hx) (by simpa [GBT] using hy)
  simpa [GBT] using hout

/-! ## Order facts about `0_B` -/

/-- `lessBT x 0_B = false` (`0_B` is the minimum). -/
private theorem lessBT_BZero_false_x5 (x : BT) : lessBT x BZero = false := by
  rcases x with ⟨xs⟩; cases xs <;> simp [BZero, lessBT, lessBPList]

/-- `0_B < x` whenever `x ≠ 0_B`. -/
private theorem lessBT_BZero_lt_x5 {x : BT} (h : x ≠ BZero) : lessBT BZero x = true := by
  rcases x with ⟨xs⟩
  cases xs with
  | nil => exact absurd rfl h
  | cons a as => simp [BZero, lessBT, lessBPList]

/-- `a +_B 0_B = a`. -/
private theorem addBT_BZero_x5 (t : BT) : addBT t BZero = t := by
  rcases t with ⟨ts⟩; simp [addBT, BZero]

/-! ## [Buc1] Lemma 3.5: `b1x_triG` congruences (Isabelle `b1x_triG_addBT`/`_Dpt`) -/

/-- Isabelle `b1x_triG_addBT` (`layerB/pss_wip.thy`:50486). -/
theorem b1x_triG_addBT_x5 {z b0 b : BT} (ps : List BP) (tri : b1x_triG z b0 b) :
    b1x_triG z (addBT (.trm ps) b0) (addBT (.trm ps) b) := by
  apply b1x_triG_I
  intro u c hlo hhi
  rcases b0 with ⟨bs0⟩
  rcases b with ⟨bs⟩
  obtain ⟨cs, hc, h0c, hcb⟩ := sandwich_prefix_bc ps bs0 bs c
    (by simpa [addBT] using hlo) (by simpa [addBT] using hhi)
  have hprefix : b1x_setle (GBT u (.trm ps)) (GBT u c ∪ GBT u z ∪ {BZero}) := by
    apply b1x_setle_subset
    intro x hx
    have hxc : x ∈ GBT u c := by
      rw [hc, show (.trm (ps ++ cs) : BT) = addBT (.trm ps) (.trm cs) from rfl, GBT_add_x5]
      exact Or.inl hx
    exact Or.inl (Or.inl hxc)
  have htail0 := tri u (.trm cs) h0c hcb
  have htail : b1x_setle (GBT u (.trm bs0)) (GBT u c ∪ GBT u z ∪ {BZero}) := by
    apply b1x_setle_widen htail0
    intro x hx
    rcases hx with (hxc | hxz) | hx0
    · have hxc' : x ∈ GBT u c := by
        rw [hc, show (.trm (ps ++ cs) : BT) = addBT (.trm ps) (.trm cs) from rfl, GBT_add_x5]
        exact Or.inr hxc
      exact Or.inl (Or.inl hxc')
    · exact Or.inl (Or.inr hxz)
    · exact Or.inr hx0
  rw [GBT_add_x5]
  exact b1x_setle_union hprefix htail

#print axioms b1x_triG_addBT_x5

/-- Isabelle `b1x_triG_Dpt` (`layerB/pss_wip.thy`:50515). -/
theorem b1x_triG_Dpt_x5 {z b0 b : BT} (v : ℕ∞) (tri : b1x_triG z b0 b) :
    b1x_triG z (Dprin v b0) (Dprin v b) := by
  apply b1x_triG_I
  intro u c hlo hhi
  obtain ⟨c0, cs, hc, h0c, hcb⟩ := sandwich_Dprin_bc hlo hhi
  by_cases huv : u ≤ v
  · rw [GBT_Dprin_x5, if_pos huv]
    intro x hx
    rcases hx with hx | hx
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨c0, ?_, h0c⟩
      refine Or.inl (Or.inl ?_)
      rw [hc]
      simp [GBT, gatherBT, gatherBPList, gatherBP, huv]
    · obtain ⟨y, hy, hxy⟩ := tri u c0 h0c hcb x hx
      refine ⟨y, ?_, hxy⟩
      rcases hy with (hyc | hyz) | hy0
      · have hc0mem : c0 ∈ GBT u c := by
          rw [hc]
          simp [GBT, gatherBT, gatherBPList, gatherBP, huv]
        exact Or.inl (Or.inl (GBT_trans_x5 hc0mem hyc))
      · exact Or.inl (Or.inr hyz)
      · exact Or.inr hy0
  · rw [GBT_Dprin_x5, if_neg huv]
    intro x hx
    exact hx.elim

#print axioms b1x_triG_Dpt_x5

/-! ## `ot1_triG_grow`: the trivial-base principal growth control -/

/-- Isabelle `ot1_triG_grow` (`layerC/pss_scratch.thy`:2765):
    `b1x_triG z (D_v t₂) (D_v (t₂ +_B c'))`. -/
theorem ot1_triG_grow_x5 {z : BT} (v : ℕ∞) (t2 c' : BT) :
    b1x_triG z (Dprin v t2) (Dprin v (addBT t2 c')) := by
  have base : b1x_triG z BZero c' := by
    apply b1x_triG_I
    intro u c _ _ x hx
    rw [GBT_BZero_x5] at hx
    exact hx.elim
  rcases t2 with ⟨t2s⟩
  have step0 := b1x_triG_addBT_x5 (z := z) t2s base
  rw [addBT_BZero_x5] at step0
  exact b1x_triG_Dpt_x5 (z := z) v step0

#print axioms ot1_triG_grow_x5

/-! ## `scbext_triG`: the shared-wrapper lift of a principal-level `b1x_triG` -/

/-- Isabelle `scbext_triG` (`layerC/pss_scratch.thy`:2711): lift a principal-level
    `b1x_triG` through a shared right-spine scb context `(s,b)` (`b` all-`RP`).
    Right-spine induction via the built `OixAlign3_holds` (Isabelle `otx2_align3`). -/
theorem scbext_triG_x5 {z : BT} {cp cp' : BP}
    (prin : b1x_triG z (.trm [cp]) (.trm [cp'])) :
    ∀ (tLo tHi : BT) (s b : List Sym),
      flatBT tLo = s ++ flatBP cp ++ b →
      flatBT tHi = s ++ flatBP cp' ++ b →
      (∀ x ∈ b, x = Sym.rp) →
      b1x_triG z tLo tHi := by
  intro tLo tHi s b hLo hHi bR
  generalize hn : sizeOf tLo = n
  induction n using Nat.strong_induction_on generalizing tLo tHi s b with
  | _ n ih =>
    rcases OixAlign3_holds tLo tHi tHi s b cp cp' cp' hLo hHi hHi bR with
      ⟨qs, hLoq, hHiq, _⟩ |
      ⟨qs, w, lb1, lb2, lb3, sc, bc, hLoq, hHiq, _hHiq3, F1, F2, _F3, hbc⟩
    · subst hLoq hHiq
      exact b1x_triG_addBT_x5 (z := z) qs (b0 := .trm [cp]) (b := .trm [cp']) prin
    · subst hLoq hHiq
      have hlt : sizeOf lb1 < n := by
        have hmem : (BP.db w lb1) ∈ qs ++ [BP.db w lb1] := by simp
        have h1 := List.sizeOf_lt_of_mem hmem
        rw [← hn]
        simp only [BT.trm.sizeOf_spec, BP.db.sizeOf_spec] at h1 ⊢
        omega
      have ih1 : b1x_triG z lb1 lb2 := ih (sizeOf lb1) hlt lb1 lb2 sc bc F1 F2 hbc rfl
      have hdpt := b1x_triG_Dpt_x5 (z := z) w ih1
      exact b1x_triG_addBT_x5 (z := z) qs (b0 := Dprin w lb1) (b := Dprin w lb2) hdpt

#print axioms scbext_triG_x5

/-! ## `ox5_body_driver`: the clean piece (Isabelle `ox5_body_driver`, :4936) -/

/-- Isabelle `ox5_body_driver` (`layerC/pss_scratch.thy`:4936): every `G_u`-member
    of the hole body `A₀` is `≤` some member of `{X₁} ∪ G_u X₁`.  From the `z = 0_B`
    G-control `tri0` and `base₁ : A₀ < X₁` (`X₁ ≠ 0_B` is derived from `base₁`). -/
theorem ox5_body_driver_x5 {A0 X1 : BT} (u : ℕ∞)
    (tri0 : b1x_triG BZero A0 X1)
    (base1 : lessBT A0 X1 = true) :
    b1x_setle (GBT u A0) (insert X1 (GBT u X1)) := by
  have X1ne : X1 ≠ BZero := by
    intro h
    rw [h, lessBT_BZero_false_x5] at base1
    exact Bool.noConfusion base1
  have leA0X1 : leBT A0 X1 = true := by simp [leBT, base1]
  have leX1X1 : leBT X1 X1 = true := by simp [leBT]
  have step := b1x_triG_D (u := u) tri0 leA0X1 leX1X1
  intro x hx
  obtain ⟨y, hy, hxy⟩ := step x hx
  rcases hy with (hyX1 | hyBZ) | hy0
  · exact ⟨y, Set.mem_insert_iff.mpr (Or.inr hyX1), hxy⟩
  · simp only [GBT_BZero_x5, Set.mem_empty_iff_false] at hyBZ
  · rw [Set.mem_singleton_iff] at hy0
    subst hy0
    have hxy' : (x == BZero) = true := by
      rw [leBT, lessBT_BZero_false_x5] at hxy
      simpa using hxy
    have hxeq : x = BZero := eq_of_beq hxy'
    subst hxeq
    refine ⟨X1, Set.mem_insert _ _, ?_⟩
    have hlt : lessBT BZero X1 = true := lessBT_BZero_lt_x5 X1ne
    simp [leBT, hlt]

#print axioms ox5_body_driver_x5

/-! ## The census assembly: the exact `ox5` shape from the wrapper flat data -/

/-- The census body driver `ox5` (Isabelle `ox5_body_driver_census`,
    `layerC/pss_scratch.thy`:4974), in the shape the built
    `«8».«8.7-otint-ox-close»` (`ox10_SETLE1_close_oc`) consumes.

    Inputs are the census wrapper decomposition: `A₀` and `X₁` share a scb wrapper
    `(s,b)` (`b` all-`RP`), `A₀` carrying the hole principal `D_tv t₂` and `X₁` the
    grown hole principal `D_tv (t₂ +_B c')`, together with `base₁ : A₀ < X₁`.
    These are the `crx_base1_of_nest`/`oi5_IIIIV_pkg` census facts (a separate deep
    leaf — see the module note), not re-derived here.

    The `tri0` is built by lifting `ot1_triG_grow_x5` through the wrapper via
    `scbext_triG_x5`; the setle then follows by `ox5_body_driver_x5`. -/
theorem ox5_census_x5 {A0 X1 : BT} {s b : List Sym} {tv : ℕ∞} {t2 c' : BT}
    (fA0 : flatBT A0 = s ++ flatBP (BP.db tv t2) ++ b)
    (fX1 : flatBT X1 = s ++ flatBP (BP.db tv (addBT t2 c')) ++ b)
    (bRP : ∀ x ∈ b, x = Sym.rp)
    (base1 : lessBT A0 X1 = true) :
    ∀ u : ℕ∞, b1x_setle (GBT u A0) (insert X1 (GBT u X1)) := by
  have tri0 : b1x_triG BZero A0 X1 :=
    scbext_triG_x5 (z := BZero) (cp := BP.db tv t2) (cp' := BP.db tv (addBT t2 c'))
      (ot1_triG_grow_x5 (z := BZero) tv t2 c') A0 X1 s b fA0 fX1 bRP
  intro u
  exact ox5_body_driver_x5 u tri0 base1

#print axioms ox5_census_x5

end PSS
