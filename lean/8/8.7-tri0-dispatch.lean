import «8».«8.7-otint-tri0-census»
import «8».«8.7-otint-ox5-census»
import «8».«8.7-census-provenance»
import «8».«8.4-base-legs»
import «8».«8.4-exch84-base1p»
import «7».«7.2-add-scb»

/-!
# PSS.«8».«8.7-tri0-dispatch» — `Tri0CruxConcrete` UNCONDITIONAL (ltJ/corner re-dispatch)

The BUILT `«8».«8.7-tri0-spine» proved `tri0CruxConcrete_of_pkg_ts : Exch84_scbDecompPkg
→ Cnv_c2_shape_condIV → Cnv_nested_hole_pair → Tri0CruxConcrete`, but its first hypothesis
`Exch84_scbDecompPkg` is **globally REFUTED** (`Exch84_scbDecompPkg_refuted_sp2`,
`«8».«8.4-scbdecomp-pkg»`): the bare package requires the degenerate `dP` decomposition
`scb_decomp (Trans (Pred (s84x_N M))) (Dsym e₃ :: u1) (flatBT (transC1 M)) v1` which is
false at the condIV admeq corner (there `Trans (Pred (s84x_N M)) = transC1 M`, so the
non-empty left context is a length contradiction).

This file re-dispatches `Tri0CruxConcrete` over `ltJ_or_IVadmeq_sp`, mirroring the
`«8».«8.4-base-legs»` Base-leg re-dispatch, and lands it **unconditionally**:

## ltJ branch (`s84x_jm3 M < transJm1 M`)

The unconditional ltJ package `exch84ScbDecompPkgLtJ_holds_sp2` (`«8».«8.4-scbdecomp-pkg»`)
supplies `hT1`/`dP`/`d2`/`d4c2`, which feed the existing `«8».«8.7-tri0-spine»` `tri0`
machinery (`crx_tri0` for condIII, `cnv_tri0` for condIV).  That machinery's private helpers
are re-derived here with suffix `_td2`.  The condIV leg additionally consumes the
unconditional `Cnv_c2_shape_condIV_holds` / `Cnv_nested_hole_pair_holds`
(`«8».«8.4-exch84-scbdecomp»`).

## corner branch (condIV ∧ `Adm M (s84x_jm2 M) = transJm1 M`)

At the admeq corner the collapse identities `cornerCollapse_holds_cr`
(`«8».«8.4-corner-redesign»`) give `Trans (Pred (s84x_N M)) = transC1 M` and
`Trans (s84x_N M) = transC2 M`.  So the `tri0` goal head `bpHeadT (Trans (Pred (s84x_N M)))`
collapses to `bpHeadT (transC1 M) = transT2 M` (bare, no wrapper), and the census
`inner`/`hflat` pin `ins 0_B = t₃ +_B D_w (t₄ +_B D_{v₁-1} 0_B)` via the condIV
nested-hole surgery pair (`Cnv_nested_hole_pair_holds`) plus scb uniqueness.  The corner
`tri0` `b1x_triG (D_∞ 0_B) (transT2 M) (t₃ +_B D_w (t₄ +_B D_{v₁-1} 0_B))` is then EXACTLY
the inner growth of the condIV dichotomy — the same `ot1_triG_add`/`b1x_triG_Dpt`/
`b1x_triG_addBT` cascade `cnv_tri0` uses BEFORE the `scbext_triG` wrapper lift (which the
corner does not need, `A₀` being bare).  So the corner `tri0` closes directly, no residual.

## What lands (green, `sorry` 0)

* `tri0CruxConcrete_holds : Tri0CruxConcrete` — **unconditional** (both branches close).
* `otSetleCore_of_remaining_td2 : A0OTNub → SetleCensusSpine → SetleCensusWrapperCondIV_cp
  → OTintIIIIV_otSetleCore` — composes `«8».«8.7-census-provenance»`'s
  `otSetleCore_of_parts_cp` with the now-unconditional `tri0CruxConcrete_holds`
  (and the fully-discharged `CensusProvenance`), so the `otSetleCore` field's remaining
  parts are exactly `{A0OTNub, SetleCensusSpine, SetleCensusWrapperCondIV_cp}` — the
  `Tri0CruxConcrete` residual is removed.

## Dependencies (built modules only, committed at b2a4380)

- `«8».«8.7-otint-tri0-census»`: `Tri0CruxConcrete`.
- `«8».«8.7-otint-ox5-census»`: `scbext_triG_x5` / `ot1_triG_grow_x5` /
  `b1x_triG_addBT_x5` / `b1x_triG_Dpt_x5`.
- `«8».«8.4-base-legs»` (transitively): `exch84ScbDecompPkgLtJ_holds_sp2` /
  `ltJ_or_IVadmeq_sp` / `cornerCollapse_holds_cr` / `Cnv_c2_shape_condIV_holds` /
  `Cnv_nested_hole_pair_holds` / `c1_shape_holds` / `scb_unique_decomp_unconditional` /
  `add_scb_marked` / `add_scb_replace_last` / `unflatBT_flat` / `STPS_RTPS` / `RTPS_TPS` /
  `RTPS_Pred` / `Trans_Mark_invariant`.
- `«8».«8.4-exch84-base1p»`: `Cnv_c2_shape_condIV` / `Cnv_nested_hole_pair`.
- `«7».«7.2-add-scb»`: `add_scb_marked` / `add_scb_replace_last`.
- `«8».«8.7-census-provenance»`: `otSetleCore_of_parts_cp` / `SetleCensusWrapperCondIV_cp`
  (and re-exports `A0OTNub` / `SetleCensusSpine` / `OTintIIIIV_otSetleCore`).

## Status
🤖 GREEN (`sorry` 0, axioms = `[propext, Classical.choice, Quot.sound]`).
Private helper suffix `_td2`.
-/

namespace PSS

/-! ## 0. Re-derived private helpers (the `«8».«8.7-tri0-spine»` twins are `private`) -/

/-- condIII c2 shape (Isabelle `crx_c2_shape_condIII`, layerB/pss_wip.thy:88353). -/
private theorem crx_c2_shape_condIII_td2 (M : PS) (hcIII : transCondIII M = true) :
    transC2 M = Dprin (transV M)
      (addBT (transT2 M) (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) := by
  unfold transC2 transC2Core
  simp only [hcIII, Bool.or_eq_true, or_true, true_or, if_true]
  rfl

/-- `D_v 0_B ∈ T_B` (`v` a finite index). -/
private theorem Dprin_nat_mem_T_B_td2 (n : ℕ) : Dprin (n : ℕ∞) BZero ∈ T_B := by
  simp [T_B, Dprin, dfree_BT, dfree_BPList, dfree_BP, BZero]

/-- A single-principal `T_B` term flattens to an `isPTB_str` string. -/
private theorem isPTB_str_princ_td2 {c : BT} (hc : c ∈ T_B) (hcP : ∃ p, c = BT.trm [p]) :
    isPTB_str (flatBT c) := by
  obtain ⟨p, rfl⟩ := hcP
  refine ⟨p, ?_, by simp [flatBT]⟩
  simpa [T_B, dfree_BT, dfree_BPList] using hc

/-- Isabelle `scb_Dpt_lift` (layerB/pss_wip.thy:1663): wrapping `D_v` adds one
`Dsym v` to the left context of a scb decomposition. -/
private theorem scb_Dprin_lift_td2 {X : BT} {s c b : List Sym} (v : ℕ∞)
    (d : scb_decomp X s c b) (ipt : isPTB_str c) :
    scb_decomp (Dprin v X) ((.dsym v) :: s) c b := by
  obtain ⟨he, _, hrp⟩ := d
  refine ⟨?_, fun _ => ipt, hrp⟩
  have hflat : flatBT (Dprin v X) = (.dsym v) :: flatBT X := by
    simp [Dprin, flatBT, flatBP]
  rw [hflat, he]; simp

/-- Isabelle `vf2x_flat_head_bpHeadT` (layerB/pss_wip.thy:69403): if
`flatBT t = Dsym v # rest` then `flatBT (bpHeadT t) = rest`. -/
private theorem flat_head_bpHeadT_td2 {t : BT} {v : ℕ∞} {rest : List Sym}
    (h : flatBT t = Sym.dsym v :: rest) : flatBT (bpHeadT t) = rest := by
  obtain ⟨xs⟩ := t
  match xs with
  | [] => simp [flatBT] at h
  | [.db u a] =>
      simp only [flatBT, flatBP, List.cons.injEq] at h
      simp only [bpHeadT]; exact h.2
  | .db u a :: .db u2 a2 :: qs =>
      simp only [flatBT, List.cons_append, List.cons.injEq, reduceCtorEq, false_and] at h

/-- `a +_B 0_B = a`. -/
private theorem addBT_BZero_td2 (t : BT) : addBT t BZero = t := by
  rcases t with ⟨ts⟩; simp [addBT, BZero]

/-- `GBT u 0_B = ∅`. -/
private theorem GBT_BZero_td2 (u : ℕ∞) : GBT u BZero = (∅ : Set BT) := by
  ext x
  simp [GBT, BZero, gatherBT, gatherBPList]

/-- Isabelle `ot1_triG_add` (layerC/pss_scratch.thy:2895): the single-append growth
control at the top level, `b1x_triG z t (t +_B c')`, from the trivial `G_u 0 = ∅`
base by one `b1x_triG_addBT`. -/
private theorem ot1_triG_add_td2 {z : BT} (t2 c' : BT) : b1x_triG z t2 (addBT t2 c') := by
  have base : b1x_triG z BZero c' := by
    apply b1x_triG_I
    intro u c _ _ x hx
    rw [GBT_BZero_td2] at hx
    exact hx.elim
  rcases t2 with ⟨t2s⟩
  have step := b1x_triG_addBT_x5 (z := z) t2s base
  rw [addBT_BZero_td2] at step
  exact step

/-! ## 1. condIII `tri0` leg (Isabelle `crx_tri0_of_nest`, spine `crx_tri0_ts` twin) -/

set_option maxHeartbeats 1000000 in
/-- Isabelle `crx_tri0_of_nest` (`pss_scratch.thy`:2784), census r72 upper endpoint
`ins 0_B` form.  Verbatim `«8».«8.7-tri0-spine»` `crx_tri0_ts` (with `_td2` helpers). -/
private theorem crx_tri0_td2
    (M : PS) (ins : BT → BT) (s0 b0 u1 u2 v1w v2 : List Sym)
    (hST : STPS M) (hmono : monoT M = true) (hj1 : 1 < Lng M - 1)
    (hcIII : transCondIII M = true) (hT1 : transT1 M ≠ BZero)
    (hflat : ∀ X, flatBT (ins X)
        = s0 ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT X ++ b0)
    (dP : scb_decomp (Trans (Pred (s84x_N M)))
            (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1w)
    (d2 : scb_decomp (Trans (s84x_N M))
            (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC2 M)) v1w)
    (d4c2 : scb_decomp (transC2 M) u2
            (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) v2)
    (inner : scb_decomp (bpHeadT (Trans (s84x_N M))) s0
            (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0) :
    b1x_triG (Dprin (⊤ : ℕ∞) BZero) (bpHeadT (Trans (Pred (s84x_N M)))) (ins BZero) := by
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have hJ1pos : 0 < transJ1 M := by simp only [transJ1, lastIdx]; omega
  obtain ⟨hVeq, hc1eq, ht2TB, _⟩ := c1_shape_holds M hMR hMT hmono hJ1pos hT1
  have c1sh : transC1 M = Dprin (transV M) (transT2 M) := by rw [hc1eq, hVeq]
  have c2sh : transC2 M = Dprin (transV M)
      (addBT (transT2 M) (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) :=
    crx_c2_shape_condIII_td2 M hcIII
  set c : BT := Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero with hcdef
  set c' : BT := Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero with hc'def
  have cTB : c ∈ T_B := Dprin_nat_mem_T_B_td2 _
  have c'TB : c' ∈ T_B := Dprin_nat_mem_T_B_td2 _
  have cp : ∃ p, c = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have c'p : ∃ p, c' = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  obtain ⟨w4, w4', d4⟩ := add_scb_marked (transT2 M) c ht2TB cTB cp
  have d4' : scb_decomp (addBT (transT2 M) c') w4 (flatBT c') w4' :=
    add_scb_replace_last (transT2 M) c c' w4 w4' ht2TB cTB cp c'TB c'p d4
  have iptc : isPTB_str (flatBT c) := isPTB_str_princ_td2 cTB cp
  have d5 : scb_decomp (Dprin (transV M) (addBT (transT2 M) c))
              ((.dsym (transV M)) :: w4) (flatBT c) w4' :=
    scb_Dprin_lift_td2 (transV M) d4 iptc
  have d5c2 : scb_decomp (transC2 M) ((.dsym (transV M)) :: w4) (flatBT c) w4' := by
    rw [c2sh]; exact d5
  obtain ⟨hu2, hv2⟩ := scb_unique_decomp_unconditional (transC2 M) u2
    ((.dsym (transV M)) :: w4) (flatBT c) v2 w4' d4c2 d5c2
  have fbody : flatBT (bpHeadT (Trans (s84x_N M))) = u1 ++ flatBT (transC2 M) ++ v1w := by
    apply flat_head_bpHeadT_td2 (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
    have h := d2.1; simpa [List.cons_append] using h
  have fc2 : flatBT (transC2 M) = u2 ++ flatBT c ++ v2 := d4c2.1
  have v1RP : ∀ x ∈ v1w, x = Sym.rp := d2.2.2
  have v2RP : ∀ x ∈ v2, x = Sym.rp := d4c2.2.2
  have b0RP' : ∀ x ∈ v2 ++ v1w, x = Sym.rp := by
    intro x hx; rcases List.mem_append.mp hx with h | h
    · exact v2RP x h
    · exact v1RP x h
  have fbody2 : flatBT (bpHeadT (Trans (s84x_N M)))
      = (u1 ++ u2) ++ flatBT c ++ (v2 ++ v1w) := by
    rw [fbody, fc2]; simp [List.append_assoc]
  have innerC : scb_decomp (bpHeadT (Trans (s84x_N M))) (u1 ++ u2) (flatBT c) (v2 ++ v1w) :=
    ⟨fbody2, fun _ => iptc, b0RP'⟩
  obtain ⟨hs0, hb0eq⟩ := scb_unique_decomp_unconditional (bpHeadT (Trans (s84x_N M)))
    s0 (u1 ++ u2) (flatBT c) b0 (v2 ++ v1w) inner innerC
  have hflat0 := hflat BZero
  have hcflat' : Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT BZero = flatBT c' := by
    simp [hc'def, Dprin, flatBT, flatBP]
  have hft2c' : flatBT (addBT (transT2 M) c') = w4 ++ flatBT c' ++ w4' := d4'.1
  have fins2 : flatBT (ins BZero)
      = u1 ++ flatBP (.db (transV M) (addBT (transT2 M) c')) ++ v1w := by
    rw [hflat0, hs0, hb0eq]
    calc (u1 ++ u2) ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT BZero ++ (v2 ++ v1w)
        = u1 ++ (u2 ++ (Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT BZero) ++ v2) ++ v1w := by
          simp [List.append_assoc]
      _ = u1 ++ (u2 ++ flatBT c' ++ v2) ++ v1w := by rw [hcflat']
      _ = u1 ++ (Sym.dsym (transV M) :: (w4 ++ flatBT c' ++ w4')) ++ v1w := by
          rw [hu2, hv2]; simp [List.append_assoc]
      _ = u1 ++ (Sym.dsym (transV M) :: flatBT (addBT (transT2 M) c')) ++ v1w := by rw [hft2c']
      _ = u1 ++ flatBP (.db (transV M) (addBT (transT2 M) c')) ++ v1w := by simp [flatBP]
  have fA0' : flatBT (bpHeadT (Trans (Pred (s84x_N M))))
      = u1 ++ flatBP (.db (transV M) (transT2 M)) ++ v1w := by
    have fA0 : flatBT (bpHeadT (Trans (Pred (s84x_N M)))) = u1 ++ flatBT (transC1 M) ++ v1w := by
      apply flat_head_bpHeadT_td2 (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
      have h := dP.1; simpa [List.cons_append] using h
    rw [fA0, c1sh]; simp [Dprin, flatBT, flatBP]
  exact scbext_triG_x5 (z := Dprin (⊤ : ℕ∞) BZero)
    (cp := BP.db (transV M) (transT2 M))
    (cp' := BP.db (transV M) (addBT (transT2 M) c'))
    (ot1_triG_grow_x5 (z := Dprin (⊤ : ℕ∞) BZero) (transV M) (transT2 M) c')
    (bpHeadT (Trans (Pred (s84x_N M)))) (ins BZero) u1 v1w fA0' fins2 v1RP

/-! ## 2. condIV `tri0` leg (Isabelle `cnv_tri0_of_nest`, spine `cnv_tri0_ts` twin) -/

set_option maxHeartbeats 1000000 in
/-- Isabelle `cnv_tri0_of_nest` (`pss_scratch.thy`:2915), census r72 upper endpoint
`ins 0_B` form.  Verbatim `«8».«8.7-tri0-spine»` `cnv_tri0_ts` (with `_td2` helpers). -/
private theorem cnv_tri0_td2
    (M : PS) (ins : BT → BT) (s0 b0 u1 u2 v1w v2 : List Sym)
    (hST : STPS M) (hmono : monoT M = true) (hj1 : 1 < Lng M - 1)
    (hcIV : transCondIV M = true) (hT1 : transT1 M ≠ BZero)
    (hcnvShape : Cnv_c2_shape_condIV) (hcnvHole : Cnv_nested_hole_pair)
    (hflat : ∀ X, flatBT (ins X)
        = s0 ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT X ++ b0)
    (dP : scb_decomp (Trans (Pred (s84x_N M)))
            (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1w)
    (d2 : scb_decomp (Trans (s84x_N M))
            (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC2 M)) v1w)
    (d4c2 : scb_decomp (transC2 M) u2
            (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) v2)
    (inner : scb_decomp (bpHeadT (Trans (s84x_N M))) s0
            (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0) :
    b1x_triG (Dprin (⊤ : ℕ∞) BZero) (bpHeadT (Trans (Pred (s84x_N M)))) (ins BZero) := by
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have hJ1pos : 0 < transJ1 M := by simp only [transJ1, lastIdx]; omega
  obtain ⟨hVeq, hc1eq, ht2TB, _⟩ := c1_shape_holds M hMR hMT hmono hJ1pos hT1
  have c1sh : transC1 M = Dprin (transV M) (transT2 M) := by rw [hc1eq, hVeq]
  obtain ⟨t3, t4, ht3TB, ht4TB, c2full, dich⟩ := hcnvShape M hST hmono hj1 hT1 hcIV
  set w : ℕ∞ := ((entry M 1 (transJ0 M) : ℕ) : ℕ∞) with hwdef
  set c : BT := Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero with hcdef
  set cc : BT := Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero with hccdef
  obtain ⟨sB, bB, holeU⟩ := hcnvHole t3 t4 w ht4TB
  have cTB : c ∈ T_B := Dprin_nat_mem_T_B_td2 _
  have ccTB : cc ∈ T_B := Dprin_nat_mem_T_B_td2 _
  have cp : ∃ p, c = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have ccp : ∃ p, cc = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have dB : scb_decomp (addBT t3 (Dprin w (addBT t4 c))) sB (flatBT c) bB := holeU c cTB cp
  have dBcc : scb_decomp (addBT t3 (Dprin w (addBT t4 cc))) sB (flatBT cc) bB := holeU cc ccTB ccp
  have iptc : isPTB_str (flatBT c) := isPTB_str_princ_td2 cTB cp
  have dc2can0 : scb_decomp (Dprin (transV M) (addBT t3 (Dprin w (addBT t4 c))))
      ((.dsym (transV M)) :: sB) (flatBT c) bB := scb_Dprin_lift_td2 (transV M) dB iptc
  have dc2can : scb_decomp (transC2 M) ((.dsym (transV M)) :: sB) (flatBT c) bB := by
    rw [c2full]; exact dc2can0
  obtain ⟨hu2, hv2⟩ := scb_unique_decomp_unconditional (transC2 M) u2
    ((.dsym (transV M)) :: sB) (flatBT c) v2 bB d4c2 dc2can
  have fbody : flatBT (bpHeadT (Trans (s84x_N M))) = u1 ++ flatBT (transC2 M) ++ v1w := by
    apply flat_head_bpHeadT_td2 (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
    have h := d2.1; simpa [List.cons_append] using h
  have fc2 : flatBT (transC2 M) = u2 ++ flatBT c ++ v2 := d4c2.1
  have v1RP : ∀ x ∈ v1w, x = Sym.rp := d2.2.2
  have v2RP : ∀ x ∈ v2, x = Sym.rp := d4c2.2.2
  have b0RP' : ∀ x ∈ v2 ++ v1w, x = Sym.rp := by
    intro x hx; rcases List.mem_append.mp hx with h | h
    · exact v2RP x h
    · exact v1RP x h
  have fbody2 : flatBT (bpHeadT (Trans (s84x_N M)))
      = (u1 ++ u2) ++ flatBT c ++ (v2 ++ v1w) := by
    rw [fbody, fc2]; simp [List.append_assoc]
  have innerC : scb_decomp (bpHeadT (Trans (s84x_N M))) (u1 ++ u2) (flatBT c) (v2 ++ v1w) :=
    ⟨fbody2, fun _ => iptc, b0RP'⟩
  obtain ⟨hs0, hb0eq⟩ := scb_unique_decomp_unconditional (bpHeadT (Trans (s84x_N M)))
    s0 (u1 ++ u2) (flatBT c) b0 (v2 ++ v1w) inner innerC
  have hflat0 := hflat BZero
  have hccflat : Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT BZero = flatBT cc := by
    simp [hccdef, Dprin, flatBT, flatBP]
  have hfB : flatBT (addBT t3 (Dprin w (addBT t4 cc))) = sB ++ flatBT cc ++ bB := dBcc.1
  have fins2 : flatBT (ins BZero)
      = u1 ++ flatBP (.db (transV M) (addBT t3 (Dprin w (addBT t4 cc)))) ++ v1w := by
    rw [hflat0, hs0, hb0eq]
    calc (u1 ++ u2) ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT BZero ++ (v2 ++ v1w)
        = u1 ++ (u2 ++ (Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT BZero) ++ v2) ++ v1w := by
          simp [List.append_assoc]
      _ = u1 ++ (u2 ++ flatBT cc ++ v2) ++ v1w := by rw [hccflat]
      _ = u1 ++ (Sym.dsym (transV M) :: (sB ++ flatBT cc ++ bB)) ++ v1w := by
          rw [hu2, hv2]; simp [List.append_assoc]
      _ = u1 ++ (Sym.dsym (transV M) :: flatBT (addBT t3 (Dprin w (addBT t4 cc)))) ++ v1w := by rw [hfB]
      _ = u1 ++ flatBP (.db (transV M) (addBT t3 (Dprin w (addBT t4 cc)))) ++ v1w := by simp [flatBP]
  have fA0' : flatBT (bpHeadT (Trans (Pred (s84x_N M))))
      = u1 ++ flatBP (.db (transV M) (transT2 M)) ++ v1w := by
    have fA0 : flatBT (bpHeadT (Trans (Pred (s84x_N M)))) = u1 ++ flatBT (transC1 M) ++ v1w := by
      apply flat_head_bpHeadT_td2 (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
      have h := dP.1; simpa [List.cons_append] using h
    rw [fA0, c1sh]; simp [Dprin, flatBT, flatBP]
  have prin : b1x_triG (Dprin (⊤ : ℕ∞) BZero)
      (Dprin (transV M) (transT2 M))
      (Dprin (transV M) (addBT t3 (Dprin w (addBT t4 cc)))) := by
    apply b1x_triG_Dpt_x5 (z := Dprin (⊤ : ℕ∞) BZero) (transV M)
    rcases dich with ⟨ht3, ht4⟩ | hB
    · subst ht3; subst ht4
      exact ot1_triG_add_td2 (z := Dprin (⊤ : ℕ∞) BZero) (transT2 M)
        (Dprin w (addBT (transT2 M) cc))
    · obtain ⟨t3s⟩ := t3
      have s1 : b1x_triG (Dprin (⊤ : ℕ∞) BZero) t4 (addBT t4 cc) :=
        ot1_triG_add_td2 (z := Dprin (⊤ : ℕ∞) BZero) t4 cc
      have s2 : b1x_triG (Dprin (⊤ : ℕ∞) BZero) (Dprin w t4) (Dprin w (addBT t4 cc)) :=
        b1x_triG_Dpt_x5 (z := Dprin (⊤ : ℕ∞) BZero) w s1
      have s3 : b1x_triG (Dprin (⊤ : ℕ∞) BZero)
          (addBT (BT.trm t3s) (Dprin w t4)) (addBT (BT.trm t3s) (Dprin w (addBT t4 cc))) :=
        b1x_triG_addBT_x5 (z := Dprin (⊤ : ℕ∞) BZero) t3s s2
      rw [hB]; exact s3
  exact scbext_triG_x5 (z := Dprin (⊤ : ℕ∞) BZero)
    (cp := BP.db (transV M) (transT2 M))
    (cp' := BP.db (transV M) (addBT t3 (Dprin w (addBT t4 cc))))
    prin
    (bpHeadT (Trans (Pred (s84x_N M)))) (ins BZero) u1 v1w fA0' fins2 v1RP

/-! ## 3. corner `tri0` leg (condIV ∧ admeq; collapse identities, no wrapper) -/

set_option maxHeartbeats 1000000 in
/-- **corner `tri0`** (condIV admeq corner).  At the corner `cornerCollapse_holds_cr`
gives `Trans (Pred (s84x_N M)) = transC1 M` and `Trans (s84x_N M) = transC2 M`.  With
`transC1 M = D_{transV} transT2` the goal head collapses to the BARE `transT2 M`
(`bpHeadT (transC1 M) = transT2 M`, no scb wrapper), so the `scbext_triG` lift the ltJ
legs use is not needed and `dP`/`d2` (degenerate at the corner) are not consulted.  The
census `inner`/`hflat` pin `ins 0_B = t₃ +_B D_w (t₄ +_B D_{v₁-1} 0_B)` through the
condIV nested-hole surgery pair `Cnv_nested_hole_pair_holds` plus scb uniqueness, and the
corner goal `b1x_triG (D_∞ 0_B) (transT2 M) (t₃ +_B D_w (t₄ +_B D_{v₁-1} 0_B))` is EXACTLY
the inner growth of the condIV dichotomy — closed directly by
`ot1_triG_add`/`b1x_triG_Dpt`/`b1x_triG_addBT`. -/
private theorem corner_tri0_td2
    (M : PS) (ins : BT → BT) (s0 b0 : List Sym)
    (hST : STPS M) (hmono : monoT M = true) (hj1 : 1 < Lng M - 1)
    (hIV : transCondIV M = true) (hadmeq : Adm M (s84x_jm2 M) = transJm1 M)
    (hp : hasParent M 1 (Lng M - 1) = true)
    (hflat : ∀ X, flatBT (ins X)
        = s0 ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT X ++ b0)
    (hinner : scb_decomp (bpHeadT (Trans (s84x_N M))) s0
            (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0) :
    b1x_triG (Dprin (⊤ : ℕ∞) BZero) (bpHeadT (Trans (Pred (s84x_N M)))) (ins BZero) := by
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have hlen : 1 < Lng M := by omega
  have hJ1pos : 0 < transJ1 M := by simp only [transJ1, lastIdx]; omega
  -- `transT1 M ≠ 0_B`
  have hLP : Lng (Pred M) = Lng M - 1 := by simp [Pred, Nat.not_le.mpr hlen]
  have nzP : zeroT (Pred M) = false := by
    have hne : ¬ (Lng (Pred M) = 1) := by rw [hLP]; omega
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    exact Or.inl hne
  have hT1 : transT1 M ≠ BZero := by
    have T1' : Trans (Pred M) ≠ BZero :=
      (Trans_Mark_invariant (Pred M) (RTPS_Pred M hMR)).2.1 nzP
    simpa [transT1] using T1'
  -- collapse identities
  obtain ⟨cN, cPN⟩ := cornerCollapse_holds_cr M hST hmono hp hj1 hIV hadmeq
  -- c1 shape ⇒ `bpHeadT (transC1 M) = transT2 M`
  obtain ⟨hVeq, hc1eq, ht2TB, _⟩ := c1_shape_holds M hMR hMT hmono hJ1pos hT1
  have c1sh : transC1 M = Dprin (transV M) (transT2 M) := by rw [hc1eq, hVeq]
  have hA0 : bpHeadT (transC1 M) = transT2 M := by rw [c1sh]; rfl
  -- condIV c2 nested shape + uniform nested hole
  obtain ⟨t3, t4, ht3TB, ht4TB, c2full, dich⟩ :=
    Cnv_c2_shape_condIV_holds M hST hmono hj1 hT1 hIV
  set w : ℕ∞ := ((entry M 1 (transJ0 M) : ℕ) : ℕ∞) with hwdef
  set c : BT := Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero with hcdef
  set cc : BT := Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero with hccdef
  obtain ⟨sB, bB, holeU⟩ := Cnv_nested_hole_pair_holds t3 t4 w ht4TB
  have cTB : c ∈ T_B := Dprin_nat_mem_T_B_td2 _
  have ccTB : cc ∈ T_B := Dprin_nat_mem_T_B_td2 _
  have cp : ∃ p, c = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have ccp : ∃ p, cc = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have dB : scb_decomp (addBT t3 (Dprin w (addBT t4 c))) sB (flatBT c) bB := holeU c cTB cp
  have dBcc : scb_decomp (addBT t3 (Dprin w (addBT t4 cc))) sB (flatBT cc) bB := holeU cc ccTB ccp
  -- rewrite the census `inner` into the nested-hole vocabulary
  have hbp : bpHeadT (transC2 M) = addBT t3 (Dprin w (addBT t4 c)) := by rw [c2full]; rfl
  rw [cN] at hinner
  rw [hbp] at hinner
  obtain ⟨hs0, hb0eq⟩ := scb_unique_decomp_unconditional
    (addBT t3 (Dprin w (addBT t4 c))) s0 sB (flatBT c) b0 bB hinner dB
  -- pin `ins 0_B = t₃ +_B D_w (t₄ +_B D_{v₁-1} 0_B)`
  have hccflat : Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT BZero = flatBT cc := by
    simp [hccdef, Dprin, flatBT, flatBP]
  have hfB : flatBT (addBT t3 (Dprin w (addBT t4 cc))) = sB ++ flatBT cc ++ bB := dBcc.1
  have hins : ins BZero = addBT t3 (Dprin w (addBT t4 cc)) := by
    have hflat0 := hflat BZero
    have feq : flatBT (ins BZero) = flatBT (addBT t3 (Dprin w (addBT t4 cc))) := by
      rw [hflat0, hfB, hs0, hb0eq, ← hccflat]
    calc ins BZero
        = unflatBT (flatBT (ins BZero)) := (unflatBT_flat _).symm
      _ = unflatBT (flatBT (addBT t3 (Dprin w (addBT t4 cc)))) := by rw [feq]
      _ = addBT t3 (Dprin w (addBT t4 cc)) := unflatBT_flat _
  -- collapse the goal head and insertion, then close by the condIV dichotomy growth
  rw [cPN, hA0, hins]
  rcases dich with ⟨ht3, ht4⟩ | hB
  · subst ht3; subst ht4
    exact ot1_triG_add_td2 (z := Dprin (⊤ : ℕ∞) BZero) (transT2 M)
      (Dprin w (addBT (transT2 M) cc))
  · obtain ⟨t3s⟩ := t3
    have s1 : b1x_triG (Dprin (⊤ : ℕ∞) BZero) t4 (addBT t4 cc) :=
      ot1_triG_add_td2 (z := Dprin (⊤ : ℕ∞) BZero) t4 cc
    have s2 : b1x_triG (Dprin (⊤ : ℕ∞) BZero) (Dprin w t4) (Dprin w (addBT t4 cc)) :=
      b1x_triG_Dpt_x5 (z := Dprin (⊤ : ℕ∞) BZero) w s1
    have s3 : b1x_triG (Dprin (⊤ : ℕ∞) BZero)
        (addBT (BT.trm t3s) (Dprin w t4)) (addBT (BT.trm t3s) (Dprin w (addBT t4 cc))) :=
      b1x_triG_addBT_x5 (z := Dprin (⊤ : ℕ∞) BZero) t3s s2
    rw [hB]; exact s3

/-! ## 4. `Tri0CruxConcrete` — UNCONDITIONAL (ltJ/corner dispatch) -/

/-- **`Tri0CruxConcrete` discharged unconditionally.**  `ltJ_or_IVadmeq_sp` splits the
condIII/IV host into the ltJ region and the condIV admeq corner:
- ltJ: the unconditional ltJ package `exch84ScbDecompPkgLtJ_holds_sp2` supplies
  `hT1`/`dP`/`d2`/`d4c2`, fed into `crx_tri0_td2` (condIII) / `cnv_tri0_td2` (condIV, with
  `Cnv_c2_shape_condIV_holds` / `Cnv_nested_hole_pair_holds`).
- corner (always condIV): `corner_tri0_td2` closes directly from the collapse identities. -/
theorem tri0CruxConcrete_holds : Tri0CruxConcrete := by
  intro M ins s0 b0 hST hmono hj1 hcond hp _hb0 hflat hinner
  rcases ltJ_or_IVadmeq_sp M hST hmono hp hj1 hcond with hltJ | ⟨hIV, hadmeq⟩
  · obtain ⟨hT1, u1, u2, v1, v2, dP, d2, d4c2, _c5⟩ :=
      exch84ScbDecompPkgLtJ_holds_sp2 M hST hmono hp hj1 hcond hltJ
    rcases hcond with hcIII | hcIV
    · exact crx_tri0_td2 M ins s0 b0 u1 u2 v1 v2 hST hmono hj1 hcIII hT1 hflat dP d2 d4c2 hinner
    · exact cnv_tri0_td2 M ins s0 b0 u1 u2 v1 v2 hST hmono hj1 hcIV hT1
        Cnv_c2_shape_condIV_holds Cnv_nested_hole_pair_holds hflat dP d2 d4c2 hinner
  · exact corner_tri0_td2 M ins s0 b0 hST hmono hj1 hIV hadmeq hp hflat hinner

#print axioms tri0CruxConcrete_holds

/-! ## 5. `otSetleCore` composition (Tri0Crux removed) -/

/-- **`otSetleCore` composed with the now-unconditional `tri0CruxConcrete_holds`.**
`«8».«8.7-census-provenance»`'s `otSetleCore_of_parts_cp` reduced `OTintIIIIV_otSetleCore`
to `{A0OTNub, Tri0CruxConcrete, SetleCensusSpine, SetleCensusWrapperCondIV_cp}`
(with `CensusProvenance` already fully discharged there).  Threading the unconditional
`tri0CruxConcrete_holds` removes the `Tri0CruxConcrete` part, so the `otSetleCore` field's
remaining residuals are exactly `{A0OTNub, SetleCensusSpine, SetleCensusWrapperCondIV_cp}`. -/
theorem otSetleCore_of_remaining_td2 (hnub : A0OTNub) (hspine : SetleCensusSpine)
    (hIVres : SetleCensusWrapperCondIV_cp) : OTintIIIIV_otSetleCore :=
  otSetleCore_of_parts_cp hnub tri0CruxConcrete_holds hspine hIVres

#print axioms otSetleCore_of_remaining_td2

end PSS
