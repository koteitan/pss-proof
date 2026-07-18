import «8».«8.7-otint-tri0-census»
import «8».«8.7-otint-kkraw»
import «8».«8.7-otint-ox5-census»
import «8».«8.4-exch84-base1p»
import «7».«7.2-add-scb»

/-!
# PSS.«8».«8.7-tri0-spine» — the two census residuals `Tri0CruxConcrete` and `SetleCensusSpine`

Discharges (largest green subset) the two `otSetleCore`/setle-census residuals that
the BUILT `«8».«8.7-otint-tri0-census»` exposes:

## (1) `Tri0CruxConcrete` — the condIII/IV hole G-control `tri0` brick

Isabelle `crx_tri0_of_nest` / `cnv_tri0_of_nest` (`pss_scratch.thy`:2784/2915,
census r72 form `oy1_tri0Y_census`:4154): the goal is

  `b1x_triG (D_∞ 0_B) (bpHeadT (Trans (Pred (s84x_N M)))) (ins 0_B)`.

Both branches lift the trivial-base principal growth control `ot1_triG_grow_x5`
(condIII) / a growth-dichotomy build (condIV) through a SHARED right-spine scb
wrapper `(u₁,v₁w)` via `scbext_triG_x5` (`«8».«8.7-otint-ox5-census»`).  The
wrapper decomposition — `A₀ = bpHeadT (Trans (Pred (s84x_N M)))` carries the hole
principal `D_{transV} transT2`, `ins 0_B` the grown principal
`D_{transV} (transT2 +_B D_{v₁-1} 0_B)`, sharing `(u₁,v₁w)` — is derived VERBATIM
from the mnform scb legs `dP`/`d2`/`d4c2` exactly as the base₁ leg
`oy1_base1Y_condIII/IV_b1p` (`«8».«8.4-exch84-base1p»`); the only difference is the
final atom: `scbext_triG_x5`+`ot1_triG_grow_x5` (G-control) instead of
`scbext_lessBT` (order).  `dP`/`d2`/`d4c2` come from the live mnform chain and are
threaded as the committed residual `Exch84_scbDecompPkg`; the condIV branch also
consumes `Cnv_c2_shape_condIV` / `Cnv_nested_hole_pair` (the same two residuals the
base₁ condIV leg exposes).

## (2) `SetleCensusSpine` — the surgery-transport census gap (Isabelle STATUS §7)

`SetleCensusSpine` concludes `SpineSurgeryTransport_kk body (ins 0_B)` for an
ABSTRACT `body`.  `censusPin_tc` (`«8».«8.7-otint-tri0-census»`) pins
`body = bpHeadT (Trans (s84x_N M))` from the provenance `SlicepkgMnformOut_sp M`
(threaded via the committed `CensusProvenance`), reducing `SetleCensusSpine` to the
CONCRETE-body transport `SpineSurgeryTransportCensus_ts`.  The transport itself is
the one genuinely-open census gap (Isabelle `ox7_align3_track`, STATUS §(7):
empirically verdict-invariant on STEP-0 11306/11306, faithful `align3`-peel proof a
future file) — left as the named residual, not our own hole.

## What lands (green, `sorry` 0)

* `tri0CruxConcrete_of_pkg_ts : Exch84_scbDecompPkg → Cnv_c2_shape_condIV →
  Cnv_nested_hole_pair → Tri0CruxConcrete` (both branches fully wired).
* `setleCensusSpine_of_census_ts : CensusProvenance → SpineSurgeryTransportCensus_ts
  → SetleCensusSpine`.

## Dependencies (built modules only, committed at 6117365)

- `«8».«8.7-otint-tri0-census»`: `Tri0CruxConcrete` / `SetleCensusSpine` /
  `CensusProvenance` / `censusPin_tc`.
- `«8».«8.7-otint-kkraw»`: `SpineSurgeryTransport_kk`.
- `«8».«8.7-otint-ox5-census»`: `scbext_triG_x5` / `ot1_triG_grow_x5` /
  `b1x_triG_addBT_x5` / `b1x_triG_Dpt_x5`.
- `«8».«8.4-exch84-base1p»`: `Exch84_scbDecompPkg` / `Cnv_c2_shape_condIV` /
  `Cnv_nested_hole_pair` (and transitively `c1_shape_holds`, `transC1`/`transC2`/…).
- `«7».«7.2-add-scb»`: `add_scb_marked` / `add_scb_replace_last`.

## Status
🤖 GREEN-MODULO (`sorry` 0, axioms = `[propext, Classical.choice, Quot.sound]`).
Private suffix `_ts`.
-/

namespace PSS

/-! ## 0. Re-derived private helpers (the `«8».«8.4-exch84-base1p»` twins are `private`) -/

/-- condIII c2 shape (Isabelle `crx_c2_shape_condIII`, layerB/pss_wip.thy:88353). -/
private theorem crx_c2_shape_condIII_ts (M : PS) (hcIII : transCondIII M = true) :
    transC2 M = Dprin (transV M)
      (addBT (transT2 M) (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) := by
  unfold transC2 transC2Core
  simp only [hcIII, Bool.or_eq_true, or_true, true_or, if_true]
  rfl

/-- `D_v 0_B ∈ T_B` (`v` a finite index). -/
private theorem Dprin_nat_mem_T_B_ts (n : ℕ) : Dprin (n : ℕ∞) BZero ∈ T_B := by
  simp [T_B, Dprin, dfree_BT, dfree_BPList, dfree_BP, BZero]

/-- A single-principal `T_B` term flattens to an `isPTB_str` string. -/
private theorem isPTB_str_princ_ts {c : BT} (hc : c ∈ T_B) (hcP : ∃ p, c = BT.trm [p]) :
    isPTB_str (flatBT c) := by
  obtain ⟨p, rfl⟩ := hcP
  refine ⟨p, ?_, by simp [flatBT]⟩
  simpa [T_B, dfree_BT, dfree_BPList] using hc

/-- Isabelle `scb_Dpt_lift` (layerB/pss_wip.thy:1663): wrapping `D_v` adds one
`Dsym v` to the left context of a scb decomposition. -/
private theorem scb_Dprin_lift_ts {X : BT} {s c b : List Sym} (v : ℕ∞)
    (d : scb_decomp X s c b) (ipt : isPTB_str c) :
    scb_decomp (Dprin v X) ((.dsym v) :: s) c b := by
  obtain ⟨he, _, hrp⟩ := d
  refine ⟨?_, fun _ => ipt, hrp⟩
  have hflat : flatBT (Dprin v X) = (.dsym v) :: flatBT X := by
    simp [Dprin, flatBT, flatBP]
  rw [hflat, he]; simp

/-- Isabelle `vf2x_flat_head_bpHeadT` (layerB/pss_wip.thy:69403): if
`flatBT t = Dsym v # rest` then `flatBT (bpHeadT t) = rest`. -/
private theorem flat_head_bpHeadT_ts {t : BT} {v : ℕ∞} {rest : List Sym}
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
private theorem addBT_BZero_ts (t : BT) : addBT t BZero = t := by
  rcases t with ⟨ts⟩; simp [addBT, BZero]

/-- `GBT u 0_B = ∅`. -/
private theorem GBT_BZero_ts (u : ℕ∞) : GBT u BZero = (∅ : Set BT) := by
  ext x
  simp [GBT, BZero, gatherBT, gatherBPList]

/-- Isabelle `ot1_triG_add` (layerC/pss_scratch.thy:2895): the single-append growth
control at the top level, `b1x_triG z t (t +_B c')`, from the trivial `G_u 0 = ∅`
base by one `b1x_triG_addBT`. -/
private theorem ot1_triG_add_ts {z : BT} (t2 c' : BT) : b1x_triG z t2 (addBT t2 c') := by
  have base : b1x_triG z BZero c' := by
    apply b1x_triG_I
    intro u c _ _ x hx
    rw [GBT_BZero_ts] at hx
    exact hx.elim
  rcases t2 with ⟨t2s⟩
  have step := b1x_triG_addBT_x5 (z := z) t2s base
  rw [addBT_BZero_ts] at step
  exact step

/-! ## 1. condIII `tri0` leg (Isabelle `crx_tri0_of_nest`) -/

set_option maxHeartbeats 1000000 in
/-- Isabelle `crx_tri0_of_nest` (`pss_scratch.thy`:2784), census r72 upper endpoint
`ins 0_B` form.  The wrapper derivation mirrors `oy1_base1Y_condIII_b1p`; the finish
is `scbext_triG_x5`+`ot1_triG_grow_x5` (G-control) instead of the order atom. -/
private theorem crx_tri0_ts
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
    crx_c2_shape_condIII_ts M hcIII
  set c : BT := Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero with hcdef
  set c' : BT := Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero with hc'def
  have cTB : c ∈ T_B := Dprin_nat_mem_T_B_ts _
  have c'TB : c' ∈ T_B := Dprin_nat_mem_T_B_ts _
  have cp : ∃ p, c = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have c'p : ∃ p, c' = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  obtain ⟨w4, w4', d4⟩ := add_scb_marked (transT2 M) c ht2TB cTB cp
  have d4' : scb_decomp (addBT (transT2 M) c') w4 (flatBT c') w4' :=
    add_scb_replace_last (transT2 M) c c' w4 w4' ht2TB cTB cp c'TB c'p d4
  have iptc : isPTB_str (flatBT c) := isPTB_str_princ_ts cTB cp
  have d5 : scb_decomp (Dprin (transV M) (addBT (transT2 M) c))
              ((.dsym (transV M)) :: w4) (flatBT c) w4' :=
    scb_Dprin_lift_ts (transV M) d4 iptc
  have d5c2 : scb_decomp (transC2 M) ((.dsym (transV M)) :: w4) (flatBT c) w4' := by
    rw [c2sh]; exact d5
  obtain ⟨hu2, hv2⟩ := scb_unique_decomp_unconditional (transC2 M) u2
    ((.dsym (transV M)) :: w4) (flatBT c) v2 w4' d4c2 d5c2
  have fbody : flatBT (bpHeadT (Trans (s84x_N M))) = u1 ++ flatBT (transC2 M) ++ v1w := by
    apply flat_head_bpHeadT_ts (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
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
      apply flat_head_bpHeadT_ts (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
      have h := dP.1; simpa [List.cons_append] using h
    rw [fA0, c1sh]; simp [Dprin, flatBT, flatBP]
  exact scbext_triG_x5 (z := Dprin (⊤ : ℕ∞) BZero)
    (cp := BP.db (transV M) (transT2 M))
    (cp' := BP.db (transV M) (addBT (transT2 M) c'))
    (ot1_triG_grow_x5 (z := Dprin (⊤ : ℕ∞) BZero) (transV M) (transT2 M) c')
    (bpHeadT (Trans (Pred (s84x_N M)))) (ins BZero) u1 v1w fA0' fins2 v1RP

/-! ## 2. condIV `tri0` leg (Isabelle `cnv_tri0_of_nest`) -/

set_option maxHeartbeats 1000000 in
/-- Isabelle `cnv_tri0_of_nest` (`pss_scratch.thy`:2915), census r72 upper endpoint
`ins 0_B` form.  The condIV mirror of `crx_tri0_ts`: the c2 body is nested
`t₃ +_B D_w(t₄ +_B ·)`, so the `prin` growth is built by the dichotomy (top-level
`ot1_triG_add_ts` / nested `b1x_triG_Dpt_x5`+`b1x_triG_addBT_x5`).  Consumes
`Cnv_c2_shape_condIV` / `Cnv_nested_hole_pair` (the two residuals the base₁ condIV
leg also exposes). -/
private theorem cnv_tri0_ts
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
  have cTB : c ∈ T_B := Dprin_nat_mem_T_B_ts _
  have ccTB : cc ∈ T_B := Dprin_nat_mem_T_B_ts _
  have cp : ∃ p, c = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have ccp : ∃ p, cc = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have dB : scb_decomp (addBT t3 (Dprin w (addBT t4 c))) sB (flatBT c) bB := holeU c cTB cp
  have dBcc : scb_decomp (addBT t3 (Dprin w (addBT t4 cc))) sB (flatBT cc) bB := holeU cc ccTB ccp
  have iptc : isPTB_str (flatBT c) := isPTB_str_princ_ts cTB cp
  have dc2can0 : scb_decomp (Dprin (transV M) (addBT t3 (Dprin w (addBT t4 c))))
      ((.dsym (transV M)) :: sB) (flatBT c) bB := scb_Dprin_lift_ts (transV M) dB iptc
  have dc2can : scb_decomp (transC2 M) ((.dsym (transV M)) :: sB) (flatBT c) bB := by
    rw [c2full]; exact dc2can0
  obtain ⟨hu2, hv2⟩ := scb_unique_decomp_unconditional (transC2 M) u2
    ((.dsym (transV M)) :: sB) (flatBT c) v2 bB d4c2 dc2can
  have fbody : flatBT (bpHeadT (Trans (s84x_N M))) = u1 ++ flatBT (transC2 M) ++ v1w := by
    apply flat_head_bpHeadT_ts (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
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
      apply flat_head_bpHeadT_ts (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
      have h := dP.1; simpa [List.cons_append] using h
    rw [fA0, c1sh]; simp [Dprin, flatBT, flatBP]
  -- FINISH: the condIV growth-dichotomy `prin`, lifted through the wrapper by `scbext_triG_x5`.
  have prin : b1x_triG (Dprin (⊤ : ℕ∞) BZero)
      (Dprin (transV M) (transT2 M))
      (Dprin (transV M) (addBT t3 (Dprin w (addBT t4 cc)))) := by
    apply b1x_triG_Dpt_x5 (z := Dprin (⊤ : ℕ∞) BZero) (transV M)
    rcases dich with ⟨ht3, ht4⟩ | hB
    · subst ht3; subst ht4
      exact ot1_triG_add_ts (z := Dprin (⊤ : ℕ∞) BZero) (transT2 M)
        (Dprin w (addBT (transT2 M) cc))
    · obtain ⟨t3s⟩ := t3
      have s1 : b1x_triG (Dprin (⊤ : ℕ∞) BZero) t4 (addBT t4 cc) :=
        ot1_triG_add_ts (z := Dprin (⊤ : ℕ∞) BZero) t4 cc
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

/-! ## 3. `Tri0CruxConcrete` field discharge (both branches) -/

/-- **`Tri0CruxConcrete` (Isabelle `oy1_tri0Y_census`/`ot1_tri0_census`).**  The
condIII/IV hole G-control `tri0` brick, dispatched over the branch.  The mnform scb
legs `dP`/`d2`/`d4c2` are supplied by the committed residual `Exch84_scbDecompPkg`
(the live mnform chain); the condIV branch additionally consumes
`Cnv_c2_shape_condIV` / `Cnv_nested_hole_pair`. -/
theorem tri0CruxConcrete_of_pkg_ts
    (pkg : Exch84_scbDecompPkg)
    (hcnvShape : Cnv_c2_shape_condIV) (hcnvHole : Cnv_nested_hole_pair) :
    Tri0CruxConcrete := by
  intro M ins s0 b0 hST hmono hj1 hcond hp _hb0 hflat hinner
  obtain ⟨hT1, u1, u2, v1, v2, dP, d2, d4c2, _c5⟩ := pkg M hST hmono hp hj1 hcond
  rcases hcond with hcIII | hcIV
  · exact crx_tri0_ts M ins s0 b0 u1 u2 v1 v2 hST hmono hj1 hcIII hT1 hflat dP d2 d4c2 hinner
  · exact cnv_tri0_ts M ins s0 b0 u1 u2 v1 v2 hST hmono hj1 hcIV hT1
      hcnvShape hcnvHole hflat dP d2 d4c2 hinner

#print axioms tri0CruxConcrete_of_pkg_ts

/-! ## 4. `SetleCensusSpine` — census-pin to the concrete-body surgery transport -/

/-- The census-instantiated surgery TRANSPORT (Isabelle STATUS §(7), the one open
census gap `ox7_align3_track`).  `SpineSurgeryTransport_kk` at the CONCRETE census
`body = bpHeadT (Trans (s84x_N M))` and the census hole insertion `ins 0_B`:
every right-spine sub-body of `body` that is `< body` is also `< ins 0_B`
(`ins 0_B` lowers the deepest-right leaf head `v₁ ⤳ v₁-1`).  Verdict-invariant on
STEP-0 (11306/11306); its faithful `align3`-peel proof is a separate future file. -/
def SpineSurgeryTransportCensus_ts : Prop :=
  ∀ (M : PS) (ins : BT → BT) (s0 b0 : List Sym),
    STPS M → monoT M = true → 1 < Lng M - 1 →
    (transCondIII M = true ∨ transCondIV M = true) →
    hasParent M 1 (Lng M - 1) = true →
    (∀ x ∈ b0, x = Sym.rp) →
    (∀ X, flatBT (ins X)
        = s0 ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT X ++ b0) →
    scb_decomp (bpHeadT (Trans (s84x_N M))) s0
      (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0 →
    SpineSurgeryTransport_kk (bpHeadT (Trans (s84x_N M))) (ins BZero)

/-- **`SetleCensusSpine` reduction.**  `SetleCensusSpine` concludes
`SpineSurgeryTransport_kk body (ins 0_B)` for an abstract `body`.  `censusPin_tc`
identifies `body = bpHeadT (Trans (s84x_N M))` and `v₁ = M_{1,Lng M-1}` from the
provenance `SlicepkgMnformOut_sp M` (threaded via `CensusProvenance`), reducing to
the concrete-body transport `SpineSurgeryTransportCensus_ts`. -/
theorem setleCensusSpine_of_census_ts (hprov : CensusProvenance)
    (htr : SpineSurgeryTransportCensus_ts) : SetleCensusSpine := by
  intro M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
    hflat hb0 hb1 hinner hk1 hmn _base0 _base1'
  obtain ⟨hv1, _he3, hbody, _hA0⟩ := censusPin_tc M ins A0 body e3 v1 s0 b0 s1 b1
    (hprov M hST hmono hp hj1 hcond) hOT hb1 hinner hk1 hmn
  subst hbody
  rw [hv1] at hflat hinner
  exact htr M ins s0 b0 hST hmono hj1 hcond hp hb0 hflat hinner

#print axioms setleCensusSpine_of_census_ts

end PSS
