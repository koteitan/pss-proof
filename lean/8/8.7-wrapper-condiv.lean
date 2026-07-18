import «8».«8.7-census-provenance»
import «8».«8.4-exch84-base1p»
import «8».«8.4-exch84-scbdecomp»
import «8».«8.4-exch84-slicepkg»
import «8».«8.4-scbdecomp-pkg»
import «8».«8.4-corner-redesign»
import «8».«8.5-exchV-props»
import «7».«7.2-add-scb»

/-!
# PSS.«8».«8.7-wrapper-condiv» — discharging `SetleCensusWrapperCondIV_cp`

The BUILT `«8».«8.7-census-provenance»` closes the census `SetleCensusWrapper` **except**
for the condIV branch, which it exposes as the named residual
`SetleCensusWrapperCondIV_cp`.  This file discharges the substantial `ltJ` part of that
residual and narrows the remainder to the admeq **corner** (Isabelle
`cnv_base1_of_nest`, layerB/pss_wip.thy:101903, and the `oy1_base1Y_condIV` leg,
layerC/pss_scratch.thy:1086).

## What `SetleCensusWrapperCondIV_cp` asks for

The shared deeper-wrapper decomposition of `A₀` vs. `ins 0_B`: witnesses `s b tv t₂ c'`
with `flatBT A₀ = s ++ flatBP (D_tv t₂) ++ b` and
`flatBT (ins 0_B) = s ++ flatBP (D_tv (t₂ + c')) ++ b` — i.e. `A₀` and `ins 0_B` share a
context `(s,b)` and differ only by growing **one** principal's body from `t₂` to `t₂ + c'`.

## The `ltJ` branch — FULLY CLOSED (`wrapperExists_condIV_ltJ_wc`)

After `censusPin_tc` pins `A₀ = bpHeadT (Trans (Pred (s84x_N M)))`,
`body = bpHeadT (Trans (s84x_N M))`, `v₁ = M_{1,Lng M-1}`, the dispatch
`ltJ_or_IVadmeq_sp` gives either `ltJ` or the admeq corner.  On `ltJ` the unconditional
pkg `exch84ScbDecompPkgLtJ_holds_sp2` supplies `dP`/`d2`/`d4c2`, and (mirroring the built
`oy1_base1Y_condIV_bl3` up to `fA0'`/`fins2`) we read off
`fA0' : flatBT A₀ = u₁ ++ flatBP (D_transV transT2) ++ v₁w` and
`fins2 : flatBT (ins 0_B) = u₁ ++ flatBP (D_transV (t₃ + D_w(t₄ + cc))) ++ v₁w`.
The condIV `c₂` body is **nested**, so `t₂ = transT2 M` does not host the growth uniformly.
We split on the `Cnv_c2_shape_condIV` dichotomy:
* **degenerate (`t₃ = t₄ = transT2 M`)**: the outer principal grows,
  `c' = D_w(t₄ + cc)` gives `t₂ + c' = t₃ + D_w(t₄ + cc)`.
* **nested (`transT2 M = t₃ + D_w t₄`)**: the OUTER principal cannot host the growth
  (`t₃ + D_w(t₄ + cc) ≠ (t₃ + D_w t₄) + c'` for any `c'`).  We extract the inner `D_w`
  principal via `nestedDb_pair_wc` (a `scb_addBT_left` surgery) and grow **that**:
  `tv = w`, `t₂ = t₄`, `c' = cc`, absorbing `t₃`'s flat into the shared `(s,b)`.

## The admeq corner — named residual `SetleCensusWrapperCondIVCorner_wc`

In the corner `cornerCollapse_holds_cr` gives `Trans (Pred (s84x_N M)) = transC1 M`, so
`A₀ = bpHeadT (transC1 M) = transT2 M` — the outer `D_transV(·)` wrapper principal is
**stripped**.  Then `ins 0_B = t₃ + D_w(t₄ + D_{ub}0)` (base1pCorner reconstruction).  In
the NESTED shape (`transT2 M = t₃ + D_w t₄`) the existence still holds — grow the inner
`D_w` principal, exactly as in the `ltJ` nested case.  But in the DEGENERATE shape
(`t₃ = t₄ = transT2 M`) `ins 0_B = transT2 M + D_w(transT2 M + D_{ub}0)` APPENDS a fresh
principal to `transT2 M` rather than growing an existing one, and the shared-wrapper
existence is structurally unavailable (concrete obstruction: `transT2 M = D₅0` forces
`flatBT A₀ = [D5,zero]`, whereas `flatBT (ins 0_B)` begins with `lp` — no split matches).
Hence this residual is dischargeable **iff** the admeq corner never exhibits the
degenerate shape (`corner ⟹ transT2 M = t₃ + D_w t₄`), the unported REGS corner shape
refinement (Isabelle STATUS §7 / `c4dx_condIV_c2body_shape` in the admeq regime).  This
mirrors the `Base1pCorner_bl3` corner leg of `base1pCondIIIIV_holds_bl3`.

## Status
🤖 GREEN-MODULO (`sorry` 0, axioms = `[propext, Classical.choice, Quot.sound]`).
Private suffix `_wc`.
-/

namespace PSS

/-! ## 1. `T_B`/scb helper twins (base1p / census private twins, suffix `_wc`) -/

/-- Isabelle `vf2x_flat_head_bpHeadT`: `flatBT t = Dsym v # rest` gives
`flatBT (bpHeadT t) = rest`.  Census private `flat_head_bpHeadT_cp` twin. -/
private theorem flat_head_bpHeadT_wc {t : BT} {v : ℕ∞} {rest : List Sym}
    (h : flatBT t = Sym.dsym v :: rest) : flatBT (bpHeadT t) = rest := by
  obtain ⟨xs⟩ := t
  match xs with
  | [] => simp [flatBT] at h
  | [.db u a] =>
      simp only [flatBT, flatBP, List.cons.injEq] at h
      simp only [bpHeadT]; exact h.2
  | .db u a :: .db u2 a2 :: qs =>
      simp only [flatBT, List.cons_append, List.cons.injEq, reduceCtorEq, false_and] at h

/-- `D_n 0_B ∈ T_B` (`n` finite index).  Census private `Dprin_nat_mem_T_B_cp` twin. -/
private theorem Dprin_nat_mem_T_B_wc (n : ℕ) : Dprin (n : ℕ∞) BZero ∈ T_B := by
  simp [T_B, Dprin, dfree_BT, dfree_BPList, dfree_BP, BZero]

/-- A principal `T_B` term flattens to `isPTB_str`.  Census private `isPTB_str_princ_cp`
twin. -/
private theorem isPTB_str_princ_wc {c : BT} (hc : c ∈ T_B) (hcP : ∃ p, c = BT.trm [p]) :
    isPTB_str (flatBT c) := by
  obtain ⟨p, rfl⟩ := hcP
  refine ⟨p, ?_, by simp [flatBT]⟩
  simpa [T_B, dfree_BT, dfree_BPList] using hc

/-- Isabelle `scb_Dpt_lift`: covering with `D_v` grows the scb left-context by one
`Dsym v`.  Census private `scb_Dprin_lift_cp` twin. -/
private theorem scb_Dprin_lift_wc {X : BT} {s c b : List Sym} (v : ℕ∞)
    (d : scb_decomp X s c b) (ipt : isPTB_str c) :
    scb_decomp (Dprin v X) ((.dsym v) :: s) c b := by
  obtain ⟨he, _, hrp⟩ := d
  refine ⟨?_, fun _ => ipt, hrp⟩
  have hflat : flatBT (Dprin v X) = (.dsym v) :: flatBT X := by
    simp [Dprin, flatBT, flatBP]
  rw [hflat, he]; simp

/-- `addBT 0_B X = X`.  `«8».«8.4-exch84-scbdecomp»` private `addBT_BZero_left_sd` twin. -/
private theorem addBT_BZero_left_wc (X : BT) : addBT BZero X = X := by
  cases X; simp [addBT, BZero]

/-- Isabelle `liftS`: the surgery prefix for a left summand `Y`.
`«8».«8.4-exch84-scbdecomp»` private `liftScbPrefix_sd` twin. -/
private def liftScbPrefix_wc (Y : BT) (s : List Sym) : List Sym :=
  match untrm Y with
  | [] => s
  | p :: ps => .lp :: flatBP p ++ flatBPTail ps ++ [.cm] ++ s

private theorem flatBPTail_append_singleton_wc (ps : List BP) (p : BP) :
    flatBPTail (ps ++ [p]) = flatBPTail ps ++ (.cm :: flatBP p) := by
  induction ps with
  | nil => simp [flatBPTail]
  | cons q qs ih => simp [flatBPTail, ih, List.append_assoc]

/-- Isabelle `scb_addBT_left`: prefixing a single principal `X` with a nonempty left
summand `Y` lifts the same-hole scb decomposition under `liftScbPrefix Y`.
`«8».«8.4-exch84-scbdecomp»` private `scb_addBT_left_sd` twin. -/
private theorem scb_addBT_left_wc {X Y : BT} {s c b : List Sym}
    (hd : scb_decomp X s c b)
    (hXone : (untrm X).length = 1)
    (hYne : untrm Y ≠ []) :
    scb_decomp (addBT Y X) (liftScbPrefix_wc Y s) c (b ++ [.rp]) := by
  rcases X with ⟨xs⟩
  rcases Y with ⟨ys⟩
  simp only [untrm] at hXone hYne
  cases xs with
  | nil => simp at hXone
  | cons x xs =>
      cases xs with
      | nil =>
          cases ys with
          | nil => exact (hYne rfl).elim
          | cons y ys =>
              rcases hd with ⟨hflat, hprincipal, htail⟩
              have hXne : BT.trm [x] ≠ BZero := by simp [BZero]
              have hc : isPTB_str c := hprincipal hXne
              have hflat' : flatBP x = s ++ c ++ b := by
                simpa [flatBT] using hflat
              refine ⟨?_, ?_, ?_⟩
              · cases ys <;>
                  simp [addBT, flatBT, flatBPTail, liftScbPrefix_wc, untrm,
                    flatBPTail_append_singleton_wc, hflat', List.append_assoc]
              · intro _
                exact hc
              · intro z hz
                rcases List.mem_append.mp hz with hz | hz
                · exact htail z hz
                · simpa using hz
      | cons x' xs => simp at hXone

/-- **Nested `D_w` principal surgery.**  For fixed `t₃`, `w` (finite) there is one shared
context `(P,Q)` (all-`rp` on the right) so that for every `T_B` hole content `Y` the term
`t₃ + D_w Y` flattens with the `D_w Y` principal exposed:
`flatBT (t₃ + D_w Y) = P ++ (Dsym w :: flatBT Y) ++ Q`.  Built from `scb_addBT_left_wc` on
the trivial single-principal decomposition of `D_w Y`. -/
private theorem nestedDb_pair_wc (t3 : BT) (w : ℕ∞) (hw : w ≠ ⊤) :
    ∃ P Q : List Sym, (∀ x ∈ Q, x = Sym.rp) ∧
      ∀ Y : BT, dfree_BT Y = true →
        flatBT (addBT t3 (Dprin w Y)) = P ++ (Sym.dsym w :: flatBT Y) ++ Q := by
  by_cases ht3 : t3 = BZero
  · refine ⟨[], [], by simp, ?_⟩
    intro Y _hY
    rw [ht3, addBT_BZero_left_wc]
    simp [Dprin, flatBT, flatBP]
  · have hYne : untrm t3 ≠ [] := by
      cases t3 with
      | trm l3 =>
          cases l3 with
          | nil => exact absurd (by simp [BZero]) ht3
          | cons a as => simp [untrm]
    refine ⟨liftScbPrefix_wc t3 [], [Sym.rp], by simp, ?_⟩
    intro Y hY
    have hdfree : dfree_BP (BP.db w Y) = true := by
      simp only [dfree_BP, Bool.and_eq_true, bne_iff_ne]; exact ⟨hw, hY⟩
    have d0 : scb_decomp (Dprin w Y) [] (flatBT (Dprin w Y)) [] :=
      ⟨by simp, fun _ => ⟨BP.db w Y, hdfree, rfl⟩, by simp⟩
    have hX1 : (untrm (Dprin w Y)).length = 1 := by simp [Dprin, untrm]
    have hres := scb_addBT_left_wc d0 hX1 hYne
    rw [hres.1]
    simp [Dprin, flatBT, flatBP]

/-! ## 2. The `ltJ` existence (condIV `crx_base1_of_nest`, `oy1_base1Y_condIV` port) -/

set_option maxHeartbeats 1000000 in
/-- **condIV census wrapper existence on the `ltJ` host.**  Mirrors the built
`oy1_base1Y_condIV_bl3` (`«8».«8.4-base-legs»`) up to `fA0'`/`fins2`, then returns the
shared deeper-wrapper decomposition by casing on the `Cnv_c2_shape_condIV` dichotomy
(degenerate: grow the outer principal; nested: grow the inner `D_w` principal via
`nestedDb_pair_wc`). -/
private theorem wrapperExists_condIV_ltJ_wc
    (M : PS) (ins : BT → BT) (s0 b0 u1 u2 v1w v2 : List Sym)
    (hST : STPS M) (hmono : monoT M = true) (hj1 : 1 < Lng M - 1)
    (hcIV : transCondIV M = true) (hT1 : transT1 M ≠ BZero)
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
    ∃ (s b : List Sym) (tv : ℕ∞) (t2 c' : BT),
      flatBT (bpHeadT (Trans (Pred (s84x_N M)))) = s ++ flatBP (BP.db tv t2) ++ b ∧
      flatBT (ins BZero) = s ++ flatBP (BP.db tv (addBT t2 c')) ++ b ∧
      (∀ x ∈ b, x = Sym.rp) := by
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have hJ1pos : 0 < transJ1 M := by simp only [transJ1, lastIdx]; omega
  obtain ⟨hVeq, hc1eq, ht2TB, _⟩ := c1_shape_holds M hMR hMT hmono hJ1pos hT1
  have c1sh : transC1 M = Dprin (transV M) (transT2 M) := by rw [hc1eq, hVeq]
  obtain ⟨t3, t4, ht3TB, ht4TB, c2full, dich⟩ :=
    Cnv_c2_shape_condIV_holds M hST hmono hj1 hT1 hcIV
  set w : ℕ∞ := ((entry M 1 (transJ0 M) : ℕ) : ℕ∞) with hwdef
  set c : BT := Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero with hcdef
  set cc : BT := Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero with hccdef
  have hwne : w ≠ ⊤ := by rw [hwdef]; exact ENat.coe_ne_top _
  obtain ⟨sB, bB, holeU⟩ := Cnv_nested_hole_pair_holds t3 t4 w ht4TB
  have cTB : c ∈ T_B := Dprin_nat_mem_T_B_wc _
  have ccTB : cc ∈ T_B := Dprin_nat_mem_T_B_wc _
  have cp : ∃ p, c = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have ccp : ∃ p, cc = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have dB : scb_decomp (addBT t3 (Dprin w (addBT t4 c))) sB (flatBT c) bB := holeU c cTB cp
  have dBcc : scb_decomp (addBT t3 (Dprin w (addBT t4 cc))) sB (flatBT cc) bB := holeU cc ccTB ccp
  have iptc : isPTB_str (flatBT c) := isPTB_str_princ_wc cTB cp
  have dc2can0 : scb_decomp (Dprin (transV M) (addBT t3 (Dprin w (addBT t4 c))))
      ((.dsym (transV M)) :: sB) (flatBT c) bB := scb_Dprin_lift_wc (transV M) dB iptc
  have dc2can : scb_decomp (transC2 M) ((.dsym (transV M)) :: sB) (flatBT c) bB := by
    rw [c2full]; exact dc2can0
  obtain ⟨hu2, hv2⟩ := scb_unique_decomp_unconditional (transC2 M) u2
    ((.dsym (transV M)) :: sB) (flatBT c) v2 bB d4c2 dc2can
  have fbody : flatBT (bpHeadT (Trans (s84x_N M))) = u1 ++ flatBT (transC2 M) ++ v1w := by
    apply flat_head_bpHeadT_wc (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
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
  obtain ⟨hs0, hb0⟩ := scb_unique_decomp_unconditional (bpHeadT (Trans (s84x_N M)))
    s0 (u1 ++ u2) (flatBT c) b0 (v2 ++ v1w) inner innerC
  have hflat0 := hflat BZero
  have hccflat : Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT BZero = flatBT cc := by
    simp [hccdef, Dprin, flatBT, flatBP]
  have hfB : flatBT (addBT t3 (Dprin w (addBT t4 cc))) = sB ++ flatBT cc ++ bB := dBcc.1
  have fins2 : flatBT (ins BZero)
      = u1 ++ flatBP (.db (transV M) (addBT t3 (Dprin w (addBT t4 cc)))) ++ v1w := by
    rw [hflat0, hs0, hb0]
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
      apply flat_head_bpHeadT_wc (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
      have h := dP.1; simpa [List.cons_append] using h
    rw [fA0, c1sh]; simp [Dprin, flatBT, flatBP]
  -- Existence: split on the `c₂` shape dichotomy.
  rcases dich with ⟨ht3, _ht4⟩ | hb
  · -- degenerate: outer principal grows, `c' = D_w(t₄ + cc)`
    rw [ht3] at fins2
    exact ⟨u1, v1w, transV M, transT2 M, Dprin w (addBT t4 cc), fA0', fins2, v1RP⟩
  · -- nested: grow the inner `D_w` principal
    obtain ⟨P, Q, hQrp, hdec⟩ := nestedDb_pair_wc t3 w hwne
    have ht4ccTB : dfree_BT (addBT t4 cc) = true := addBT_mem_T_B ht4TB ccTB
    refine ⟨u1 ++ Sym.dsym (transV M) :: P, Q ++ v1w, w, t4, cc, ?_, ?_, ?_⟩
    · have e1 : flatBT (transT2 M) = P ++ (Sym.dsym w :: flatBT t4) ++ Q := by
        rw [hb]; exact hdec t4 ht4TB
      rw [fA0']
      simp only [flatBP, e1]
      simp [List.append_assoc, List.cons_append]
    · have e2 : flatBT (addBT t3 (Dprin w (addBT t4 cc)))
          = P ++ (Sym.dsym w :: flatBT (addBT t4 cc)) ++ Q := hdec (addBT t4 cc) ht4ccTB
      rw [fins2]
      simp only [flatBP, e2]
      simp [List.append_assoc, List.cons_append]
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hQrp x h
      · exact v1RP x h

/-! ## 3. The admeq corner residual (existence form of the corner wrapper) -/

/-- **condIV admeq corner census wrapper residual (existence form).**  The corner analog
of `Base1pCorner_bl3` (`«8».«8.4-base-legs»`), strengthened from the `lessBT` ordering to
the full shared-wrapper decomposition demanded by `SetleCensusWrapperCondIV_cp`.  In the
corner `A₀ = bpHeadT (transC1 M) = transT2 M` (the outer `D_transV(·)` wrapper is stripped
by the collapse), so the existence is available for the NESTED `c₂` shape but structurally
FALSE for the DEGENERATE shape (there `ins 0_B` appends a fresh principal to `transT2 M`).
Dischargeable iff the admeq corner never exhibits the degenerate shape — the unported REGS
corner shape refinement. -/
def SetleCensusWrapperCondIVCorner_wc : Prop :=
  ∀ (M : PS) (ins : BT → BT) (s0 b0 : List Sym),
    STPS M → monoT M = true → 1 < Lng M - 1 →
    transCondIV M = true → hasParent M 1 (Lng M - 1) = true →
    Adm M (s84x_jm2 M) = transJm1 M →
    (∀ X, flatBT (ins X)
        = s0 ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT X ++ b0) →
    (∀ x ∈ b0, x = Sym.rp) →
    scb_decomp (bpHeadT (transC2 M)) s0
      (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0 →
    (∃ (s b : List Sym) (tv : ℕ∞) (t2 c' : BT),
       flatBT (bpHeadT (transC1 M)) = s ++ flatBP (BP.db tv t2) ++ b ∧
       flatBT (ins BZero) = s ++ flatBP (BP.db tv (addBT t2 c')) ++ b ∧
       (∀ x ∈ b, x = Sym.rp))

/-! ## 4. `SetleCensusWrapperCondIV_cp` = `ltJ` (closed) ⊕ corner residual -/

/-- **`SetleCensusWrapperCondIV_cp` reduced to the admeq corner residual.**  `censusPin_tc`
pins the abstract census binders (`A₀`/`body`/`v₁`) to their concrete provenance, then
`ltJ_or_IVadmeq_sp` dispatches:
- **`ltJ`**: the unconditional pkg `exch84ScbDecompPkgLtJ_holds_sp2` feeds
  `wrapperExists_condIV_ltJ_wc` (fully closed).
- **admeq corner**: `cornerCollapse_holds_cr` rewrites `Trans (·) = transC1/transC2 M`
  and reduces to `SetleCensusWrapperCondIVCorner_wc`. -/
theorem setleCensusWrapperCondIV_holds_wc
    (hcorner : SetleCensusWrapperCondIVCorner_wc) : SetleCensusWrapperCondIV_cp := by
  intro M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcIV hp hOT
    hflat hb0 hb1 hinner hk1 hmn _base0 _base1'
  have hprov : SlicepkgMnformOut_sp M :=
    censusProvenance_holds_cp M hST hmono hp hj1 (Or.inr hcIV)
  obtain ⟨hv1, _he3, hbody, hA0⟩ :=
    censusPin_tc M ins A0 body e3 v1 s0 b0 s1 b1 hprov hOT hb1 hinner hk1 hmn
  subst hbody; subst hA0
  rw [hv1] at hflat hinner
  rcases ltJ_or_IVadmeq_sp M hST hmono hp hj1 (Or.inr hcIV) with hltJ | ⟨_hIV, hadmeq⟩
  · -- ltJ branch: pkg + existence port
    obtain ⟨hT1, u1, u2, v1w, v2, dP, d2, d4c2, _c5⟩ :=
      exch84ScbDecompPkgLtJ_holds_sp2 M hST hmono hp hj1 (Or.inr hcIV) hltJ
    exact wrapperExists_condIV_ltJ_wc M ins s0 b0 u1 u2 v1w v2 hST hmono hj1 hcIV hT1
      hflat dP d2 d4c2 hinner
  · -- admeq corner branch: collapse + residual
    obtain ⟨cN, cPN⟩ := cornerCollapse_holds_cr M hST hmono hp hj1 hcIV hadmeq
    rw [cN] at hinner
    rw [cPN]
    exact hcorner M ins s0 b0 hST hmono hj1 hcIV hp hadmeq hflat hb0 hinner

#print axioms setleCensusWrapperCondIV_holds_wc

/-! ## 5. Field reduction combining the discharge -/

/-- **Field reduction (updated).**  `OTintIIIIV_otSetleCore` reduces to
`{A0OTNub, Tri0CruxConcrete, SetleCensusSpine, SetleCensusWrapperCondIVCorner_wc}` — the
census `SetleCensusWrapper` is now fully discharged except for the admeq corner residual
(the `ltJ` condIV branch is closed here). -/
theorem otSetleCore_of_parts_wc (hnub : A0OTNub) (hcrux : Tri0CruxConcrete)
    (hspine : SetleCensusSpine) (hcorner : SetleCensusWrapperCondIVCorner_wc) :
    OTintIIIIV_otSetleCore :=
  otSetleCore_of_parts_cp hnub hcrux hspine (setleCensusWrapperCondIV_holds_wc hcorner)

#print axioms otSetleCore_of_parts_wc

end PSS
