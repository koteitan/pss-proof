import «8».«8.7-otint-tri0-census»
import «8».«8.4-mnform-corner-dispatch»
import «8».«8.4-d4a-trunk»
import «8».«8.4-slicepkg-residuals»
import «8».«8.4-exch84-from-slice»
import «8».«8.4-np-c2decomp»
import «8».«8.4-corner-engine»
import «8».«8.4-corner-core»
import «8».«8.4-corner-readouts»
import «8».«8.4-corner-np-value»
import «8».«8.4-corner-deep»
import «8».«8.4-scbdecomp-pkg»
import «8».«8.5-exchV-props»
import «7».«7.2-add-scb»

/-!
# PSS.«8».«8.7-census-provenance» — discharging `CensusProvenance` (and `SetleCensusWrapper`)

The BUILT `«8».«8.7-otint-tri0-census» reduces the termination field `otSetleCore` to
five census parts via `otSetleCore_of_parts_tc`:
`{A0OTNub, CensusProvenance, Tri0CruxConcrete, SetleCensusWrapper, SetleCensusSpine}`.
This file discharges two of them.

## `CensusProvenance` (`censusProvenance_holds_cp`) — FULLY CLOSED

`CensusProvenance M` is exactly `SlicepkgMnformOut_sp M` on the condIII/IV `hasParent`
host.  The mnform chain is now live and unconditional:

* `mnform_of_residual` (`«8».«8.4-exch84-mnform»`) turns a `MnformResidual M` into the
  provenance `SlicepkgMnformOut_sp M`.
* `mnformResidual_dispatch_md` (`«8».«8.4-mnform-corner-dispatch»`) supplies
  `∀ M … → MnformResidual M` from four now-unconditional legs:
  - `nestScbD4aTransport_dk` (`«8».«8.4-d4a-trunk»`, d4a transport),
  - `transC2HoleDecomp_holds_sr` (`«8».«8.4-slicepkg-residuals»`, the c4 hole),
  - `mnformBottomExtResidual_holds ∘ sliceExtTupleResidual_holds_nc2`
    (`«8».«8.4-exch84-from-slice»` ∘ `«8».«8.4-np-c2decomp»`, the ltJ bottom bundle),
  - the corner leg
    `mnformCornerResidual_holds_ce ∘ mnformCornerCoreResidual_holds_cc ∘
    (cornerCoreReadouts_of_residual cornerNpSliceValue_holds_cnv, cornerC2Kind1_holds_cd)`.

## `SetleCensusWrapper` (`setleCensusWrapper_holds_cp`) — house pattern

`SetleCensusWrapper` is the Isabelle `crx_base1_of_nest` `fA0'`/`fins2` residual: the
shared deeper-wrapper decomposition of `A₀` versus `ins 0_B`.  We pin the abstract
census binders with `censusPin_tc` (threading the provenance produced above), dispatch
`ltJ`/corner with `ltJ_or_IVadmeq_sp`, and on the `ltJ` side re-derive the `fA0'`/`fins2`
existence directly (the construction that lives PRIVATELY inside `oy1_base1Y_condIII_b1p`
/ `oy1_base1Y_condIV_b1p` in `«8».«8.4-exch84-base1p»`) from the now-unconditional ltJ scb
package `exch84ScbDecompPkgLtJ_holds_sp2` plus the pinned `inner`/`hflat`.  The condIV/admeq
corner degeneracy is exposed as the named residual `SetleCensusWrapperCorner_cp`.

## Status
🤖 GREEN-MODULO (`sorry` 0, axioms = `[propext, Classical.choice, Quot.sound]`).
Private suffix `_cp`.
-/

namespace PSS

/-! ## 1. `CensusProvenance` — the mnform chain wired unconditionally -/

/-- **`CensusProvenance` (`«8».«8.7-otint-tri0-census»:204`) discharged.**  On the
condIII/IV `hasParent` host, the concrete census provenance `SlicepkgMnformOut_sp M`
is produced by `mnform_of_residual` fed by the unconditional `mnformResidual_dispatch_md`.
The four dispatch legs are all now unconditional (see the module docstring). -/
theorem censusProvenance_holds_cp : CensusProvenance := by
  intro M hST hmono hp hj1 hcond
  have hread : CornerCoreReadouts_cc :=
    cornerCoreReadouts_of_residual cornerNpSliceValue_holds_cnv
  have hcorner : MnformCornerResidual_md :=
    mnformCornerResidual_holds_ce
      (mnformCornerCoreResidual_holds_cc transC2HoleDecomp_holds_sr hread
        cornerC2Kind1_holds_cd)
  have hres : MnformResidual M :=
    mnformResidual_dispatch_md nestScbD4aTransport_dk transC2HoleDecomp_holds_sr
      (mnformBottomExtResidual_holds sliceExtTupleResidual_holds_nc2) hcorner
      M hST hmono hp hj1 hcond
  exact mnform_of_residual M hST hmono hp hj1 hres

#print axioms censusProvenance_holds_cp

/-! ## 2. `SetleCensusWrapper` — pure `T_B`/scb helpers (base1p private twins, suffix `_cp`) -/

/-- Isabelle `vf2x_flat_head_bpHeadT` (layerB/pss_wip.thy:69403): `flatBT t = Dsym v # rest`
gives `flatBT (bpHeadT t) = rest`.  base1p private `flat_head_bpHeadT_b1p` twin. -/
private theorem flat_head_bpHeadT_cp {t : BT} {v : ℕ∞} {rest : List Sym}
    (h : flatBT t = Sym.dsym v :: rest) : flatBT (bpHeadT t) = rest := by
  obtain ⟨xs⟩ := t
  match xs with
  | [] => simp [flatBT] at h
  | [.db u a] =>
      simp only [flatBT, flatBP, List.cons.injEq] at h
      simp only [bpHeadT]; exact h.2
  | .db u a :: .db u2 a2 :: qs =>
      simp only [flatBT, List.cons_append, List.cons.injEq, reduceCtorEq, false_and] at h

/-- condIII の c2 形状（Isabelle `crx_c2_shape_condIII`, layerB/pss_wip.thy:88353）。
base1p private `crx_c2_shape_condIII_b1p` twin。 -/
private theorem crx_c2_shape_condIII_cp (M : PS) (hcIII : transCondIII M = true) :
    transC2 M = Dprin (transV M)
      (addBT (transT2 M) (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) := by
  unfold transC2 transC2Core
  simp only [hcIII, Bool.or_eq_true, or_true, true_or, if_true]
  rfl

/-- `D_v 0_B ∈ T_B`（`v` は有限指標）。base1p private `Dprin_nat_mem_T_B_b1p` twin。 -/
private theorem Dprin_nat_mem_T_B_cp (n : ℕ) : Dprin (n : ℕ∞) BZero ∈ T_B := by
  simp [T_B, Dprin, dfree_BT, dfree_BPList, dfree_BP, BZero]

/-- 単項 `T_B` 項の flat 文字列は `isPTB_str`。base1p private `isPTB_str_princ_b1p` twin。 -/
private theorem isPTB_str_princ_cp {c : BT} (hc : c ∈ T_B) (hcP : ∃ p, c = BT.trm [p]) :
    isPTB_str (flatBT c) := by
  obtain ⟨p, rfl⟩ := hcP
  refine ⟨p, ?_, by simp [flatBT]⟩
  simpa [T_B, dfree_BT, dfree_BPList] using hc

/-- Isabelle `scb_Dpt_lift` (layerB/pss_wip.thy:1663): `D_v` を被せると scb 分解の左文脈に
`Dsym v` が 1 つ増える。base1p private `scb_Dprin_lift_b1p` twin。 -/
private theorem scb_Dprin_lift_cp {X : BT} {s c b : List Sym} (v : ℕ∞)
    (d : scb_decomp X s c b) (ipt : isPTB_str c) :
    scb_decomp (Dprin v X) ((.dsym v) :: s) c b := by
  obtain ⟨he, _, hrp⟩ := d
  refine ⟨?_, fun _ => ipt, hrp⟩
  have hflat : flatBT (Dprin v X) = (.dsym v) :: flatBT X := by
    simp [Dprin, flatBT, flatBP]
  rw [hflat, he]; simp

/-- `transCondIII` と `transCondIV` は排他的（前者は `adm (lastParent)` を要求、後者は否定）。 -/
private theorem transCondIII_IV_excl_cp {M : PS}
    (h3 : transCondIII M = true) (h4 : transCondIV M = true) : False := by
  simp only [transCondIII, Bool.and_eq_true] at h3
  simp only [transCondIV, Bool.and_eq_true] at h4
  have ha3 : adm M (lastParent M) = true := h3.2
  have ha4 : (!adm M (lastParent M)) = true := h4.2
  rw [ha3] at ha4
  exact absurd ha4 (by decide)

/-! ## 3. condIII の `fA0'`/`fins2` 存在（`crx_base1_of_nest` の存在版、`oy1_base1Y_condIII` port） -/

set_option maxHeartbeats 1000000 in
/-- **condIII の census wrapper 存在**（Isabelle `crx_base1_of_nest` の存在値、
`oy1_base1Y_condIII` の `fA0'`/`fins2`）。base1p private `oy1_base1Y_condIII_b1p` と同じ
共有 surgery 拡張で、`lessBT` の代わりに `∃ s b tv t2 c'` の共有深層 wrapper 分解を返す。
入力 `dP`/`d2`/`d4c2` は無条件 ltJ pkg `exch84ScbDecompPkgLtJ_holds_sp2` から供給される。 -/
private theorem wrapperExists_condIII_cp
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
    ∃ (s b : List Sym) (tv : ℕ∞) (t2 c' : BT),
      flatBT (bpHeadT (Trans (Pred (s84x_N M)))) = s ++ flatBP (BP.db tv t2) ++ b ∧
      flatBT (ins BZero) = s ++ flatBP (BP.db tv (addBT t2 c')) ++ b ∧
      (∀ x ∈ b, x = Sym.rp) := by
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have hJ1pos : 0 < transJ1 M := by simp only [transJ1, lastIdx]; omega
  obtain ⟨hVeq, hc1eq, ht2TB, _⟩ := c1_shape_holds M hMR hMT hmono hJ1pos hT1
  have c1sh : transC1 M = Dprin (transV M) (transT2 M) := by rw [hc1eq, hVeq]
  have c2sh : transC2 M = Dprin (transV M)
      (addBT (transT2 M) (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) :=
    crx_c2_shape_condIII_cp M hcIII
  set c : BT := Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero with hcdef
  set c' : BT := Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero with hc'def
  have cTB : c ∈ T_B := Dprin_nat_mem_T_B_cp _
  have c'TB : c' ∈ T_B := Dprin_nat_mem_T_B_cp _
  have cp : ∃ p, c = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have c'p : ∃ p, c' = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have c'ne : c' ≠ BZero := by simp [hc'def, Dprin, BZero]
  obtain ⟨w4, w4', d4⟩ := add_scb_marked (transT2 M) c ht2TB cTB cp
  have d4' : scb_decomp (addBT (transT2 M) c') w4 (flatBT c') w4' :=
    add_scb_replace_last (transT2 M) c c' w4 w4' ht2TB cTB cp c'TB c'p d4
  have iptc : isPTB_str (flatBT c) := isPTB_str_princ_cp cTB cp
  have d5 : scb_decomp (Dprin (transV M) (addBT (transT2 M) c))
              ((.dsym (transV M)) :: w4) (flatBT c) w4' :=
    scb_Dprin_lift_cp (transV M) d4 iptc
  have d5c2 : scb_decomp (transC2 M) ((.dsym (transV M)) :: w4) (flatBT c) w4' := by
    rw [c2sh]; exact d5
  obtain ⟨hu2, hv2⟩ := scb_unique_decomp_unconditional (transC2 M) u2
    ((.dsym (transV M)) :: w4) (flatBT c) v2 w4' d4c2 d5c2
  have fbody : flatBT (bpHeadT (Trans (s84x_N M))) = u1 ++ flatBT (transC2 M) ++ v1w := by
    apply flat_head_bpHeadT_cp (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
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
  have hcflat' : Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT BZero = flatBT c' := by
    simp [hc'def, Dprin, flatBT, flatBP]
  have hft2c' : flatBT (addBT (transT2 M) c') = w4 ++ flatBT c' ++ w4' := d4'.1
  have fins2 : flatBT (ins BZero)
      = u1 ++ flatBP (.db (transV M) (addBT (transT2 M) c')) ++ v1w := by
    rw [hflat0, hs0, hb0]
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
      apply flat_head_bpHeadT_cp (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
      have h := dP.1; simpa [List.cons_append] using h
    rw [fA0, c1sh]; simp [Dprin, flatBT, flatBP]
  exact ⟨u1, v1w, transV M, transT2 M, c', fA0', fins2, v1RP⟩

/-! ## 4. condIV の census wrapper（named 残差、condIV 隅の入れ子/退化が深い） -/

/-- **condIV の census wrapper 存在残差**（Isabelle `crx_base1_of_nest` の condIV 版）。
condIV では `transC2 M` の c2 本体が入れ子 `t₃ + D_w(t₄ + D_{v₁}0)` になり、`ltJ` 域では
`oy1_base1Y_condIV` の共有 wrapper が使えるが `A₀`/`ins 0_B` の分解基準点は dich 形状
（case 2 の非退化入れ子）と隅（`admeq`）退化で分かれ、共有 `t₂` の存在が非自明。REGS/REGSP
隅エンジンが Lean 未移植のため named 残差として露出する。`SetleCensusWrapper` の hcond を
`transCondIV` に固定した形。 -/
def SetleCensusWrapperCondIV_cp : Prop :=
  ∀ (M : PS) (ins : BT → BT) (A0 body : BT) (e3 v1 : ℕ) (s0 b0 s1 b1 : List Sym),
    STPS M → monoT M = true → 1 < Lng M - 1 →
    transCondIV M = true →
    hasParent M 1 (Lng M - 1) = true →
    Trans M ∈ OT_B →
    (∀ X, flatBT (ins X) = s0 ++ Sym.dsym ((v1 - 1 : ℕ) : ℕ∞) :: flatBT X ++ b0) →
    (∀ x ∈ b0, x = Sym.rp) → (∀ x ∈ b1, x = Sym.rp) →
    scb_decomp body s0 (flatBT (Dprin (v1 : ℕ∞) BZero)) b0 →
    scb_kind1 (Trans M) s1 (flatBT (Dprin (e3 : ℕ∞) body)) b1 →
    (∀ m, 1 ≤ m → flatBT (Trans (oper M m))
      = s1 ++ flatBP (BP.db (e3 : ℕ∞) (coreTower_e34 ins A0 (m - 1))) ++ b1) →
    lessBT (Dprin ((v1 - 1 : ℕ) : ℕ∞) BZero) A0 = true →
    lessBT A0 (ins BZero) = true →
    (∃ (s b : List Sym) (tv : ℕ∞) (t2 c' : BT),
       flatBT A0 = s ++ flatBP (BP.db tv t2) ++ b ∧
       flatBT (ins BZero) = s ++ flatBP (BP.db tv (addBT t2 c')) ++ b ∧
       (∀ x ∈ b, x = Sym.rp))

/-! ## 5. `SetleCensusWrapper` の dispatch（condIII 完全証明 ＋ condIV 残差） -/

/-- **`SetleCensusWrapper`（«8».«8.7-otint-tri0-census»:212）の drop-in**。
`censusPin_tc`（`censusProvenance_holds_cp` で provenance を供給）で `body`/`A₀`/`v₁` を
census provenance に pin し、`hcond` で分岐:
- **condIII 枝（完全証明）**: condIII は必ず `ltJ`（`transCondIII_IV_excl_cp` ＋
  `ltJ_or_IVadmeq_sp`）なので、無条件 ltJ pkg `exch84ScbDecompPkgLtJ_holds_sp2` から
  `dP`/`d2`/`d4c2` を得、`wrapperExists_condIII_cp` で共有深層 wrapper 分解を返す。
- **condIV 枝**: named 残差 `SetleCensusWrapperCondIV_cp` に帰着。 -/
theorem setleCensusWrapper_holds_cp
    (hIVres : SetleCensusWrapperCondIV_cp) : SetleCensusWrapper := by
  intro M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
    hflat hb0 hb1 hinner hk1 hmn base0 base1'
  rcases hcond with hcIII | hcIV
  · -- condIII: pin, establish ltJ, ltJ pkg, existence
    have hprov : SlicepkgMnformOut_sp M :=
      censusProvenance_holds_cp M hST hmono hp hj1 (Or.inl hcIII)
    obtain ⟨hv1, _he3, hbody, hA0⟩ :=
      censusPin_tc M ins A0 body e3 v1 s0 b0 s1 b1 hprov hOT hb1 hinner hk1 hmn
    subst hbody; subst hA0
    have hltJ : s84x_jm3 M < transJm1 M := by
      rcases ltJ_or_IVadmeq_sp M hST hmono hp hj1 (Or.inl hcIII) with h | ⟨hIV, _⟩
      · exact h
      · exact (transCondIII_IV_excl_cp hcIII hIV).elim
    obtain ⟨hT1, u1, u2, v1w, v2, dP, d2, d4c2, _c5⟩ :=
      exch84ScbDecompPkgLtJ_holds_sp2 M hST hmono hp hj1 (Or.inl hcIII) hltJ
    rw [hv1] at hflat hinner
    exact wrapperExists_condIII_cp M ins s0 b0 u1 u2 v1w v2 hST hmono hj1 hcIII hT1
      hflat dP d2 d4c2 hinner
  · -- condIV: residual
    exact hIVres M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcIV hp hOT
      hflat hb0 hb1 hinner hk1 hmn base0 base1'

#print axioms setleCensusWrapper_holds_cp

/-! ## 6. Field reduction combining both discharges -/

/-- **Field reduction (updated).**  `OTintIIIIV_otSetleCore` reduces to
`{A0OTNub, Tri0CruxConcrete, SetleCensusSpine, SetleCensusWrapperCondIV_cp}` — with
`CensusProvenance` fully discharged (`censusProvenance_holds_cp`) and the census
`SetleCensusWrapper` reduced to its condIV residual (condIII fully closed). -/
theorem otSetleCore_of_parts_cp (hnub : A0OTNub) (hcrux : Tri0CruxConcrete)
    (hspine : SetleCensusSpine) (hIVres : SetleCensusWrapperCondIV_cp) :
    OTintIIIIV_otSetleCore :=
  otSetleCore_of_parts_tc hnub censusProvenance_holds_cp hcrux
    (setleCensusWrapper_holds_cp hIVres) hspine

#print axioms otSetleCore_of_parts_cp

end PSS
