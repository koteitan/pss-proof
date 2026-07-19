import «8».«8.7-tri0-dispatch»
import «8».«8.7-otint-census-leaves»

/-!
# PSS.«8».«8.7-corner-census» — the condIV admeq corner census obligation, RE-PLUMBED

## The blocker and why the old route died

The BUILT `«8».«8.7-census-provenance»` reduced the `otSetleCore` field's setle side to the
census `SetleCensusWrapper` (Isabelle `crx_base1_of_nest` `fA0'`/`fins2`): the **shared
deeper-wrapper** existence `∃ s b tv t₂ c', flatBT A₀ = s ++ flatBP (D_tv t₂) ++ b ∧
flatBT (ins 0_B) = s ++ flatBP (D_tv (t₂ +_B c')) ++ b`.  The `«8».«8.7-wrapper-condiv»`
file closed the `ltJ` part and narrowed the remainder to the admeq corner residual
`SetleCensusWrapperCondIVCorner_wc`, which `«8».«8.7-corner-shape»` then **REFUTED**: at the
admeq corner the collapse `cornerCollapse_holds_cr` strips the outer wrapper, leaving
`A₀ = bpHeadT (transC1 M) = transT2 M` a SINGLE zero-body principal `D_a 0`, while the
census insertion `ins 0_B = transT2 M +_B D_w (transT2 M +_B D_{v₁-1} 0_B)` is a genuine
TWO-principal term (the `+_B` appends a fresh top principal, it does not grow one).  A
shared context in which one principal `D_tv t₂` grows is then structurally impossible
(`corner_wrapper_conclusion_unsat_cs`), and the numeric census shows every one of the 24
admeq-corner condIV hosts is degenerate.  So the wrapper-shaped obligation is FALSE, and
`SetleCensusWrapperCondIV_cp` (a `∀` over all condIV hosts including these corners) is a
FALSE Prop — the whole `OTintIIIIV_setleCensus` route cannot be discharged at the corner.

## Isabelle's actual pivot: the wrapper is never needed — `ox5` follows from `tri0`

The shared wrapper existence is consumed at EXACTLY one place: the built
`«8».«8.7-otint-ox5-census»` `ox5_census_x5` uses it (via `scbext_triG_x5`) to build a
G-control `tri0 : b1x_triG _ A₀ (ins 0_B)`, and then `ox5_body_driver_x5` turns
`tri0` + `base₁ : A₀ < ins 0_B` into the census body driver

    ox5 :  ∀ u, b1x_setle (GBT u A₀) (insert (ins 0_B) (GBT u (ins 0_B))),

which is all the setle assembly (`«8».«8.7-otint-setle-assembly»`
`otSetleCore_setle_holds`) actually needs.  But the G-control `tri0` is **already available
unconditionally**: `«8».«8.7-tri0-dispatch»` `tri0CruxConcrete_holds` proves
`b1x_triG (D_∞ 0_B) A₀ (ins 0_B)` for every condIII/IV host — its corner branch
`corner_tri0_td2` closes DIRECTLY from the collapse identities, no wrapper.  This is the
`ox5_body_driver_census` pivot in `isabelle/layerC/pss_scratch.thy`:4936–4974: the setle
census leaf is built from the `tri0` G-control, not from the wrapper.

The one adaptation: `ox5_body_driver_x5` was stated at `z = 0_B` (using `GBT u 0_B = ∅`),
whereas `tri0CruxConcrete_holds` supplies `z = D_∞ 0_B`.  But `GBT u (D_∞ 0_B) = {0_B}`,
which merges harmlessly with the `{0_B}` already present in the `b1x_triG` conclusion; the
`y = 0_B` case is handled identically.  `ox5_body_driver_cc2` below is the `z = D_∞ 0_B`
variant.  So `ox5` holds unconditionally for the corner — verified numerically on all 24
admeq-corner hosts (`python/audit_corner_ox5_cc2.py`, 24/24, including the mission's
`(0,0)(1,1)(2,2)(2,1)` where `A₀ = D_2 0` but `ins 0_B` is two-principal).

## What this file does

1. **`SetleCensusOx5_cc2`** — the RESTATED census obligation (faithful to Isabelle
   `ox5_body_driver_census`): the census body driver `ox5` itself, replacing the false
   wrapper-existence conjunct.
2. **`setleCensusOx5_holds_cc2 : SetleCensusOx5_cc2`** — discharged UNCONDITIONALLY
   (`censusPin_tc` + `tri0CruxConcrete_holds` + `ox5_body_driver_cc2`).  The corner branch
   closes exactly where the wrapper route died.
3. **`otSetleCoreSetle_of_ox5_cc2`** — the setle consumer accepts `ox5` directly (KKraw
   geometry from `hOT`/`hk1`, then `ox10_SETLE1_close_oc`), mirroring
   `otSetleCore_setle_holds` but taking `ox5` instead of the wrapper.
4. **`otSetleCore_of_parts_cc2 : A0OTNub → SetleCensusSpine → OTintIIIIV_otSetleCore`** —
   the field reduction.  `SetleCensusWrapperCondIV_cp` is **eliminated**: the `otSetleCore`
   field's remaining residuals are exactly `{A0OTNub, SetleCensusSpine}`.

## Status
🤖 GREEN (`sorry` 0, axioms = `[propext, Classical.choice, Quot.sound]`).  Private suffix
`_cc2`.
-/

namespace PSS

/-! ## 1. `GBT`/`lessBT` order helpers (private twins, suffix `_cc2`) -/

/-- `GBT u (D_v b) = if u ≤ v then {b} ∪ GBT u b else ∅` (ox5-census private
`GBT_Dprin_x5` twin). -/
private theorem GBT_Dprin_cc2 (u v : ℕ∞) (b : BT) :
    GBT u (Dprin v b) = if u ≤ v then ({b} ∪ GBT u b) else (∅ : Set BT) := by
  ext x
  by_cases huv : u ≤ v <;>
    simp [GBT, Dprin, gatherBT, gatherBPList, gatherBP, huv]

/-- `GBT u 0_B = ∅` (ox5-census private `GBT_BZero_x5` twin). -/
private theorem GBT_BZero_cc2 (u : ℕ∞) : GBT u BZero = (∅ : Set BT) := by
  ext x
  simp [GBT, BZero, gatherBT, gatherBPList]

/-- `lessBT x 0_B = false` (ox5-census private `lessBT_BZero_false_x5` twin). -/
private theorem lessBT_BZero_false_cc2 (x : BT) : lessBT x BZero = false := by
  rcases x with ⟨xs⟩; cases xs <;> simp [BZero, lessBT, lessBPList]

/-- `0_B < x` whenever `x ≠ 0_B` (ox5-census private `lessBT_BZero_lt_x5` twin). -/
private theorem lessBT_BZero_lt_cc2 {x : BT} (h : x ≠ BZero) : lessBT BZero x = true := by
  rcases x with ⟨xs⟩
  cases xs with
  | nil => exact absurd rfl h
  | cons a as => simp [BZero, lessBT, lessBPList]

/-! ## 2. `ox5_body_driver` at `z = D_∞ 0_B` (the tri0-crux G-control level) -/

/-- **The census body driver at `z = D_∞ 0_B`.**  The `z = 0_B` variant
`ox5_body_driver_x5` (`«8».«8.7-otint-ox5-census»`) used `GBT u 0_B = ∅`; here
`GBT u (D_∞ 0_B) = {0_B}`, which merges with the `{0_B}` already present in the
`b1x_triG` conclusion (the `y = 0_B` case is handled the same way).  This lets the
already-unconditional `tri0CruxConcrete_holds` (which supplies `z = D_∞ 0_B`) feed the
census `ox5` directly — no shared wrapper required. -/
theorem ox5_body_driver_cc2 {A0 X1 : BT} (u : ℕ∞)
    (tri0 : b1x_triG (Dprin (⊤ : ℕ∞) BZero) A0 X1)
    (base1 : lessBT A0 X1 = true) :
    b1x_setle (GBT u A0) (insert X1 (GBT u X1)) := by
  have X1ne : X1 ≠ BZero := by
    intro h; rw [h, lessBT_BZero_false_cc2] at base1; exact Bool.noConfusion base1
  have leA0X1 : leBT A0 X1 = true := by simp [leBT, base1]
  have leX1X1 : leBT X1 X1 = true := by simp [leBT]
  have step := b1x_triG_D (u := u) tri0 leA0X1 leX1X1
  -- `step : b1x_setle (GBT u A0) (GBT u X1 ∪ GBT u (D_∞ 0_B) ∪ {0_B})`
  have hz : GBT u (Dprin (⊤ : ℕ∞) BZero) = ({BZero} : Set BT) := by
    rw [GBT_Dprin_cc2, if_pos (le_top), GBT_BZero_cc2, Set.union_empty]
  intro x hx
  obtain ⟨y, hy, hxy⟩ := step x hx
  have hyc : y ∈ GBT u X1 ∨ y = BZero := by
    rcases hy with (h | h) | h
    · exact Or.inl h
    · rw [hz, Set.mem_singleton_iff] at h; exact Or.inr h
    · rw [Set.mem_singleton_iff] at h; exact Or.inr h
  rcases hyc with hyX1 | hyBZ
  · exact ⟨y, Set.mem_insert_iff.mpr (Or.inr hyX1), hxy⟩
  · subst hyBZ
    have hxeq : x = BZero := by
      have hb : (x == BZero) = true := by
        rw [leBT, lessBT_BZero_false_cc2] at hxy; simpa using hxy
      exact eq_of_beq hb
    subst hxeq
    exact ⟨X1, Set.mem_insert _ _, by simp [leBT, lessBT_BZero_lt_cc2 X1ne]⟩

#print axioms ox5_body_driver_cc2

/-! ## 3. KKraw geometry helpers (private `_sa` twins, suffix `_cc2`) -/

private def symFin_cc2 : Sym → Bool
  | .dsym v => v != (⊤ : ℕ∞)
  | _ => true

private def flatFin_cc2 (l : List Sym) : Bool := l.all symFin_cc2

private theorem flatFin_append_cc2 (a b : List Sym) :
    flatFin_cc2 (a ++ b) = (flatFin_cc2 a && flatFin_cc2 b) := by
  simp only [flatFin_cc2, List.all_append]

private theorem flatFin_cons_cc2 (x : Sym) (l : List Sym) :
    flatFin_cc2 (x :: l) = (symFin_cc2 x && flatFin_cc2 l) := by
  simp only [flatFin_cc2, List.all_cons]

mutual
  private theorem dfree_flat_BT_cc2 : ∀ t : BT, dfree_BT t = flatFin_cc2 (flatBT t)
    | .trm [] => by rfl
    | .trm [p] => by
        show (dfree_BP p && dfree_BPList []) = flatFin_cc2 (flatBP p)
        rw [dfree_flat_BP_cc2 p]; simp [dfree_BPList]
    | .trm (p :: q :: ps) => by
        show (dfree_BP p && dfree_BPList (q :: ps))
            = flatFin_cc2 (Sym.lp :: (flatBP p ++ flatBPTail (q :: ps)) ++ [Sym.rp])
        rw [flatFin_append_cc2, flatFin_cons_cc2, flatFin_append_cc2,
          dfree_flat_BP_cc2 p, dfree_flat_BPTail_cc2 (q :: ps)]
        simp [symFin_cc2, flatFin_cc2]
  private theorem dfree_flat_BP_cc2 : ∀ p : BP, dfree_BP p = flatFin_cc2 (flatBP p)
    | .db u a => by
        show ((u != (⊤ : ℕ∞)) && dfree_BT a) = flatFin_cc2 (Sym.dsym u :: flatBT a)
        rw [flatFin_cons_cc2, dfree_flat_BT_cc2 a]; rfl
  private theorem dfree_flat_BPTail_cc2 : ∀ ps : List BP, dfree_BPList ps = flatFin_cc2 (flatBPTail ps)
    | [] => by rfl
    | p :: ps => by
        show (dfree_BP p && dfree_BPList ps) = flatFin_cc2 (Sym.cm :: flatBP p ++ flatBPTail ps)
        rw [flatFin_append_cc2, flatFin_cons_cc2, dfree_flat_BP_cc2 p, dfree_flat_BPTail_cc2 ps]
        simp [symFin_cc2]
end

private theorem mem_T_B_iff_flatFin_cc2 (t : BT) : t ∈ T_B ↔ flatFin_cc2 (flatBT t) = true := by
  show dfree_BT t = true ↔ flatFin_cc2 (flatBT t) = true
  rw [dfree_flat_BT_cc2 t]

private theorem flatFin_ins_mid_cc2 {s mid b : List Sym} {v : ℕ∞}
    (h : flatFin_cc2 (s ++ Sym.dsym v :: mid ++ b) = true) : flatFin_cc2 mid = true := by
  rw [flatFin_append_cc2, flatFin_append_cc2, flatFin_cons_cc2] at h
  have h1 := ((Bool.and_eq_true _ _).mp h).1
  have h2 := ((Bool.and_eq_true _ _).mp h1).2
  exact ((Bool.and_eq_true _ _).mp h2).2

/-- `dfree_BT body` from `Trans M ∈ OT_B` + `hk1` (assembly private `body_dfree_sa` twin). -/
private theorem body_dfree_cc2 {M : PS} {body : BT} {e3 : ℕ} {s1 b1 : List Sym}
    (hOT : Trans M ∈ OT_B)
    (hk1 : scb_kind1 (Trans M) s1 (flatBT (Dprin (e3 : ℕ∞) body)) b1) :
    dfree_BT body = true := by
  have hTB : Trans M ∈ T_B := hOT.2
  have hfin : flatFin_cc2 (flatBT (Trans M)) = true := (mem_T_B_iff_flatFin_cc2 _).mp hTB
  have hbf : flatBT (Dprin (e3 : ℕ∞) body) = Sym.dsym (e3 : ℕ∞) :: flatBT body := rfl
  rw [hk1.1.1, hbf] at hfin
  have : flatFin_cc2 (flatBT body) = true := flatFin_ins_mid_cc2 hfin
  exact (mem_T_B_iff_flatFin_cc2 _).mpr this

/-- `isOT_BP (D_{e₃} body)` (assembly private `otp_e3_body_sa` twin, via `OT_scb_recursive`). -/
private theorem otp_e3_body_cc2 {M : PS} {body : BT} {e3 : ℕ} {s1 b1 : List Sym}
    (hOT : Trans M ∈ OT_B)
    (hk1 : scb_kind1 (Trans M) s1 (flatBT (Dprin (e3 : ℕ∞) body)) b1) :
    isOT_BP (BP.db (e3 : ℕ∞) body) = true := by
  have dfb : dfree_BT body = true := body_dfree_cc2 hOT hk1
  have hcTB : Dprin (e3 : ℕ∞) body ∈ T_B := by
    show dfree_BT (Dprin (e3 : ℕ∞) body) = true
    simp [Dprin, dfree_BT, dfree_BPList, dfree_BP, dfb]
  have hcOT : Dprin (e3 : ℕ∞) body ∈ OT :=
    OT_scb_recursive (Trans M) (Dprin (e3 : ℕ∞) body) s1 b1 hOT hcTB hk1.1
  have h' : isOT_BT (Dprin (e3 : ℕ∞) body) = true := hcOT
  simpa [Dprin, isOT_BT, isOT_BPList, descP] using h'

private theorem rightNodes_Dprin_cc2 (e3 : ℕ) (body : BT) :
    RightNodes (Dprin (e3 : ℕ∞) body) = e3 :: RightNodes body := by
  show rightNodesList [BP.db (e3 : ℕ∞) body] = e3 :: RightNodes body
  show ((e3 : ℕ∞).toNat) :: RightNodes body = e3 :: RightNodes body
  simp

private theorem kind1_tail_gt_cc2 {e3 : ℕ} {RNb : List ℕ}
    (h2 : e3 < (e3 :: RNb).getD ((e3 :: RNb).length - 1) 0)
    (h3 : ∀ j, 0 < j → j < (e3 :: RNb).length - 1 →
            (e3 :: RNb).getD ((e3 :: RNb).length - 1) 0 ≤ (e3 :: RNb).getD j 0) :
    ∀ x ∈ RNb, e3 < x := by
  set r := e3 :: RNb with hr
  have hlen : r.length = RNb.length + 1 := by rw [hr]; simp
  have key : ∀ j, 1 ≤ j → j < r.length → e3 < r.getD j 0 := by
    intro j hj1 hjlt
    rcases Nat.lt_or_ge j (r.length - 1) with hlt | hge
    · exact lt_of_lt_of_le h2 (h3 j hj1 hlt)
    · have : j = r.length - 1 := by omega
      rw [this]; exact h2
  intro x hx
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
  have hb : i + 1 < r.length := by rw [hlen]; omega
  have hidx : r.getD (i + 1) 0 = x := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]
    show (e3 :: RNb)[i + 1] = x
    rw [List.getElem_cons_succ]; exact hxi
  have := key (i + 1) (by omega) hb
  rwa [hidx] at this

/-- `∀ x ∈ RightNodes body, e₃ < x` (assembly private `rightNodes_body_gt_e3_sa` twin). -/
private theorem rightNodes_body_gt_e3_cc2 {M : PS} {body : BT} {e3 : ℕ} {s1 b1 : List Sym}
    (hk1 : scb_kind1 (Trans M) s1 (flatBT (Dprin (e3 : ℕ∞) body)) b1) :
    ∀ x ∈ RightNodes body, e3 < x := by
  have hc : flatBT (Dprin (e3 : ℕ∞) body) = flatBP (BP.db (e3 : ℕ∞) body) := rfl
  have hcond := hk1.2 (BP.db (e3 : ℕ∞) body) hc
  have hRN : RightNodes (BT.trm [BP.db (e3 : ℕ∞) body]) = e3 :: RightNodes body :=
    rightNodes_Dprin_cc2 e3 body
  simp only [hRN] at hcond
  obtain ⟨_h1, h2, h3⟩ := hcond
  exact kind1_tail_gt_cc2 h2 h3

/-! ## 4. The restated census obligation `SetleCensusOx5_cc2` -/

/-- **The restated corner census obligation** (Isabelle `ox5_body_driver_census`,
`isabelle/layerC/pss_scratch.thy`:4974): the census body driver `ox5` itself.  This is the
FAITHFUL restatement of the setle-side census fact that the assembly actually consumes —
replacing the FALSE shared-wrapper existence of `SetleCensusWrapperCondIV_cp` (refuted at
the admeq corner, `«8».«8.7-corner-shape»`) with the `b1x_setle` conclusion the wrapper was
only ever used to produce.  Same hypothesis bundle as `OTintIIIIV_setleCensus`. -/
def SetleCensusOx5_cc2 : Prop :=
  ∀ (M : PS) (ins : BT → BT) (A0 body : BT) (e3 v1 : ℕ) (s0 b0 s1 b1 : List Sym),
    STPS M → monoT M = true → 1 < Lng M - 1 →
    (transCondIII M = true ∨ transCondIV M = true) →
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
    ∀ u : ℕ∞, b1x_setle (GBT u A0) (insert (ins BZero) (GBT u (ins BZero)))

/-! ## 5. `SetleCensusOx5_cc2` discharged UNCONDITIONALLY (corner + ltJ, uniform) -/

/-- **`SetleCensusOx5_cc2` holds — unconditionally.**  `censusPin_tc` pins
`A₀ = bpHeadT (Trans (Pred (s84x_N M)))`, `body`, `v₁`; then the already-unconditional
`tri0CruxConcrete_holds` supplies the G-control `b1x_triG (D_∞ 0_B) A₀ (ins 0_B)` (its
corner branch closes DIRECTLY, exactly where the wrapper route died), and
`ox5_body_driver_cc2` turns it + `base₁` into the census body driver.  No ltJ/corner split
is needed at this level — the `tri0` crux already handles both. -/
theorem setleCensusOx5_holds_cc2 : SetleCensusOx5_cc2 := by
  intro M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
    hflat hb0 hb1 hinner hk1 hmn _base0 base1'
  have hprov : SlicepkgMnformOut_sp M :=
    censusProvenance_holds_cp M hST hmono hp hj1 hcond
  obtain ⟨hv1, _he3, hbody, hA0⟩ :=
    censusPin_tc M ins A0 body e3 v1 s0 b0 s1 b1 hprov hOT hb1 hinner hk1 hmn
  subst hbody; subst hv1; subst hA0
  have tri0 : b1x_triG (Dprin (⊤ : ℕ∞) BZero) (bpHeadT (Trans (Pred (s84x_N M)))) (ins BZero) :=
    tri0CruxConcrete_holds M ins s0 b0 hST hmono hj1 hcond hp hb0 hflat hinner
  intro u
  exact ox5_body_driver_cc2 u tri0 base1'

#print axioms setleCensusOx5_holds_cc2

/-! ## 6. The setle consumer accepts `ox5` directly -/

/-- **The setle consumer, wrapper-free.**  Mirrors the built `otSetleCore_setle_holds`
(`«8».«8.7-otint-setle-assembly»`) but takes the census body driver `ox5` directly (from
`SetleCensusOx5_cc2`) instead of building it from a shared wrapper.  The KKraw geometry
(`otp`/`dfb`/`RNge`) is derived from the core's own `hOT`/`hk1`, `hv₁pos` from `censusPin_tc`
+ `s84c1_jm2_basic`, and the surgery transport from `SetleCensusSpine`; then
`ox10_SETLE1_close_oc` fires. -/
theorem otSetleCoreSetle_of_ox5_cc2 (hox5 : SetleCensusOx5_cc2) (hspine : SetleCensusSpine) :
    OTintIIIIV_otSetleCoreSetle := by
  intro M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
    hflat hb0 hb1 hinner hk1 hmn base0 base1'
  -- census body driver `ox5`, direct
  have ox5 : ∀ u : ℕ∞, b1x_setle (GBT u A0) (insert (ins BZero) (GBT u (ins BZero))) :=
    hox5 M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
      hflat hb0 hb1 hinner hk1 hmn base0 base1'
  -- `0 < v₁` from the census pin
  have hprov : SlicepkgMnformOut_sp M :=
    censusProvenance_holds_cp M hST hmono hp hj1 hcond
  obtain ⟨hv1, _, _, _⟩ :=
    censusPin_tc M ins A0 body e3 v1 s0 b0 s1 b1 hprov hOT hb1 hinner hk1 hmn
  have hv1pos : 0 < v1 := by
    rw [hv1]; have := (s84c1_jm2_basic M hp).2.1; omega
  -- KKraw geometry from the core's own hypotheses (`v₁ := e₃+1`)
  have otp : isOT_BP (BP.db (e3 : ℕ∞) body) = true := otp_e3_body_cc2 hOT hk1
  have dfb : dfree_BT body = true := body_dfree_cc2 hOT hk1
  have RNge : ∀ x ∈ RightNodes body, e3 + 1 ≤ x :=
    fun x hx => rightNodes_body_gt_e3_cc2 hk1 x hx
  have transp : SpineSurgeryTransport_kk body (ins BZero) :=
    hspine M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
      hflat hb0 hb1 hinner hk1 hmn base0 base1'
  have KKraw : ∀ k, 1 ≤ k → (∀ j, j < k → ox8_rsub body j ≠ BZero) →
      lessBT (ox8_rsub body k) (ins BZero) = true :=
    ox8_KKraw_kk otp (Nat.lt_succ_self e3) RNge dfb transp
  exact ox10_SETLE1_close_oc hflat hb0 hinner base1' hv1pos ox5 KKraw

#print axioms otSetleCoreSetle_of_ox5_cc2

/-! ## 7. Field reduction — `SetleCensusWrapperCondIV_cp` eliminated -/

/-- **`OTintIIIIV_otSetleCore` from the isOT side + the wrapper-free setle side.**  Combines
`OTintIIIIV_otSetleCoreA` (the `isOT_BT (ins A₀)` conjunct, via `isOT_A0_of_provenance`)
with `otSetleCoreSetle_of_ox5_cc2` (the `setle` conjunct). -/
theorem otSetleCore_of_ox5_spine_cc2 (hnub : A0OTNub) (hox5 : SetleCensusOx5_cc2)
    (hspine : SetleCensusSpine) : OTintIIIIV_otSetleCore := by
  intro M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
    hflat hb0 hb1 hinner hk1 hmn base0 base1'
  refine ⟨?_, ?_⟩
  · exact isOT_A0_of_provenance OixCoreTri_holds hnub
      (tri0Census_of_crux_tc censusProvenance_holds_cp tri0CruxConcrete_holds)
      M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
      hflat hb0 hb1 hinner hk1 hmn base0 base1'
  · exact otSetleCoreSetle_of_ox5_cc2 hox5 hspine
      M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
      hflat hb0 hb1 hinner hk1 hmn base0 base1'

#print axioms otSetleCore_of_ox5_spine_cc2

/-- **Field reduction (final).**  `OTintIIIIV_otSetleCore` reduces to just
`{A0OTNub, SetleCensusSpine}`: the census body driver (`SetleCensusOx5_cc2`) is discharged
unconditionally here, `CensusProvenance`/`Tri0CruxConcrete`/`OixCoreTri` are already
unconditional, and the FALSE `SetleCensusWrapperCondIV_cp` corner obligation is
**eliminated** — the corner census closes via the `tri0`-crux pivot, not a shared wrapper. -/
theorem otSetleCore_of_parts_cc2 (hnub : A0OTNub) (hspine : SetleCensusSpine) :
    OTintIIIIV_otSetleCore :=
  otSetleCore_of_ox5_spine_cc2 hnub setleCensusOx5_holds_cc2 hspine

#print axioms otSetleCore_of_parts_cc2

end PSS
