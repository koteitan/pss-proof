import «8».«8.7-otint-setle»
import «8».«8.7-otint-ox-close»
import «8».«8.7-otint-ox5-census»
import «8».«8.7-otint-kkraw»
import «8».«8.7-otint-a0ot»

/-!
# §8.7 SETLE1 assembly — wiring the census pieces into `OTintIIIIV_otSetleCore`

The BUILT `«8».«8.7-otint-setle»` states the atomic residual
`OTintIIIIV_otSetleCore`, whose conclusion is the conjunction

  `isOT_BT (ins A₀) = true  ∧  (∀ u, b1x_setle (Gᵤ (ins A₀)) (insert (ins 0_B) (Gᵤ (ins 0_B))))`.

Its **first** conjunct (`isOT_BT (ins A₀)`) is mapped by the BUILT
`«8».«8.7-otint-a0ot»` to the three deep census leaves `OixCoreTri` / `A0OTNub` /
`Tri0Census` (`isOT_A0_of_provenance`).  This file discharges its **second**
conjunct — the SETLE1 `setle` — by wiring the three built census engines:

- `ox5_census_x5` (`«8».«8.7-otint-ox5-census»`): the census body driver
  `∀ u, b1x_setle (Gᵤ A₀) (insert X₁ (Gᵤ X₁))` from the wrapper data
  `fA0`/`fX1`/`bRP` and `base₁` (Isabelle `ox5_body_driver_census`, :4974).
- `ox8_KKraw_kk` (`«8».«8.7-otint-kkraw»`): the raw right-spine bound `KKraw`
  from `otp`/`e3lt`/`RNge`/`dfb` plus the surgery transport residual
  `SpineSurgeryTransport_kk` (Isabelle `ox8_body_rspine_lessBT`, :8539 + STATUS §7).
- `ox10_SETLE1_close_oc` (`«8».«8.7-otint-ox-close»`): fires the right-spine
  descent engine on `ox5`/`KKraw`/`hv1pos` to produce the exact `setle` conjunct
  (Isabelle `ox10_SETLE1_ltJ`, :10995).

## What lands vs. what is a NEED

Everything that is discharged is discharged from the **core's own hypotheses**:
`base₁ = base1'`, and the KKraw geometry `otp` (`isOT_BP (D_{e₃} body)`, via
`OT_scb_recursive`), `dfb` (`dfree_BT body`, via the flat-fin characterisation),
`e3lt`/`RNge` (`e₃ < v₁` and `v₁ ≤` every right node of `body`, both from the
`scb_kind1` head inequalities of `hk1` with `v₁ := e₃+1`) are all derived here.

The residual `OTintIIIIV_setleCensus` bundles the setle-side census facts that are
NOT visible in the abstract core interface (each an Isabelle census leaf):
  * `hv1pos : 0 < v₁` (Isabelle `ublt` / `oi5_regime`),
  * the `ox5` wrapper `∃ s b tv t₂ c', fA0 ∧ fX1 ∧ bRP` (Isabelle `oi5_IIIIV_pkg`
    / `crx_base1_of_nest`; the census right-spine peel of `A₀ = bpHeadT(Trans(Pred
    (s84x_N N)))` vs. `ins 0_B` at a shared deeper wrapper — cannot be the given
    `(s₀,b₀)`, since that would force `A₀ = ins 0_B`, contradicting `base1'`),
  * `SpineSurgeryTransport_kk body (ins 0_B)` (Isabelle STATUS §7, verdict-invariant
    on 11306/11306 — the one genuinely open census gap).

## Results (`sorry` 0, axioms `[propext, Classical.choice, Quot.sound]`)

- `otSetleCore_setle_holds : OTintIIIIV_setleCensus → OTintIIIIV_otSetleCoreSetle`
  (the setle conjunct under the core's hypotheses).
- `otSetleCore_of_parts : OTintIIIIV_otSetleCoreA → OTintIIIIV_setleCensus →
  OTintIIIIV_otSetleCore` (glue with the a0ot isOT side).
- `otSetleCore_of_leaves : OixCoreTri → A0OTNub → Tri0Census →
  OTintIIIIV_setleCensus → OTintIIIIV_otSetleCore` — the field reduces to the three
  a0ot leaves plus the one setle census residual.

private suffix `_sa`.
-/

namespace PSS

/-! ## 1. flat-dfree characterisation (private twin of `«8».«8.7-otint-setle»`) -/

private def symFin_sa : Sym → Bool
  | .dsym v => v != (⊤ : ℕ∞)
  | _ => true

private def flatFin_sa (l : List Sym) : Bool := l.all symFin_sa

private theorem flatFin_append_sa (a b : List Sym) :
    flatFin_sa (a ++ b) = (flatFin_sa a && flatFin_sa b) := by
  simp only [flatFin_sa, List.all_append]

private theorem flatFin_cons_sa (x : Sym) (l : List Sym) :
    flatFin_sa (x :: l) = (symFin_sa x && flatFin_sa l) := by
  simp only [flatFin_sa, List.all_cons]

mutual
  private theorem dfree_flat_BT_sa : ∀ t : BT, dfree_BT t = flatFin_sa (flatBT t)
    | .trm [] => by rfl
    | .trm [p] => by
        show (dfree_BP p && dfree_BPList []) = flatFin_sa (flatBP p)
        rw [dfree_flat_BP_sa p]; simp [dfree_BPList]
    | .trm (p :: q :: ps) => by
        show (dfree_BP p && dfree_BPList (q :: ps))
            = flatFin_sa (Sym.lp :: (flatBP p ++ flatBPTail (q :: ps)) ++ [Sym.rp])
        rw [flatFin_append_sa, flatFin_cons_sa, flatFin_append_sa,
          dfree_flat_BP_sa p, dfree_flat_BPTail_sa (q :: ps)]
        simp [symFin_sa, flatFin_sa]
  private theorem dfree_flat_BP_sa : ∀ p : BP, dfree_BP p = flatFin_sa (flatBP p)
    | .db u a => by
        show ((u != (⊤ : ℕ∞)) && dfree_BT a) = flatFin_sa (Sym.dsym u :: flatBT a)
        rw [flatFin_cons_sa, dfree_flat_BT_sa a]; rfl
  private theorem dfree_flat_BPTail_sa : ∀ ps : List BP, dfree_BPList ps = flatFin_sa (flatBPTail ps)
    | [] => by rfl
    | p :: ps => by
        show (dfree_BP p && dfree_BPList ps) = flatFin_sa (Sym.cm :: flatBP p ++ flatBPTail ps)
        rw [flatFin_append_sa, flatFin_cons_sa, dfree_flat_BP_sa p, dfree_flat_BPTail_sa ps]
        simp [symFin_sa]
end

private theorem mem_T_B_iff_flatFin_sa (t : BT) : t ∈ T_B ↔ flatFin_sa (flatBT t) = true := by
  show dfree_BT t = true ↔ flatFin_sa (flatBT t) = true
  rw [dfree_flat_BT_sa t]

/-- `flatFin_sa (s ++ Dsym v :: mid ++ b)` から中身 `mid` の fin。 -/
private theorem flatFin_ins_mid_sa {s mid b : List Sym} {v : ℕ∞}
    (h : flatFin_sa (s ++ Sym.dsym v :: mid ++ b) = true) : flatFin_sa mid = true := by
  rw [flatFin_append_sa, flatFin_append_sa, flatFin_cons_sa] at h
  have h1 := ((Bool.and_eq_true _ _).mp h).1
  have h2 := ((Bool.and_eq_true _ _).mp h1).2
  exact ((Bool.and_eq_true _ _).mp h2).2

/-! ## 2. `dfb` / `otp` derived from `Trans M ∈ OT_B` + `hk1` -/

/-- `dfree_BT body`: `body`'s flat is a `Dsym`-guarded infix of the finite flat of
`Trans M ∈ T_B`. -/
private theorem body_dfree_sa {M : PS} {body : BT} {e3 : ℕ} {s1 b1 : List Sym}
    (hOT : Trans M ∈ OT_B)
    (hk1 : scb_kind1 (Trans M) s1 (flatBT (Dprin (e3 : ℕ∞) body)) b1) :
    dfree_BT body = true := by
  have hTB : Trans M ∈ T_B := hOT.2
  have hfin : flatFin_sa (flatBT (Trans M)) = true := (mem_T_B_iff_flatFin_sa _).mp hTB
  have hbf : flatBT (Dprin (e3 : ℕ∞) body) = Sym.dsym (e3 : ℕ∞) :: flatBT body := rfl
  rw [hk1.1.1, hbf] at hfin
  have : flatFin_sa (flatBT body) = true := flatFin_ins_mid_sa hfin
  exact (mem_T_B_iff_flatFin_sa _).mpr this

/-- `isOT_BP (D_{e₃} body)`: the scb core of `Trans M ∈ OT_B` is `OT` (Isabelle
`ox8_OTP_e3_body`, via `OT_scb_recursive`). -/
private theorem otp_e3_body_sa {M : PS} {body : BT} {e3 : ℕ} {s1 b1 : List Sym}
    (hOT : Trans M ∈ OT_B)
    (hk1 : scb_kind1 (Trans M) s1 (flatBT (Dprin (e3 : ℕ∞) body)) b1) :
    isOT_BP (BP.db (e3 : ℕ∞) body) = true := by
  have dfb : dfree_BT body = true := body_dfree_sa hOT hk1
  have hcTB : Dprin (e3 : ℕ∞) body ∈ T_B := by
    show dfree_BT (Dprin (e3 : ℕ∞) body) = true
    simp [Dprin, dfree_BT, dfree_BPList, dfree_BP, dfb]
  have hcOT : Dprin (e3 : ℕ∞) body ∈ OT :=
    OT_scb_recursive (Trans M) (Dprin (e3 : ℕ∞) body) s1 b1 hOT hcTB hk1.1
  have h' : isOT_BT (Dprin (e3 : ℕ∞) body) = true := hcOT
  simpa [Dprin, isOT_BT, isOT_BPList, descP] using h'

/-! ## 3. `e₃ < every right node of body` from the `scb_kind1` head order of `hk1` -/

private theorem rightNodes_Dprin_sa (e3 : ℕ) (body : BT) :
    RightNodes (Dprin (e3 : ℕ∞) body) = e3 :: RightNodes body := by
  show rightNodesList [BP.db (e3 : ℕ∞) body] = e3 :: RightNodes body
  show ((e3 : ℕ∞).toNat) :: RightNodes body = e3 :: RightNodes body
  simp

/-- From the `scb_kind1` head inequalities: every tail head is `> e₃`. -/
private theorem kind1_tail_gt_sa {e3 : ℕ} {RNb : List ℕ}
    (h2 : e3 < (e3 :: RNb).getD ((e3 :: RNb).length - 1) 0)
    (h3 : ∀ j, 0 < j → j < (e3 :: RNb).length - 1 →
            (e3 :: RNb).getD ((e3 :: RNb).length - 1) 0 ≤ (e3 :: RNb).getD j 0) :
    ∀ x ∈ RNb, e3 < x := by
  set r := e3 :: RNb with hr
  have hlen : r.length = RNb.length + 1 := by rw [hr]; simp
  -- the "last" entry `L` dominates the whole tail and is `> e₃`
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

/-- `∀ x ∈ RightNodes body, e₃ < x`, straight from the `scb_kind1` head order of `hk1`.
    (Isabelle: the `ox7`/`oi5_regime` head-order data, here derived abstractly.) -/
private theorem rightNodes_body_gt_e3_sa {M : PS} {body : BT} {e3 : ℕ} {s1 b1 : List Sym}
    (hk1 : scb_kind1 (Trans M) s1 (flatBT (Dprin (e3 : ℕ∞) body)) b1) :
    ∀ x ∈ RightNodes body, e3 < x := by
  have hc : flatBT (Dprin (e3 : ℕ∞) body) = flatBP (BP.db (e3 : ℕ∞) body) := rfl
  have hcond := hk1.2 (BP.db (e3 : ℕ∞) body) hc
  have hRN : RightNodes (BT.trm [BP.db (e3 : ℕ∞) body]) = e3 :: RightNodes body :=
    rightNodes_Dprin_sa e3 body
  simp only [hRN] at hcond
  obtain ⟨_h1, h2, h3⟩ := hcond
  exact kind1_tail_gt_sa h2 h3

/-! ## 4. The setle conjunct as a named Prop, and the setle-side census residual -/

/-- The **second** conjunct of `OTintIIIIV_otSetleCore` (SETLE1), under the identical
core hypothesis bundle (`«8».«8.7-otint-setle»`:56). -/
def OTintIIIIV_otSetleCoreSetle : Prop :=
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
    ∀ u : ℕ∞, b1x_setle (GBT u (ins A0)) (insert (ins BZero) (GBT u (ins BZero)))

/-- The setle-side census residual: the census facts about `A₀ = bpHeadT(Trans(Pred
(s84x_N N)))`, `body`, and the hole depth `v₁` that are NOT visible in the abstract
core interface.  Under the same hypothesis bundle it asserts:
  * `0 < v₁` (Isabelle `ublt`/`oi5_regime`),
  * the `ox5` wrapper of `A₀` vs. `ins 0_B` at a shared deeper wrapper `(s,b)`
    (Isabelle `oi5_IIIIV_pkg`/`crx_base1_of_nest`),
  * the surgery-transport `SpineSurgeryTransport_kk body (ins 0_B)` (Isabelle
    STATUS §7). -/
def OTintIIIIV_setleCensus : Prop :=
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
    (0 < v1)
    ∧ (∃ (s b : List Sym) (tv : ℕ∞) (t2 c' : BT),
         flatBT A0 = s ++ flatBP (BP.db tv t2) ++ b ∧
         flatBT (ins BZero) = s ++ flatBP (BP.db tv (addBT t2 c')) ++ b ∧
         (∀ x ∈ b, x = Sym.rp))
    ∧ SpineSurgeryTransport_kk body (ins BZero)

/-! ## 5. Assembly -/

/-- **SETLE1 assembly.**  From the setle census residual, derive the setle conjunct
of `OTintIIIIV_otSetleCore` under the core's own hypotheses: instantiate
`ox5_census_x5` (from the census wrapper), the KKraw engine `ox8_KKraw_kk` (with its
geometry `otp`/`dfb`/`e3lt`/`RNge` all derived from `hOT`/`hk1`, and `v₁ := e₃+1`),
and fire `ox10_SETLE1_close_oc`. -/
theorem otSetleCore_setle_holds (hcensus : OTintIIIIV_setleCensus) :
    OTintIIIIV_otSetleCoreSetle := by
  intro M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
    hflat hb0 hb1 hinner hk1 hmn base0 base1'
  obtain ⟨hv1pos, ⟨s, b, tv, t2, c', fA0, fX1, bRP⟩, transp⟩ :=
    hcensus M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
      hflat hb0 hb1 hinner hk1 hmn base0 base1'
  -- census body driver `ox5`
  have ox5 : ∀ u : ℕ∞, b1x_setle (GBT u A0) (insert (ins BZero) (GBT u (ins BZero))) :=
    ox5_census_x5 fA0 fX1 bRP base1'
  -- KKraw geometry, derived from the core's own hypotheses
  have otp : isOT_BP (BP.db (e3 : ℕ∞) body) = true := otp_e3_body_sa hOT hk1
  have dfb : dfree_BT body = true := body_dfree_sa hOT hk1
  have hRNgt : ∀ x ∈ RightNodes body, e3 < x := rightNodes_body_gt_e3_sa hk1
  have e3lt : e3 < e3 + 1 := Nat.lt_succ_self e3
  have RNge : ∀ x ∈ RightNodes body, e3 + 1 ≤ x := fun x hx => hRNgt x hx
  have KKraw : ∀ k, 1 ≤ k → (∀ j, j < k → ox8_rsub body j ≠ BZero) →
      lessBT (ox8_rsub body k) (ins BZero) = true :=
    ox8_KKraw_kk otp e3lt RNge dfb transp
  -- fire the right-spine descent engine
  exact ox10_SETLE1_close_oc hflat hb0 hinner base1' hv1pos ox5 KKraw

#print axioms otSetleCore_setle_holds

/-- **Glue.**  Combine the a0ot isOT side (`OTintIIIIV_otSetleCoreA`, whose
conclusion is exactly the first conjunct `isOT_BT (ins A₀)`) with the setle
assembly to reconstitute the full field `OTintIIIIV_otSetleCore`. -/
theorem otSetleCore_of_parts (ha : OTintIIIIV_otSetleCoreA) (hc : OTintIIIIV_setleCensus) :
    OTintIIIIV_otSetleCore := by
  intro M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
    hflat hb0 hb1 hinner hk1 hmn base0 base1'
  refine ⟨?_, ?_⟩
  · exact ha M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
      hflat hb0 hb1 hinner hk1 hmn base0 base1'
  · exact otSetleCore_setle_holds hc M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
      hflat hb0 hb1 hinner hk1 hmn base0 base1'

#print axioms otSetleCore_of_parts

/-- **Field reduction.**  `OTintIIIIV_otSetleCore` reduces to the three a0ot leaves
(`OixCoreTri` / `A0OTNub` / `Tri0Census`, mapping the isOT side) plus the single
setle-side census residual `OTintIIIIV_setleCensus`. -/
theorem otSetleCore_of_leaves (coreTri : OixCoreTri) (hnub : A0OTNub) (htri0 : Tri0Census)
    (hc : OTintIIIIV_setleCensus) : OTintIIIIV_otSetleCore :=
  otSetleCore_of_parts (isOT_A0_of_provenance coreTri hnub htri0) hc

#print axioms otSetleCore_of_leaves

end PSS
