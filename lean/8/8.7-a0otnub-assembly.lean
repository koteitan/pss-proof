import «8».«8.7-otint-a0ot-nub»
import «8».«8.7-a0ot-close»
import «8».«8.7-census-provenance»
import «8».«8.7-otint-tri0-census»
import «8».«8.7-tri0-dispatch»
import «8».«8.7-tri0-spine»
import «8».«8.7-wrapper-condiv»
import «Buchholz-1986».«Buchholz-1986-3.3»

/-!
# PSS.«8».«8.7-a0otnub-assembly» — `A0OTNub` UNCONDITIONAL (all four residuals supplied)

The BUILT `«8».«8.7-otint-a0ot-nub»` proved the narrowing

    `A0OTNub_of_residuals : NubGControl_an → A0OT_an → NubRegimeE3_an → Tri0Census → A0OTNub`

reducing the census brick `nub = isOT_BP (D_{v₁-1} A₀)` to four named legs.  Every one of
those legs is now suppliable, so this file lands `A0OTNub` **unconditionally** and threads
it into the `otSetleCore` composition.

The four legs:
* `NubGControl_an` — the last generic [Buc1] Lemma 3.4 `G`-control residual.  It is the
  **verbatim twin** of the public `OixGControl` (`«8».«8.7-otint-transport»`), discharged
  here from the public `G_control_bc`/`triGBC` (`«Buchholz-1986».«Buchholz-1986-3.3»`) exactly
  as `OixGControl_holds` (`«8».«8.7-otint-uncond»`) does — `b1x_triG` is defeq to `triGBC`.
* `A0OT_an` — the one-time census unknown `isOT_BT A₀`, closed by
  `A0OT_holds_ac censusProvenance_holds_cp` (`«8».«8.7-a0ot-close»` +
  `«8».«8.7-census-provenance»`).
* `NubRegimeE3_an` — the regime `e₃ ≤ v₁-1`, closed by
  `NubRegimeE3_holds_ac censusProvenance_holds_cp` (`«8».«8.7-a0ot-close»`).
* `Tri0Census` — closed by
  `tri0Census_of_crux_tc censusProvenance_holds_cp tri0CruxConcrete_holds`
  (`«8».«8.7-otint-tri0-census»` + `«8».«8.7-tri0-dispatch»`).

Composition (`otSetleCore_of_parts_wc`, `«8».«8.7-wrapper-condiv»`): with `A0OTNub` and the
unconditional `Tri0CruxConcrete` (`tri0CruxConcrete_holds`) both supplied here, and the
census `SetleCensusSpine` relocated to its true gap `SpineSurgeryTransportCensus_ts`
(`setleCensusSpine_of_census_ts censusProvenance_holds_cp`), `OTintIIIIV_otSetleCore`
reduces to **exactly two** remaining atoms:
  * `SpineSurgeryTransportCensus_ts` (Isabelle STATUS §(7) `ox7_align3_track`, the one open
    census surgery-transport gap), and
  * `SetleCensusWrapperCondIVCorner_wc` (the admeq corner shape-refinement residual).

Status: 🤖 GREEN (sorry 0, axioms = propext/Classical.choice/Quot.sound).
Remaining `otSetleCore` residuals = `{SpineSurgeryTransportCensus_ts,
SetleCensusWrapperCondIVCorner_wc}`.  Private suffix `_na2`.
-/

namespace PSS

/-! ## 1. `NubGControl_an` — the last generic [Buc1] Lemma 3.4 `G`-control residual -/

/-- **`NubGControl_an` discharged unconditionally.**  Verbatim twin of the public
`OixGControl` (`«8».«8.7-otint-transport»`); mirror of `OixGControl_holds`
(`«8».«8.7-otint-uncond»`).  `b1x_triG z b a` is defeq to `triGBC z b a`, so the public
Buchholz Lemma 3.4 `G_control_bc` (`«Buchholz-1986».«Buchholz-1986-3.3»`) closes it directly. -/
private theorem nubGControl_holds_na2 : NubGControl_an := by
  intro z b a u htri hba hGa hGz
  have htri' : triGBC z b a := htri
  exact G_control_bc htri' hba hGa hGz

/-! ## 2. `A0OTNub` unconditional -/

/-- **`A0OTNub` landed unconditionally** (Isabelle `ot1_nub_from_A0OT` with every leg
supplied).  Feeds the narrowing `A0OTNub_of_residuals` (`«8».«8.7-otint-a0ot-nub»`) with:
`nubGControl_holds_na2` (Lemma 3.4), `A0OT_holds_ac censusProvenance_holds_cp` (the census
unknown), `NubRegimeE3_holds_ac censusProvenance_holds_cp` (the regime), and
`tri0Census_of_crux_tc censusProvenance_holds_cp tri0CruxConcrete_holds` (the `tri0` leaf). -/
theorem a0otNub_holds : A0OTNub :=
  A0OTNub_of_residuals
    nubGControl_holds_na2
    (A0OT_holds_ac censusProvenance_holds_cp)
    (NubRegimeE3_holds_ac censusProvenance_holds_cp)
    (tri0Census_of_crux_tc censusProvenance_holds_cp tri0CruxConcrete_holds)

#print axioms a0otNub_holds

/-! ## 3. `otSetleCore` composition — reduced to the two true census gaps -/

/-- **`OTintIIIIV_otSetleCore` reduced to `{SpineSurgeryTransportCensus_ts,
SetleCensusWrapperCondIVCorner_wc}`.**  Threads the now-unconditional `a0otNub_holds` and
`tri0CruxConcrete_holds` into `otSetleCore_of_parts_wc` (`«8».«8.7-wrapper-condiv»`), and
relocates the census `SetleCensusSpine` to its concrete-body transport gap
`SpineSurgeryTransportCensus_ts` via `setleCensusSpine_of_census_ts censusProvenance_holds_cp`
(`«8».«8.7-tri0-spine»`).  The two hypotheses are exactly the remaining census residuals:
`SpineSurgeryTransportCensus_ts` (Isabelle `ox7_align3_track`) and the admeq corner shape
residual `SetleCensusWrapperCondIVCorner_wc`. -/
theorem otSetleCore_of_remaining_na2
    (hspine : SpineSurgeryTransportCensus_ts)
    (hcorner : SetleCensusWrapperCondIVCorner_wc) :
    OTintIIIIV_otSetleCore :=
  otSetleCore_of_parts_wc a0otNub_holds tri0CruxConcrete_holds
    (setleCensusSpine_of_census_ts censusProvenance_holds_cp hspine) hcorner

#print axioms otSetleCore_of_remaining_na2

end PSS
