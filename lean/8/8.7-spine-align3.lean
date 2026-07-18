import «8».«8.7-otint-uncond»
import «8».«8.7-tri0-spine»
import «7».«7.3-Pred-Trans-descend»

/-!
# PSS.«8».«8.7-spine-align3» — the census surgery-TRANSPORT gap `ox7_align3_track`

Attacks the ONE genuinely-open census gap that `«8».«8.7-tri0-spine» exposes:
`SpineSurgeryTransportCensus_ts` — the census-instantiated `SpineSurgeryTransport_kk`
(`«8».«8.7-otint-kkraw»`) at the concrete census body/insertion.  移植元 (deferred on
the Isabelle side too): `ox7_align3_track` / the align3-peel STATUS §(7)
(`isabelle/layerC/pss_scratch.thy`:8589–8659; STEP-0 verdict-invariant 11306/11306,
faithful peel a future file).

## The transport in one line

`body = bpHeadT (Trans (s84x_N M))` and `ins 0_B` share a scb decomposition
`s₀ ⌢ flat (D_{v₁} 0) ⌢ b₀` (`b₀` all-`RP`), except `ins 0_B` LOWERS the shared
deepest-right leaf head `v₁ ⤳ v₁-1`.  `SpineSurgeryTransport_kk body (ins 0_B)` asks:
every right-spine sub-body `ox8_rsub body k` (`k ≥ 1`) that is `< body` is also
`< ins 0_B`.  This is a lock-step first-difference argument on the shared right spine.

## What lands here (green, `sorry` 0)

Bottom-up bricks + the vocabulary discharge, reducing the gap to ONE named residual:

1. **`ox9_holeD_of_flat2_sa3`** (Isabelle `ox9_holeD_of_flat3`, :10507): recover the
   deepest-right hole relation `ox9_holeD e (D_{v₁}0) (D_{v₁-1}0) body (ins 0_B)` from
   the two shared-`(s₀,b₀)` flat decompositions, via the built 3-slot alignment engine
   `OixAlign3_holds` (`«8».«8.7-otint-uncond»`).  This is the align3 spine peel.
2. **`ox8_rsub_eventually_zero_sa3`**: below the leaf hole (depth `> e`) the right-spine
   iterate collapses to `0_B` — so the transport is DISCHARGED unconditionally for `k > e`
   (`0_B < ins 0_B` since `ins 0_B ≠ 0_B`).  This peels off the below-hole regime.
3. **`spineSurgeryTransportCensus_of_core_sa3`**: the full wrapper, discharging every
   piece of census vocabulary (`s84x_N`, `Trans`, `bpHeadT`, the scb threading,
   condIII/IV, `hasParent`) and the below-hole regime, leaving the single residual
   `SpineAlign3PeelCore_sa3` — the `k ≤ e` first-difference peel over the ABSTRACT
   `ox9_holeD` relation.  That residual is exactly `ox7_align3_track`.
4. **`ox7_scbext_leBT_hole_sa3`** (Isabelle `ox7_scbext_leBT_hole`, :6180): the reusable
   `≤`-lex congruence at a shared right-spine hole (the `leBT` twin of `scbext_lessBT`).

## The remaining residual (`SpineAlign3PeelCore_sa3`)

The pure combinatorial core: for `ox9_holeD e (D_{v₁}0) (D_{v₁-1}0) WB ins0` and
`1 ≤ k ≤ e`, transport `lessBT (ox8_rsub WB k) WB` to `lessBT (ox8_rsub WB k) ins0`.
STEP-0 validates it (11306/11306); the faithful lock-step peel keeping the two sides
aligned at every shared `(qs,w,sc,bc)` is the deferred `ox7_align3_track`.

## Dependencies (built modules only, committed at b2a4380)
- `«8».«8.7-otint-uncond»`: `OixAlign3` / `OixAlign3_holds`.
- `«8».«8.7-tri0-spine»`: `SpineSurgeryTransportCensus_ts` (and transitively
  `SpineSurgeryTransport_kk`, `ox9_holeD`, `ox8_rsub`, the `ox9_*` eliminators).
- `«7».«7.3-Pred-Trans-descend»`: `scbext_lessBT` (and transitively `flatBT_injective`).

## Status
🤖 GREEN-MODULO (`sorry` 0, axioms = `[propext, Classical.choice, Quot.sound]`).
Private suffix `_sa3`.
-/

namespace PSS

/-! ## 0. `sizeOf` measure for the last-body recursion -/

/-- The last body of a `snoc` term is `sizeOf`-smaller than the whole term. -/
private theorem sizeOf_lastbody_lt_sa3 (qs : List BP) (w : ℕ∞) (lb : BT) :
    sizeOf lb < sizeOf (BT.trm (qs ++ [BP.db w lb])) := by
  have h1 : sizeOf (BP.db w lb) < sizeOf (qs ++ [BP.db w lb]) :=
    List.sizeOf_lt_of_mem (by simp)
  have h2 : sizeOf lb < sizeOf (BP.db w lb) := by
    simp only [BP.db.sizeOf_spec]; omega
  have h3 : sizeOf (BT.trm (qs ++ [BP.db w lb])) = 1 + sizeOf (qs ++ [BP.db w lb]) := by
    simp [BT.trm.sizeOf_spec]
  omega

/-! ## 1. Recover the deepest-right hole relation from the shared flat decomposition
       (Isabelle `ox9_holeD_of_flat3`, `pss_scratch.thy`:10507 — the align3 spine peel) -/

/-- Isabelle `ox9_holeD_of_flat3` (2-slot form).  Two trees `t`, `t1` whose flats share
the scb wrapper `(s,b)` (`b` all-`RP`) and carry principals `p`, `q` at the hole are
related by `ox9_holeD e p q t t1` for some right-spine depth `e`.  Derived by iterating
the built 3-slot alignment engine `OixAlign3` (feeding the third slot `= t1`) down the
right spine, `sizeOf`-terminating. -/
private theorem ox9_holeD_of_flat2_sa3 (halign : OixAlign3) :
    ∀ (n : ℕ) (t t1 : BT) (s b : List Sym) (p q : BP),
      sizeOf t ≤ n →
      flatBT t = s ++ flatBP p ++ b →
      flatBT t1 = s ++ flatBP q ++ b →
      (∀ x ∈ b, x = .rp) →
      ∃ e, ox9_holeD e p q t t1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro t t1 s b p q hsz e1 e2 hb
    rcases halign t t1 t1 s b p q q e1 e2 e2 hb with
      ⟨qs, ht, ht1, _⟩ | ⟨qs, w, lb1, lb2, _lb3, sc, bc, ht, ht1, _, F1, F2, _, hbc⟩
    · refine ⟨0, ?_⟩
      rw [ht, ht1]; exact ox9_holeD.hD0 qs p q
    · have hszlt : sizeOf lb1 < sizeOf t := by
        rw [ht]; exact sizeOf_lastbody_lt_sa3 qs w lb1
      obtain ⟨ed, hed⟩ :=
        IH (sizeOf lb1) (by omega) lb1 lb2 sc bc p q (le_refl _) F1 F2 hbc
      refine ⟨ed + 1, ?_⟩
      rw [ht, ht1]; exact ox9_holeD.hDS ed qs w p q lb1 lb2 hed

/-! ## 2. Below the leaf hole the right spine collapses to `0_B` -/

/-- The right side of a hole relation is nonzero (mirror of `ox9_holeD_ne_ox`). -/
private theorem ox9_holeD_ne_right_sa3 {e : ℕ} {p q : BP} {t t' : BT}
    (h : ox9_holeD e p q t t') : t' ≠ BZero := by
  cases h with
  | hD0 ps p q => simp [BZero]
  | hDS k ps w p q b b' hb => simp [BZero]

/-- Nothing but `0_B` is `≤ 0_B`; conversely `0_B < t` for any nonzero `t`. -/
private theorem lessBT_BZero_left_sa3 {t : BT} (hne : t ≠ BZero) : lessBT BZero t = true := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => exact absurd rfl hne
  | cons a as => simp [lessBT, BZero, lessBPList]

/-- Below the leaf hole `D_{v₁} 0_B` (right-spine depth `e`), every deeper right-spine
iterate of `WB` is `0_B`: at depth `e` the last principal's body is `0_B`, so `ox8_lastT`
bottoms out.  (The leaf is what makes the below-hole regime trivial.) -/
private theorem ox8_rsub_eventually_zero_sa3 {v1 : ℕ∞} {q : BP} {e : ℕ} {WB ins0 : BT}
    (hd : ox9_holeD e (.db v1 BZero) q WB ins0) :
    ∀ k, e < k → ox8_rsub WB k = BZero := by
  have h0 := ox9_holeD_rsub_ox e hd (le_refl e)
  rw [Nat.sub_self] at h0
  obtain ⟨ps, hWBe, _⟩ := ox9_holeD_0E_ox h0
  have hlast : ox8_lastT (ox8_rsub WB e) = BZero := by
    rw [hWBe, ox8_lastT_snoc_ox]
  have hSe : ox8_rsub WB (e + 1) = BZero := by
    rw [ox9_rsub_Suc_ox, hlast]
  have key : ∀ j, ox8_rsub WB (e + 1 + j) = BZero := by
    intro j
    induction j with
    | zero => simpa using hSe
    | succ j ih =>
        have step : ox8_rsub WB (e + 1 + (j + 1)) = ox8_lastT (ox8_rsub WB (e + 1 + j)) := by
          rw [show e + 1 + (j + 1) = (e + 1 + j) + 1 by omega, ox9_rsub_Suc_ox]
        rw [step, ih]; rfl
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = e + 1 + j := ⟨k - (e + 1), by omega⟩
  exact key j

/-! ## 3. The residual: the `k ≤ e` first-difference peel (`ox7_align3_track`) -/

/-- **The one genuinely-open census gap** — Isabelle `ox7_align3_track` / the align3-peel
STATUS §(7).  Over the abstract deepest-right hole relation
`ox9_holeD e (D_{v₁}0) (D_{v₁-1}0) WB ins0`, the census surgery-transport for the
`k ≤ e` (above-and-at-the-hole) regime: a right-spine sub-body `ox8_rsub WB k` that is
`< WB` is also `< ins0` (the lowered tree).  Empirically verdict-invariant (STEP-0,
11306/11306); the faithful lock-step first-difference peel keeping the two sides aligned
at every shared `(qs,w,sc,bc)` is deferred (Isabelle-side too). -/
def SpineAlign3PeelCore_sa3 : Prop :=
  ∀ (e v1 : ℕ) (WB ins0 : BT),
    ox9_holeD e (.db (v1 : ℕ∞) BZero) (.db ((v1 - 1 : ℕ) : ℕ∞) BZero) WB ins0 →
    ∀ k, 1 ≤ k → k ≤ e →
      lessBT (ox8_rsub WB k) WB = true → lessBT (ox8_rsub WB k) ins0 = true

/-- The flat-level transport: from the two shared-wrapper flat decompositions (`WB` with
the leaf hole `D_{v₁}0`, `ins0` with the lowered leaf `D_{v₁-1}0`), the residual
`SpineAlign3PeelCore_sa3` (for `k ≤ e`) plus the below-hole collapse (for `k > e`)
transport `lessBT (ox8_rsub WB k) WB` to `lessBT (ox8_rsub WB k) ins0`. -/
private theorem spineFlatTransport_of_core_sa3 (hcore : SpineAlign3PeelCore_sa3)
    (WB ins0 : BT) (s0 b0 : List Sym) (v1 : ℕ)
    (fWB : flatBT WB = s0 ++ flatBP (.db (v1 : ℕ∞) BZero) ++ b0)
    (fins : flatBT ins0 = s0 ++ flatBP (.db ((v1 - 1 : ℕ) : ℕ∞) BZero) ++ b0)
    (hb0 : ∀ x ∈ b0, x = .rp) :
    ∀ k, 1 ≤ k → lessBT (ox8_rsub WB k) WB = true → lessBT (ox8_rsub WB k) ins0 = true := by
  obtain ⟨e, hd⟩ := ox9_holeD_of_flat2_sa3 OixAlign3_holds (sizeOf WB) WB ins0 s0 b0
    (.db (v1 : ℕ∞) BZero) (.db ((v1 - 1 : ℕ) : ℕ∞) BZero) (le_refl _) fWB fins hb0
  intro k hk hlt
  by_cases hke : k ≤ e
  · exact hcore e v1 WB ins0 hd k hk hke hlt
  · have hz : ox8_rsub WB k = BZero := ox8_rsub_eventually_zero_sa3 hd k (by omega)
    rw [hz]
    exact lessBT_BZero_left_sa3 (ox9_holeD_ne_right_sa3 hd)

/-! ## 4. Full wrapper: discharge the census vocabulary, leaving one residual -/

/-- **`SpineSurgeryTransportCensus_ts` from the single residual.**  Discharges all census
vocabulary (`s84x_N`, `Trans`, `bpHeadT`, the scb threading, condIII/IV, `hasParent`) and
the below-hole regime; the only remaining input is `SpineAlign3PeelCore_sa3`
(`= ox7_align3_track`). -/
theorem spineSurgeryTransportCensus_of_core_sa3 (hcore : SpineAlign3PeelCore_sa3) :
    SpineSurgeryTransportCensus_ts := by
  intro M ins s0 b0 _hST _hmono _hj1 _hcond _hp hb0 hflat hinner
  set v1 : ℕ := entry M 1 (Lng M - 1) with hv1
  have fWB : flatBT (bpHeadT (Trans (s84x_N M)))
      = s0 ++ flatBP (.db (v1 : ℕ∞) BZero) ++ b0 := hinner.1
  have fins : flatBT (ins BZero)
      = s0 ++ flatBP (.db ((v1 - 1 : ℕ) : ℕ∞) BZero) ++ b0 := by
    have h := hflat BZero
    rw [h]; simp only [flatBP]
  intro k hk hlt
  exact spineFlatTransport_of_core_sa3 hcore (bpHeadT (Trans (s84x_N M))) (ins BZero)
    s0 b0 v1 fWB fins hb0 k hk hlt

#print axioms spineSurgeryTransportCensus_of_core_sa3

/-! ## 5. Reusable brick: `≤`-lex congruence at a shared right-spine hole -/

/-- Isabelle `ox7_scbext_leBT_hole` (`pss_scratch.thy`:6180): if `t`, `t'` share the scb
wrapper `(s,b)` (`b` all-`RP`) and differ only at a same-head hole principal `D_w a₁`
resp. `D_w a₂`, then `a₁ ≤ a₂ ⟹ t ≤ t'`.  The `leBT` twin of `scbext_lessBT` (strict
half) and `flatBT_injective` (equality half) — the reusable localized-hole lex step. -/
theorem ox7_scbext_leBT_hole_sa3 {t t' : BT} {s b : List Sym} {w : ℕ∞} {a1 a2 : BT}
    (fa : flatBT t = s ++ flatBP (.db w a1) ++ b)
    (fb : flatBT t' = s ++ flatBP (.db w a2) ++ b)
    (bRP : ∀ x ∈ b, x = .rp)
    (le : leBT a1 a2 = true) :
    leBT t t' = true := by
  simp only [leBT, Bool.or_eq_true] at le
  rcases le with hlt | heq
  · have hlp : lessBP (.db w a1) (.db w a2) = true := by simp [lessBP, hlt]
    have hh := scbext_lessBT fa fb bRP hlp
    simp [leBT, hh]
  · have ha : a1 = a2 := eq_of_beq heq
    subst ha
    have hft : flatBT t = flatBT t' := by rw [fa, fb]
    have : t = t' := flatBT_injective hft
    subst this; simp [leBT]

#print axioms ox7_scbext_leBT_hole_sa3

end PSS
