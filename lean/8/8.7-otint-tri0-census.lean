import «8».«8.7-otint-census-leaves»
import «8».«8.4-exch84-slicepkg»
import «8».«8.4-s84x-vocab-run»
import «7».«7.2-scb-unique»

/-!
# PSS.«8».«8.7-otint-tri0-census» — attacking the `otSetleCore` census leaves

The BUILT `«8».«8.7-otint-census-leaves»` reduces the termination field
`otSetleCore` to the three census leaves via `otSetleCore_of_3leaves`:

  `A0OTNub → Tri0Census → OTintIIIIV_setleCensus → OTintIIIIV_otSetleCore`

(with `OixCoreTri` already unconditional).  Each leaf is an abstract `∀`-statement
over the binders `M ins A0 body e3 v1 s0 b0 s1 b1` whose hypothesis bundle PINS
those binders — via `scb_kind1`/`scb_decomp` uniqueness — to the *concrete census
provenance* that the abstract interface deliberately hides:

  `body = bpHeadT (Trans (s84x_N M))`,  `A0 = bpHeadT (Trans (Pred (s84x_N M)))`,
  `e3 = M_{1,j₋₃}`,  `v1 = M_{1,Lng M-1}`.

This file supplies that pinning (`censusPin_tc`) by threading the concrete
provenance `SlicepkgMnformOut_sp M` (Isabelle `oi5_IIIIV_pkg`'s output; produced in
Lean by `Mnform_condIIIIV`/`Mnform_condIV_admeq_sp` via `mnform_of_residual`, and
concretely available modulo `cornerNpValue`), and uses it to make progress on the
two census leaves the mission targets.

## What lands (green, `sorry` 0)

* **`censusPin_tc`** — the abstract-to-concrete identification, from
  `scb_kind1_unique` (`«7».«7.2-scb-unique»`) + `flatBT_injective` +
  a `Dsym _ :: … :: Zsym`-centre RP-suffix pin (`centerZ_pin_tc`) + `hmn`-at-`m=1`.

* **`setleCensus_of_parts_tc`** — reduces `OTintIIIIV_setleCensus` to
  `CensusProvenance` + `SetleCensusWrapper` + `SetleCensusSpine`, **DISCHARGING the
  `0 < v₁` conjunct** (Isabelle `ublt`/`oi5_regime`): once `v₁ = M_{1,Lng M-1}` is
  pinned, `0 < v₁` is immediate from `s84c1_jm2_basic`
  (`entry M 1 (s84x_jm2 M) < entry M 1 (Lng M-1)`).  The remaining `wrapper`
  (Isabelle `crx_base1_of_nest` `fA0'`/`fins2`) and `SpineSurgeryTransport_kk`
  conjuncts stay as named residuals.

* **`tri0Census_of_crux_tc`** — reduces the abstract `Tri0Census` leaf (Isabelle
  `ot1_tri0_census`, the condIII/IV mnform CRUX) to the **concrete**
  `Tri0CruxConcrete` residual (= Isabelle `oy1_tri0Y_census`: the `tri0` brick
  `b1x_triG (D_∞ 0_B) (bpHeadT (Trans (Pred (s84x_N M)))) (ins 0_B)` at the census
  wrapper), threading the provenance.  The CRUX itself (`crx_tri0_of_nest` /
  `cnv_tri0_of_nest` = `scbext_triG` lift, the triG primitives for which are ported
  in `«8».«8.7-otint-ox5-census»`) is left as the concrete residual for a future
  port — its `dP`/`d2`/`d4c2` mnform decompositions come from `MnformBottomResidual`.

* **`otSetleCore_of_parts_tc`** — the field reduction combining the above:
  `otSetleCore` reduces to `{A0OTNub, CensusProvenance, Tri0CruxConcrete,
  SetleCensusWrapper, SetleCensusSpine}`, with `0 < v₁` discharged and `Tri0Census`
  relocated to its concrete Isabelle form.

## Dependencies (built modules only, committed at 39e6765)

- `«8».«8.7-otint-census-leaves»`: `Tri0Census` / `A0OTNub` / `OTintIIIIV_setleCensus`
  / `OTintIIIIV_otSetleCore` / `otSetleCore_of_3leaves` and (transitively)
  `SpineSurgeryTransport_kk`, `Dprin`, `scb_decomp`/`scb_kind1`, `coreTower_e34`,
  `bpHeadT`, `Trans`, `oper`, `flatBT`/`flatBP`, `b1x_triG`, …
- `«8».«8.4-exch84-slicepkg»`: `SlicepkgMnformOut_sp` (the concrete provenance).
- `«8».«8.4-s84x-vocab-run»`: `s84c1_jm2_basic`.
- `«7».«7.2-scb-unique»`: `scb_kind1_unique` (+ `flatBT_injective` via `PSS.Flat`).

## Status

🤖 GREEN-MODULO (`sorry` 0, axioms = `[propext, Classical.choice, Quot.sound]`).
Private suffix `_tc`.
-/

namespace PSS

/-! ## 1. RP-suffix pin (an all-`RP` suffix after a `Zsym`-ending prefix is maximal) -/

/-- Two all-`RP` *prefixes* followed by lists whose heads are `Zsym` (`≠ RP`)
coincide.  The reversed form of `centerZ_pin_tc`. -/
private theorem rp_prefix_pin_tc {r1 r2 rest1 rest2 : List Sym}
    (h : r1 ++ (Sym.zero :: rest1) = r2 ++ (Sym.zero :: rest2))
    (hr1 : ∀ x ∈ r1, x = Sym.rp) (hr2 : ∀ x ∈ r2, x = Sym.rp) :
    r1 = r2 ∧ rest1 = rest2 := by
  rcases List.append_eq_append_iff.mp h with ⟨m, hl, hb⟩ | ⟨m, hl, hb⟩
  · rcases m with _ | ⟨m0, mt⟩
    · simp only [List.append_nil, List.nil_append] at hl hb
      exact ⟨hl.symm, (List.cons.injEq _ _ _ _).mp hb |>.2⟩
    · exfalso
      have hm0 : m0 = Sym.rp := hr2 m0 (by rw [hl]; simp)
      have hz : Sym.zero = m0 := by simpa using congrArg List.head? hb
      rw [hm0] at hz; exact absurd hz (by decide)
  · rcases m with _ | ⟨m0, mt⟩
    · simp only [List.append_nil, List.nil_append] at hl hb
      exact ⟨hl, ((List.cons.injEq _ _ _ _).mp hb |>.2).symm⟩
    · exfalso
      have hm0 : m0 = Sym.rp := hr1 m0 (by rw [hl]; simp)
      have hz : Sym.zero = m0 := by simpa using congrArg List.head? hb
      rw [hm0] at hz; exact absurd hz (by decide)

/-- Two scb-style occurrences with a single-`Dsym`/`Zsym` centre and all-`RP` tails
pin the `Dsym` value, the prefix, and the tail.  (`flatBT (D_v 0_B) = [Dsym v, Zsym]`.) -/
private theorem centerZ_pin_tc {s0 s0' b0 b0' : List Sym} {w w' : Sym}
    (heq : s0 ++ (w :: Sym.zero :: []) ++ b0 = s0' ++ (w' :: Sym.zero :: []) ++ b0')
    (hb0 : ∀ x ∈ b0, x = Sym.rp) (hb0' : ∀ x ∈ b0', x = Sym.rp) :
    w = w' ∧ s0 = s0' ∧ b0 = b0' := by
  have hrev := congrArg List.reverse heq
  simp only [List.reverse_append, List.reverse_cons,
    List.nil_append, List.append_assoc, List.cons_append] at hrev
  have hr1 : ∀ x ∈ b0.reverse, x = Sym.rp := fun x hx => hb0 x (List.mem_reverse.mp hx)
  have hr2 : ∀ x ∈ b0'.reverse, x = Sym.rp := fun x hx => hb0' x (List.mem_reverse.mp hx)
  obtain ⟨hrr, hrest⟩ := rp_prefix_pin_tc hrev hr1 hr2
  have hbb : b0 = b0' := by have := congrArg List.reverse hrr; simpa using this
  have hww : w = w' := by simpa using ((List.cons.injEq _ _ _ _).mp hrest).1
  have hss : s0 = s0' := by
    have h2 : s0.reverse = s0'.reverse := ((List.cons.injEq _ _ _ _).mp hrest).2
    have := congrArg List.reverse h2; simpa using this
  exact ⟨hww, hss, hbb⟩

/-! ## 2. The census pinning: abstract binders = concrete provenance -/

/-- **Census pinning.**  Under the census-leaf hypotheses (`hOT`/`hinner`/`hk1`/`hmn`)
together with the concrete provenance `SlicepkgMnformOut_sp M`, the abstract binders
are identified with their census provenance:
`v₁ = M_{1,Lng M-1}`, `e₃ = M_{1,j₋₃}`, `body = bpHeadT (Trans (s84x_N M))`,
`A₀ = bpHeadT (Trans (Pred (s84x_N M)))`.

Route: `scb_kind1_unique` on `Trans M` pins `s₁`, `b₁`, and the outer hole (whence
`e₃` by `Nat.cast` injectivity and `body` by `flatBT_injective`); the inner hole is
pinned by the `Zsym`-centre RP-suffix lemma `centerZ_pin_tc` (whence `v₁`); and
`hmn` at `m = 1` (the depth-0 tower `coreTower_e34 ins A₀ 0 = A₀`) pins `A₀`. -/
theorem censusPin_tc (M : PS) (ins : BT → BT) (A0 body : BT) (e3 v1 : ℕ)
    (s0 b0 s1 b1 : List Sym)
    (hprov : SlicepkgMnformOut_sp M)
    (hOT : Trans M ∈ OT_B)
    (_hb1 : ∀ x ∈ b1, x = Sym.rp)
    (hinner : scb_decomp body s0 (flatBT (Dprin (v1 : ℕ∞) BZero)) b0)
    (hk1 : scb_kind1 (Trans M) s1 (flatBT (Dprin (e3 : ℕ∞) body)) b1)
    (hmn : ∀ m, 1 ≤ m → flatBT (Trans (oper M m))
        = s1 ++ flatBP (BP.db (e3 : ℕ∞) (coreTower_e34 ins A0 (m - 1))) ++ b1) :
    v1 = entry M 1 (Lng M - 1) ∧ e3 = entry M 1 (s84x_jm3 M)
      ∧ body = bpHeadT (Trans (s84x_N M))
      ∧ A0 = bpHeadT (Trans (Pred (s84x_N M))) := by
  obtain ⟨ins', s0', b0', s1', b1', hflat', hb0rp', hb1rp', hinner', hk1', hmn'⟩ := hprov
  have hTB : Trans M ∈ T_B := hOT.2
  have hbf : flatBT (Dprin (e3 : ℕ∞) body) = Sym.dsym (e3 : ℕ∞) :: flatBT body := rfl
  have hne : Trans M ≠ BZero := by
    intro hz
    have hlen := congrArg List.length hk1.1.1
    rw [hz, hbf, hinner.1] at hlen
    simp only [BZero, flatBT, flatBP, Dprin, List.length_cons, List.length_append,
      List.length_nil] at hlen
    omega
  -- (a) outer-hole pin via `scb_kind1_unique`
  have huniq := scb_kind1_unique hTB hne hk1 hk1'
  rw [Prod.mk.injEq, Prod.mk.injEq] at huniq
  obtain ⟨hs1, hc, hb1eq⟩ := huniq
  have hcc : Sym.dsym (e3 : ℕ∞) :: flatBT body
      = Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
          :: flatBT (bpHeadT (Trans (s84x_N M))) := by
    simpa [Dprin, flatBT, flatBP] using hc
  have he3 : e3 = entry M 1 (s84x_jm3 M) := by
    have h2 : (e3 : ℕ∞) = ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) := by
      simpa using ((List.cons.injEq _ _ _ _).mp hcc).1
    exact_mod_cast h2
  have hbody : body = bpHeadT (Trans (s84x_N M)) :=
    flatBT_injective ((List.cons.injEq _ _ _ _).mp hcc).2
  subst hbody
  -- (b) inner-hole pin via `centerZ_pin_tc`
  have hin1 : flatBT (bpHeadT (Trans (s84x_N M)))
      = s0 ++ (Sym.dsym (v1 : ℕ∞) :: Sym.zero :: []) ++ b0 := by
    simpa [Dprin, flatBT, flatBP, BZero] using hinner.1
  have hin2 : flatBT (bpHeadT (Trans (s84x_N M)))
      = s0' ++ (Sym.dsym ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) :: Sym.zero :: []) ++ b0' := by
    simpa [Dprin, flatBT, flatBP, BZero] using hinner'.1
  obtain ⟨hw, _hs0, _hb0eq⟩ := centerZ_pin_tc (hin1.symm.trans hin2) hinner.2.2 hinner'.2.2
  have hv1 : v1 = entry M 1 (Lng M - 1) := by
    have h2 : (v1 : ℕ∞) = ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) := by simpa using hw
    exact_mod_cast h2
  -- (c) `A₀` pin via `hmn`/`hmn'` at `m = 1`
  have hm1 : flatBT (Trans (oper M 1))
      = s1 ++ (Sym.dsym (e3 : ℕ∞) :: flatBT A0) ++ b1 := by
    simpa [coreTower_e34, flatBP] using hmn 1 (le_refl 1)
  have hm1' : flatBT (Trans (oper M 1))
      = s1' ++ (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
          :: flatBT (bpHeadT (Trans (Pred (s84x_N M))))) ++ b1' := by
    simpa [coreTower_e34, flatBP] using hmn' 1 (le_refl 1)
  have hmeq : s1 ++ (Sym.dsym (e3 : ℕ∞) :: flatBT A0) ++ b1
      = s1 ++ (Sym.dsym (e3 : ℕ∞)
          :: flatBT (bpHeadT (Trans (Pred (s84x_N M))))) ++ b1 := by
    rw [← hm1, hm1', hs1, hb1eq, he3]
  have hmid : (Sym.dsym (e3 : ℕ∞) :: flatBT A0)
      = (Sym.dsym (e3 : ℕ∞) :: flatBT (bpHeadT (Trans (Pred (s84x_N M))))) :=
    List.append_cancel_left (List.append_cancel_right hmeq)
  have hA0 : A0 = bpHeadT (Trans (Pred (s84x_N M))) :=
    flatBT_injective ((List.cons.injEq _ _ _ _).mp hmid).2
  exact ⟨hv1, he3, rfl, hA0⟩

#print axioms censusPin_tc

/-! ## 3. The threaded provenance and the residual census facts -/

/-- The concrete census provenance for a condIII/IV `hasParent` host: Isabelle
`oi5_IIIIV_pkg`'s `obtains` body (`SlicepkgMnformOut_sp`), produced in Lean by
`Mnform_condIIIIV`/`Mnform_condIV_admeq_sp` and concretely available (modulo the
single `cornerNpValue` atom) via the slicepkg assembly. -/
def CensusProvenance : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    SlicepkgMnformOut_sp M

/-- The setle-side census **wrapper** residual (Isabelle `crx_base1_of_nest`
`fA0'`/`fins2`): the shared deeper-wrapper decomposition of `A₀` vs. `ins 0_B`.
Same hypothesis bundle as `OTintIIIIV_setleCensus`. -/
def SetleCensusWrapper : Prop :=
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
    (∃ (s b : List Sym) (tv : ℕ∞) (t2 c' : BT),
       flatBT A0 = s ++ flatBP (BP.db tv t2) ++ b ∧
       flatBT (ins BZero) = s ++ flatBP (BP.db tv (addBT t2 c')) ++ b ∧
       (∀ x ∈ b, x = Sym.rp))

/-- The setle-side census **spine-transport** residual (Isabelle STATUS §7, the one
genuinely open census gap).  Same hypothesis bundle as `OTintIIIIV_setleCensus`. -/
def SetleCensusSpine : Prop :=
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
    SpineSurgeryTransport_kk body (ins BZero)

/-! ## 4. `OTintIIIIV_setleCensus`: the `0 < v₁` conjunct DISCHARGED -/

/-- **Setle census reduction (`0 < v₁` discharged).**  `OTintIIIIV_setleCensus`
follows from the provenance plus the wrapper and spine residuals.  The `0 < v₁`
conjunct (Isabelle `ublt`) is closed here: `censusPin_tc` gives
`v₁ = M_{1,Lng M-1}`, and `s84c1_jm2_basic` gives
`M_{1,j₋₂} < M_{1,Lng M-1}`, whence `0 < v₁`. -/
theorem setleCensus_of_parts_tc (hprov : CensusProvenance)
    (hwrap : SetleCensusWrapper) (hspine : SetleCensusSpine) :
    OTintIIIIV_setleCensus := by
  intro M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
    hflat hb0 hb1 hinner hk1 hmn base0 base1'
  obtain ⟨hv1, _, _, _⟩ := censusPin_tc M ins A0 body e3 v1 s0 b0 s1 b1
    (hprov M hST hmono hp hj1 hcond) hOT hb1 hinner hk1 hmn
  refine ⟨?_, ?_, ?_⟩
  · -- `0 < v₁`
    rw [hv1]
    have := (s84c1_jm2_basic M hp).2.1
    omega
  · exact hwrap M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
      hflat hb0 hb1 hinner hk1 hmn base0 base1'
  · exact hspine M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
      hflat hb0 hb1 hinner hk1 hmn base0 base1'

#print axioms setleCensus_of_parts_tc

/-! ## 5. `Tri0Census`: reduced to the concrete Isabelle `oy1_tri0Y_census` residual -/

/-- The concrete `tri0` census CRUX (Isabelle `oy1_tri0Y_census` /
`ot1_tri0_census`, `pss_scratch.thy`:4154/4081): the hole G-control brick
`b1x_triG (D_∞ 0_B) (bpHeadT (Trans (Pred (s84x_N M)))) (ins 0_B)` at the census
wrapper `(s₀,b₀)`.  Discharged in Isabelle by `crx_tri0_of_nest` (condIII) /
`cnv_tri0_of_nest` (condIV) — the `scbext_triG` lift of `ot1_triG_grow` through the
shared `fA0'`/`fins2` wrapper (triG primitives ported in `«8».«8.7-otint-ox5-census»`;
the `dP`/`d2`/`d4c2` mnform decompositions come from `MnformBottomResidual`). -/
def Tri0CruxConcrete : Prop :=
  ∀ (M : PS) (ins : BT → BT) (s0 b0 : List Sym),
    STPS M → monoT M = true → 1 < Lng M - 1 →
    (transCondIII M = true ∨ transCondIV M = true) →
    hasParent M 1 (Lng M - 1) = true →
    (∀ x ∈ b0, x = Sym.rp) →
    (∀ X, flatBT (ins X)
        = s0 ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT X ++ b0) →
    scb_decomp (bpHeadT (Trans (s84x_N M))) s0
      (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0 →
    b1x_triG (Dprin (⊤ : ℕ∞) BZero) (bpHeadT (Trans (Pred (s84x_N M)))) (ins BZero)

/-- **`Tri0Census` reduction.**  The abstract census leaf `Tri0Census` (Isabelle
`ot1_tri0_census`) reduces to the concrete residual `Tri0CruxConcrete` (=
`oy1_tri0Y_census`) plus the provenance.  `censusPin_tc` identifies
`body = bpHeadT (Trans (s84x_N M))`, `A₀ = bpHeadT (Trans (Pred (s84x_N M)))`, and
`v₁ = M_{1,Lng M-1}`, after which the abstract goal is exactly `Tri0CruxConcrete`
applied at the census's own `ins`/`s₀`/`b₀`. -/
theorem tri0Census_of_crux_tc (hprov : CensusProvenance) (hcrux : Tri0CruxConcrete) :
    Tri0Census := by
  intro M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
    hflat hb0 hb1 hinner hk1 hmn base0 base1'
  obtain ⟨hv1, _he3, hbody, hA0⟩ := censusPin_tc M ins A0 body e3 v1 s0 b0 s1 b1
    (hprov M hST hmono hp hj1 hcond) hOT hb1 hinner hk1 hmn
  subst hbody; subst hA0
  rw [hv1] at hflat hinner
  exact hcrux M ins s0 b0 hST hmono hj1 hcond hp hb0 hflat hinner

#print axioms tri0Census_of_crux_tc

/-! ## 6. Field reduction combining the census work -/

/-- **Field reduction.**  `OTintIIIIV_otSetleCore` reduces to
`{A0OTNub, CensusProvenance, Tri0CruxConcrete, SetleCensusWrapper, SetleCensusSpine}`
— with `OixCoreTri` already unconditional (`«8».«8.7-otint-census-leaves»`), the
`0 < v₁` census conjunct discharged, and the abstract `Tri0Census` leaf relocated to
its concrete Isabelle form `Tri0CruxConcrete`. -/
theorem otSetleCore_of_parts_tc (hnub : A0OTNub) (hprov : CensusProvenance)
    (hcrux : Tri0CruxConcrete) (hwrap : SetleCensusWrapper) (hspine : SetleCensusSpine) :
    OTintIIIIV_otSetleCore :=
  otSetleCore_of_3leaves hnub (tri0Census_of_crux_tc hprov hcrux)
    (setleCensus_of_parts_tc hprov hwrap hspine)

#print axioms otSetleCore_of_parts_tc

end PSS
