import «8».«8.7-otint-ox-engine»
import «8».«8.7-otint-uncond»

/-!
# §8.7 `ox` close — discharging `Ox10SETLE1Residual_ox` (census `SETLE1`)

The BUILT `«8».«8.7-otint-ox-engine»` landed the right-spine descent ENGINE
(`ox10_engine_ox` / `ox10_setle_from_engine_ox`) unconditionally, and reduced the
census top `ox10_SETLE1_ltJ` (`isabelle/layerC/pss_scratch.thy`:10995) to the named
5-input residual `Ox10SETLE1Residual_ox`.  This file assembles those 5 inputs for the
**concrete surgery triple** of the census, in the shape the built
`«8».«8.7-otint-setle»` core (`OTintIIIIV_otSetleCore`) expects, and fires the engine.

## The concrete surgery triple (setle core naming)

`ins X = d4vx_ins s0 (v1-1) b0 X`  (the census inserter; here abstracted by its flat
law `hflat`), `WB = body` (census body `bpHeadT (Trans (s84x_N N))`),
`A1 = ins A0`, `X1 = ins 0_B`, `pA = D_{v1-1} A0`, `pX = D_{v1-1} 0_B`, hole `= D_{v1} 0_B`.

## The 5 engine inputs and how each lands (移植元: pss_scratch.thy)

- **`pAlt`** `= lessBP (D_{v1-1} A0) (D_{v1} 0_B)`: **fully discharged** here from
  `ublt` (`v1-1 < v1`, i.e. `0 < v1`), via `pAlt_oc`.  Isabelle: `ublt`/`pAlt`
  (:11017–11018), `0 < v1` from `transCondIII/IV`.
- **`holeH`** `= b1x_setle (GBP u pA) (insert X1 (GBT u X1))`: reduced by the ported
  `ox6_holeH_oc` (Isabelle `ox6_holeH`, :5081) to the census body driver
  `ox5 : b1x_setle (GBT u A0) (insert X1 (GBT u X1))` (Isabelle `ox5_body_driver_census`,
  :4974) plus the setle-core hypothesis `base1 : lessBT A0 X1`.
- **`hdA`/`hdX`** `= ox9_holeD dR (D_{v1} 0_B) pA/pX WB A1/X1`: read off the three flat
  surgery strings (`wrap`/`fA1`/`fX1`, from the setle-core flat law `hflat` and the
  scb wrapper `hinner`) by the structural alignment `Ox9HoleDOfFlat3_oc` (Isabelle
  `ox9_holeD_of_flat3`, :10507 = the iterated `otx2_align3` right-spine peel — pure
  flat-string parsing, no census).  **Fully proved here** as `Ox9HoleDOfFlat3_holds_oc`
  by size-recursion over `OixAlign3_holds` (the built `otx2_align3` twin in
  `«8».«8.7-otint-uncond»`).  The `d4vx_ins_flat` step of the census is what produces
  `hflat`; at the setle-core interface it is `hflat` itself.
- **`KK`** `= ∀ j, 1 ≤ j → j ≤ dR → lessBT (ox8_rsub WB j) X1`: derived here from the
  raw census spine bound `KKraw` (Isabelle `KK` hyp of `ox10_SETLE1_ltJ`, i.e.
  `ox8_body_rspine_lessBT`, :8539 — census geometry, NEED) using the engine publics
  `ox9_holeD_rsub_ox` + `ox9_holeD_ne_ox` for the aliveness side-condition (exactly the
  Isabelle `KKd` derivation, :11061–11073).

## 状態
GREEN-MODULO.  `pAlt` fully proved; `holeH` ported; `hdA`/`hdX` **fully proved**
(`Ox9HoleDOfFlat3_holds_oc`); `KK` derived from the raw spine bound.  The bridge
`ox10_SETLE1_close_oc` produces the setle-core SETLE conjunct
`∀ u, b1x_setle (GBT u (ins A0)) (insert (ins 0_B) (GBT u (ins 0_B)))`.
Remaining NEEDs (pure census, none our own gap): `ox5` (`ox5_body_driver_census`,
:4974) and `KKraw` (`ox8_body_rspine_lessBT`, :8539), taken as bridge hypotheses.
private suffix `_oc`.
-/

namespace PSS

/-! ## helpers -/

private theorem leBT_of_lessBT_oc {a b : BT} (h : lessBT a b = true) : leBT a b = true := by
  simp [leBT, h]

/-! ## `pAlt`: fully discharged from `ublt` (`v1-1 < v1`) -/

/-- Isabelle `pAlt` (pss_scratch.thy:11018): `lessBP (D_{ub} A0) (D_{v1} 0_B)` from
    `ublt : ub < v1`.  The second disjunct (`ub = v1 ∧ A0 < 0_B`) is vacuous. -/
private theorem pAlt_oc {ub v1 : ℕ} {A0 : BT} (h : ub < v1) :
    lessBP (.db (ub : ℕ∞) A0) (.db (v1 : ℕ∞) BZero) = true := by
  have hlt : ((ub : ℕ∞)) < ((v1 : ℕ∞)) := by exact_mod_cast h
  simp only [lessBP, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inl hlt

/-! ## `holeH`: the ported `ox6_holeH` -/

/-- Isabelle `ox6_holeH` (pss_scratch.thy:5081): the hole principal `D_v A0`'s `G_u`
    escapes (`{A0} ∪ G_u A0`) are dominated by `{X1} ∪ G_u X1` — `A0` by
    `base1 : A0 < X1`, and `G_u A0` by the body driver `ox5`. -/
theorem ox6_holeH_oc {u v : ℕ∞} {A0 X1 : BT}
    (ox5 : b1x_setle (GBT u A0) (insert X1 (GBT u X1)))
    (base1 : lessBT A0 X1 = true) :
    b1x_setle (GBP u (.db v A0)) (insert X1 (GBT u X1)) := by
  intro x hx
  rw [mem_GBP_db_ox] at hx
  obtain ⟨_uv, xcase⟩ := hx
  rcases xcase with rfl | hxA0
  · exact ⟨X1, Set.mem_insert_iff.mpr (Or.inl rfl), leBT_of_lessBT_oc base1⟩
  · exact ox5 x hxA0

#print axioms ox6_holeH_oc

/-! ## `hdA`/`hdX`: reading `ox9_holeD` off the flat surgery -/

/-- Isabelle `ox9_holeD_of_flat3` (pss_scratch.thy:10507): the census flat-level
    surgery data (one body `t`, two replacements `q1,q2` at the SAME wrapper `(s,b)`,
    `b` all-`RP`) yields the two structural hole relations at the SAME depth `e`.

    Pure flat-string parsing (the iterated `otx2_align3` right-spine peel, layerB
    `pss_wip.thy`:114296) — no census.  Left as a NEED here: porting the `otx2_align3`
    alignment chain (`otx2_top_shape`/`otx2_peel`/`otx2_join3`/`otx2_BP_prefix`) is a
    self-contained future file. -/
def Ox9HoleDOfFlat3_oc : Prop :=
  ∀ (t t1 t2 : BT) (p q1 q2 : BP) (s b : List Sym),
    flatBT t = s ++ flatBP p ++ b →
    flatBT t1 = s ++ flatBP q1 ++ b →
    flatBT t2 = s ++ flatBP q2 ++ b →
    (∀ x ∈ b, x = Sym.rp) →
    ∃ e, ox9_holeD e p q1 t t1 ∧ ox9_holeD e p q2 t t2

/-- Isabelle `ox9_holeD_of_flat3` (pss_scratch.thy:10507) — **fully proved**.
    Size-recursion over the built `otx2_align3` twin `OixAlign3_holds`
    (`«8».«8.7-otint-uncond»`): the single-level 3-slot alignment classifies
    `(t, t1, t2)` at the shared hole into (A) all three carry the core as the last
    top-level principal over a shared prefix `qs` (→ `ox9_holeD.hD0`, depth `0`), or
    (B) all three descend through a shared last principal `D_w` into aligned bodies at
    a strictly-smaller sub-position (→ `ox9_holeD.hDS`, depth `e+1` from recursion). -/
theorem Ox9HoleDOfFlat3_holds_oc : Ox9HoleDOfFlat3_oc := by
  intro t t1 t2 p q1 q2 s b e1 e2 e3 bR
  generalize hn : sizeOf t = n
  induction n using Nat.strong_induction_on generalizing t t1 t2 s b with
  | _ n ih =>
    rcases OixAlign3_holds t t1 t2 s b p q1 q2 e1 e2 e3 bR with
      ⟨qs, ht, ht1, ht2⟩ | ⟨qs, w, lb1, lb2, lb3, sc, bc, ht, ht1, ht2, f1, f2, f3, hbc⟩
    · subst ht ht1 ht2
      exact ⟨0, ox9_holeD.hD0 qs p q1, ox9_holeD.hD0 qs p q2⟩
    · subst ht ht1 ht2
      have hlt : sizeOf lb1 < n := by
        have hmem : (BP.db w lb1) ∈ qs ++ [BP.db w lb1] := by simp
        have h1 := List.sizeOf_lt_of_mem hmem
        rw [← hn]
        simp only [BT.trm.sizeOf_spec, BP.db.sizeOf_spec] at h1 ⊢
        omega
      obtain ⟨e, hA, hX⟩ := ih (sizeOf lb1) hlt lb1 lb2 lb3 sc bc f1 f2 f3 hbc rfl
      exact ⟨e + 1, ox9_holeD.hDS e qs w p q1 lb1 lb2 hA,
                    ox9_holeD.hDS e qs w p q2 lb1 lb3 hX⟩

#print axioms Ox9HoleDOfFlat3_holds_oc

/-! ## The bridge: `Ox10SETLE1Residual_ox` assembled → the setle-core SETLE conjunct -/

/-- **Close.**  For the concrete census surgery triple (`ins`, `A0`, `body`, `v1`,
    `s0`, `b0`), assemble the 5 inputs of `Ox10SETLE1Residual_ox` and fire the engine
    (`ox10_setle_from_engine_ox`) to produce the `SETLE1` conclusion in the exact shape
    the built `«8».«8.7-otint-setle»` core (`OTintIIIIV_otSetleCore`) expects:

    `∀ u, b1x_setle (GBT u (ins A0)) (insert (ins 0_B) (GBT u (ins 0_B)))`.

    Hypotheses:
    * `hflat` / `hb0` / `hinner` / `base1` : the setle-core inputs (`ins`'s flat law,
      `b0` all-`RP`, the scb wrapper of `body`, and `A0 < ins 0_B`).
    * `hv1pos` : `0 < v1` (census `ublt`; `v1 = entry N 1 (Lng N - 1) > 0` from branch).
    * `ox5` : the census body driver NEED (`ox5_body_driver_census`).
    * `KKraw` : the raw census spine bound NEED (`ox8_body_rspine_lessBT`, the `KK`
      hypothesis of `ox10_SETLE1_ltJ`), with aliveness discharged internally. -/
theorem ox10_SETLE1_close_oc
    {ins : BT → BT} {A0 body : BT} {v1 : ℕ} {s0 b0 : List Sym}
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ((v1 - 1 : ℕ) : ℕ∞) :: flatBT X ++ b0)
    (hb0 : ∀ x ∈ b0, x = Sym.rp)
    (hinner : scb_decomp body s0 (flatBT (Dprin (v1 : ℕ∞) BZero)) b0)
    (base1 : lessBT A0 (ins BZero) = true)
    (hv1pos : 0 < v1)
    (ox5 : ∀ u : ℕ∞, b1x_setle (GBT u A0) (insert (ins BZero) (GBT u (ins BZero))))
    (KKraw : ∀ k, 1 ≤ k → (∀ j, j < k → ox8_rsub body j ≠ BZero) →
      lessBT (ox8_rsub body k) (ins BZero) = true) :
    ∀ u : ℕ∞, b1x_setle (GBT u (ins A0)) (insert (ins BZero) (GBT u (ins BZero))) := by
  -- The three flat surgery strings (from `hinner` and the flat law `hflat`).
  have wrap : flatBT body = s0 ++ flatBP (.db (v1 : ℕ∞) BZero) ++ b0 := hinner.1
  have fA1 : flatBT (ins A0) = s0 ++ flatBP (.db ((v1 - 1 : ℕ) : ℕ∞) A0) ++ b0 := by
    rw [hflat A0]; rfl
  have fX1 : flatBT (ins BZero) = s0 ++ flatBP (.db ((v1 - 1 : ℕ) : ℕ∞) BZero) ++ b0 := by
    rw [hflat BZero]; rfl
  -- `hdA`/`hdX` at the shared depth `dR` (the fully-proved structural alignment).
  obtain ⟨dR, hdA, hdX⟩ :=
    Ox9HoleDOfFlat3_holds_oc body (ins A0) (ins BZero)
      (.db (v1 : ℕ∞) BZero) (.db ((v1 - 1 : ℕ) : ℕ∞) A0) (.db ((v1 - 1 : ℕ) : ℕ∞) BZero)
      s0 b0 wrap fA1 fX1 hb0
  -- `pAlt` (fully discharged) from `ublt : v1 - 1 < v1`.
  have hub : v1 - 1 < v1 := Nat.sub_lt hv1pos Nat.one_pos
  have pAlt : lessBP (.db ((v1 - 1 : ℕ) : ℕ∞) A0) (.db (v1 : ℕ∞) BZero) = true := pAlt_oc hub
  -- `KK` from the raw census spine bound, aliveness via the engine publics.
  have KK : ∀ j, 1 ≤ j → j ≤ dR → lessBT (ox8_rsub body j) (ins BZero) = true := by
    intro k hk1 hkle
    have alive : ∀ j, j < k → ox8_rsub body j ≠ BZero := by
      intro j hjk
      have jle : j ≤ dR := le_trans (Nat.le_of_lt hjk) hkle
      exact ox9_holeD_ne_ox (ox9_holeD_rsub_ox j hdA jle)
    exact KKraw k hk1 alive
  -- Run the engine per `u` (`holeH` is per-`u`; `hdA`/`hdX`/`pAlt`/`KK` are not).
  intro u
  have holeH : b1x_setle (GBP u (.db ((v1 - 1 : ℕ) : ℕ∞) A0))
      (insert (ins BZero) (GBT u (ins BZero))) := ox6_holeH_oc (ox5 u) base1
  exact ox10_setle_from_engine_ox holeH hdA hdX pAlt KK

#print axioms ox10_SETLE1_close_oc

end PSS
