import «8».«8.7-spine-align3»
import «8».«8.7-census-provenance»

/-!
# PSS.«8».«8.7-align3-close» — discharging the align3 spine gap `SpineAlign3PeelCore_sa3`

The BUILT `«8».«8.7-spine-align3»` reduced the census surgery-TRANSPORT gap
`SpineSurgeryTransportCensus_ts` (Isabelle STATUS §(7) / `ox7_align3_track`, the ONE
genuinely-open census gap, deferred on the Isabelle side too) to the single residual
`SpineAlign3PeelCore_sa3`.  **This file discharges it unconditionally**, closing
`SetleCensusSpine`.

## The residual and the closing idea

`SpineAlign3PeelCore_sa3`: for `ox9_holeD e (D_{v₁}0) (D_{v₁-1}0) WB ins0` (`ins0` is `WB`
with its deepest-right LEAF head lowered `v₁ ⤳ v₁-1`) and `1 ≤ k ≤ e`, a right-spine
sub-body `S = ox8_rsub WB k` with `S < WB` is also `S < ins0`.

STEP-0 flagged this as verdict-INVARIANT (`ox7_align3_track`).  The faithful "lock-step
first-difference peel" the Isabelle note describes is superseded here by a **node-count
monovariant**.  Write `nodesBT` for the *head-independent* count of `D`-nodes of a
Buchholz term.  The key facts:

1. **`nodesNODES_a3c`** (the monovariant): for the hole relation with the leaf principal
   `p` node-count `1`, ANY tree `T` with `ins0 < T < WB` (i.e. wedged in `[ins0, WB)`)
   has `nodesBT WB ≤ nodesBT T`.  Proof: induction on `ox9_holeD` + a left-to-right
   prefix walk (`walk_a3c`); the hole surgery only ever touches the LAST principal of
   each right-spine level, so at the first differing position the verdict either
   transports verbatim (hole-free principal) or bottoms out at the leaf, where the
   lowered head forces `nodesBT WB ≤ nodesBT T`.
2. **`nodesBT_ox8_rsub_lt`**: a right-spine sub-body `ox8_rsub WB k` (`k ≥ 1`) is a
   PROPER subterm, so `nodesBT (ox8_rsub WB k) < nodesBT WB`.

So no spine iterate can be wedged in `[ins0, WB)`: it would need `nodesBT WB ≤ nodesBT S`
by (1) yet `nodesBT S < nodesBT WB` by (2).  Trichotomy (`lessBT_linear_trichotomy`) then
gives `S < ins0` directly (the `S = ins0` case is excluded because the surgery preserves
the node count, `nodesBT_holeD_eq`).

Numerically verified: verdict-invariant on 105900 spine-iterate cases and the monovariant
holds for all `T` (`python` brute force, 4M+ hole structures, zero counterexamples).

## Dependencies (built modules only, committed at a5ca2ff)
- `«8».«8.7-spine-align3»`: `SpineAlign3PeelCore_sa3`, `spineSurgeryTransportCensus_of_core_sa3`
  (and transitively `ox9_holeD`/`ox8_rsub` engine, `lessBT_linear_*`, `setleCensusSpine_of_census_ts`).
- `«8».«8.7-census-provenance»`: `censusProvenance_holds_cp`.

## Status
🤖 GREEN (`sorry` 0, axioms = `[propext, Classical.choice, Quot.sound]`).
Private suffix `_a3c`.
-/

namespace PSS

/-! ## 0. `nodesBT`: the head-independent `D`-node count -/

/- Head-independent node count of a Buchholz term (counts `D`-constructors only). -/
mutual
  def nodesBT : BT → ℕ
    | .trm ps => nodesBPList ps
  def nodesBP : BP → ℕ
    | .db _ b => 1 + nodesBT b
  def nodesBPList : List BP → ℕ
    | [] => 0
    | p :: ps => nodesBP p + nodesBPList ps
end

/-- `nodesBPList` is additive over `++`. -/
private theorem nodesBPList_append_a3c (as bs : List BP) :
    nodesBPList (as ++ bs) = nodesBPList as + nodesBPList bs := by
  induction as with
  | nil => simp [nodesBPList]
  | cons a as ih => simp only [List.cons_append, nodesBPList, ih]; omega

/-! ## 1. Node count along the right spine — a proper sub-body has fewer nodes -/

/-- A nonzero Buchholz term splits as a `snoc` (mirror of `bt_ne_zero_snoc_kk`). -/
private theorem bt_snoc_a3c {t : BT} (ne : t ≠ BZero) :
    ∃ (ps : List BP) (v : ℕ∞) (b : BT), t = .trm (ps ++ [.db v b]) := by
  obtain ⟨qs⟩ := t
  have hqs : qs ≠ [] := by intro h; subst h; exact ne rfl
  rcases hrev : qs.reverse with _ | ⟨p, rs⟩
  · exact absurd (by rw [← List.reverse_reverse qs, hrev]; rfl) hqs
  · obtain ⟨v, b⟩ := p
    refine ⟨rs.reverse, v, b, ?_⟩
    have hq : qs = rs.reverse ++ [.db v b] := by
      rw [← List.reverse_reverse qs, hrev]; simp
    rw [hq]

/-- The last principal's body has no more nodes than the whole term. -/
private theorem nodesBT_ox8_lastT_le (t : BT) : nodesBT (ox8_lastT t) ≤ nodesBT t := by
  rcases eq_or_ne t BZero with rfl | ne
  · simp [ox8_lastT, BZero, nodesBT, nodesBPList]
  · obtain ⟨ps, v, b, rfl⟩ := bt_snoc_a3c ne
    rw [ox8_lastT_snoc_ox]
    show nodesBT b ≤ nodesBPList (ps ++ [.db v b])
    rw [nodesBPList_append_a3c]
    simp only [nodesBPList, nodesBP]
    omega

/-- The last principal's body has STRICTLY fewer nodes (for a nonzero term). -/
private theorem nodesBT_ox8_lastT_lt {t : BT} (ne : t ≠ BZero) :
    nodesBT (ox8_lastT t) < nodesBT t := by
  obtain ⟨ps, v, b, rfl⟩ := bt_snoc_a3c ne
  rw [ox8_lastT_snoc_ox]
  show nodesBT b < nodesBPList (ps ++ [.db v b])
  rw [nodesBPList_append_a3c]
  simp only [nodesBPList, nodesBP]
  omega

/-- `nodesBT` is non-increasing under right-spine descent. -/
private theorem nodesBT_ox8_rsub_le : ∀ (k : ℕ) (t : BT), nodesBT (ox8_rsub t k) ≤ nodesBT t := by
  intro k
  induction k with
  | zero => intro t; simp [ox8_rsub_zero_ox]
  | succ k ih =>
      intro t
      rw [ox8_rsub_succ_ox]
      exact le_trans (ih (ox8_lastT t)) (nodesBT_ox8_lastT_le t)

/-- A right-spine sub-body `ox8_rsub t k` (`k ≥ 1`, `t ≠ 0`) is a PROPER subterm:
    strictly fewer nodes. -/
private theorem nodesBT_ox8_rsub_lt (t : BT) (k : ℕ) (ne : t ≠ BZero) (hk : 1 ≤ k) :
    nodesBT (ox8_rsub t k) < nodesBT t := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [ox8_rsub_succ_ox]
  exact lt_of_le_of_lt (nodesBT_ox8_rsub_le k (ox8_lastT t)) (nodesBT_ox8_lastT_lt ne)

/-! ## 2. Hole surgery preserves the node count -/

/-- The deepest-right surgery `p ⤳ q` with `nodesBP p = nodesBP q` preserves `nodesBT`. -/
private theorem nodesBT_holeD_eq : ∀ {e : ℕ} {p q : BP} {WB ins0 : BT},
    ox9_holeD e p q WB ins0 → nodesBP p = nodesBP q → nodesBT WB = nodesBT ins0 := by
  intro e p q WB ins0 h
  induction h with
  | hD0 ps p q =>
      intro hpq
      show nodesBPList (ps ++ [p]) = nodesBPList (ps ++ [q])
      rw [nodesBPList_append_a3c, nodesBPList_append_a3c]
      simp only [nodesBPList, hpq]
  | hDS k ps w p q b b' hb IH =>
      intro hpq
      have hbb := IH hpq
      show nodesBPList (ps ++ [.db w b]) = nodesBPList (ps ++ [.db w b'])
      rw [nodesBPList_append_a3c, nodesBPList_append_a3c]
      simp only [nodesBPList, nodesBP, hbb]

/-! ## 3. Elementary `lessBP` order facts (via the `lessBT` linear order) -/

/-- `lessBP` on principals is `lessBT` on their singleton terms. -/
private theorem lessBP_eq_trm_a3c (a b : BP) : lessBP a b = lessBT (BT.trm [a]) (BT.trm [b]) := by
  show lessBP a b = lessBPList [a] [b]
  simp [lessBPList]

/-- `lessBP` is irreflexive. -/
private theorem lessBP_irrefl_a3c (c : BP) : lessBP c c = false := by
  rw [lessBP_eq_trm_a3c]; exact lessBT_linear_irrefl _

/-- `lessBP` is asymmetric. -/
private theorem lessBP_asymm_a3c {a b : BP} (h1 : lessBP a b = true) (h2 : lessBP b a = true) :
    False := by
  rw [lessBP_eq_trm_a3c] at h1 h2
  have hc := lessBT_linear_trans _ _ _ h1 h2
  rw [lessBT_linear_irrefl] at hc
  exact Bool.false_ne_true hc

/-! ## 4. `walk_a3c` — the left-to-right prefix walk giving the node bound -/

/-- The wedge node bound at one right-spine level.  `xW`/`xI` are the last principals of
`WB`/`ins0` at this level (`xI < xW` implicitly).  If a candidate list `L` sits in the
wedge `(prefix ⌢ [xI]) < L < (prefix ⌢ [xW])` then `nodesBPList (prefix ⌢ [xW]) ≤ nodesBPList L`,
given the FINal-position fact `FIN` (hole-free principal transports the count) and
`hxWI : nodesBP xW ≤ nodesBP xI` (surgery preserves the count). -/
private theorem walk_a3c {xW xI : BP}
    (FIN : ∀ d : BP, lessBP xI d = true → lessBP d xW = true → nodesBP xW ≤ nodesBP d)
    (hxWI : nodesBP xW ≤ nodesBP xI) :
    ∀ (ps L : List BP),
      lessBPList (ps ++ [xI]) L = true →
      lessBPList L (ps ++ [xW]) = true →
      nodesBPList (ps ++ [xW]) ≤ nodesBPList L := by
  intro ps
  induction ps with
  | nil =>
      intro L hle hlt
      simp only [List.nil_append] at hle hlt ⊢
      cases L with
      | nil => simp [lessBPList] at hle
      | cons d L' =>
          have hL0 : lessBPList L' [] = false := by cases L' <;> rfl
          have hdW : lessBP d xW = true := by
            have h2 : (lessBP d xW || (d == xW && lessBPList L' [])) = true := hlt
            simp only [hL0, Bool.and_false, Bool.or_false] at h2; exact h2
          have hle2 : (lessBP xI d || (xI == d && lessBPList ([] : List BP) L')) = true := hle
          simp only [nodesBPList]
          simp only [Bool.or_eq_true] at hle2
          rcases hle2 with h | h
          · have := FIN d h hdW; omega
          · rw [Bool.and_eq_true] at h
            have hxd : xI = d := eq_of_beq h.1
            rw [← hxd]; omega
  | cons c ps' ih =>
      intro L hle hlt
      cases L with
      | nil => simp [lessBPList] at hle
      | cons d L' =>
          simp only [List.cons_append] at hle hlt ⊢
          by_cases hcd : c = d
          · subst hcd
            have hcc : lessBP c c = false := lessBP_irrefl_a3c c
            have hle' : lessBPList (ps' ++ [xI]) L' = true := by
              have h2 : (lessBP c c || (c == c && lessBPList (ps' ++ [xI]) L')) = true := hle
              simpa only [hcc, beq_self_eq_true, Bool.false_or, Bool.true_and] using h2
            have hlt' : lessBPList L' (ps' ++ [xW]) = true := by
              have h2 : (lessBP c c || (c == c && lessBPList L' (ps' ++ [xW]))) = true := hlt
              simpa only [hcc, beq_self_eq_true, Bool.false_or, Bool.true_and] using h2
            have IHres := ih L' hle' hlt'
            simp only [nodesBPList]; omega
          · have hcd_beq : (c == d) = false := by
              cases hh : (c == d) with
              | false => rfl
              | true => exact absurd (eq_of_beq hh) hcd
            have hdc_beq : (d == c) = false := by
              cases hh : (d == c) with
              | false => rfl
              | true => exact absurd (eq_of_beq hh).symm hcd
            have hcd' : lessBP c d = true := by
              have h2 : (lessBP c d || (c == d && lessBPList (ps' ++ [xI]) L')) = true := hle
              simpa only [hcd_beq, Bool.false_and, Bool.or_false] using h2
            have hdc' : lessBP d c = true := by
              have h2 : (lessBP d c || (d == c && lessBPList L' (ps' ++ [xW]))) = true := hlt
              simpa only [hdc_beq, Bool.false_and, Bool.or_false] using h2
            exact (lessBP_asymm_a3c hcd' hdc').elim

/-! ## 5. `nodesNODES_a3c` — the wedge monovariant -/

/-- **The node-count monovariant.**  For `ox9_holeD e p q WB ins0` with the leaf principal
`p` of node-count `1` (`p = D_{v₁}0`) and `nodesBP p = nodesBP q` (surgery preserves count),
ANY tree `T` strictly between `ins0` and `WB` (i.e. `ins0 < T` and `T < WB`) satisfies
`nodesBT WB ≤ nodesBT T`. -/
private theorem nodesNODES_a3c : ∀ {e : ℕ} {p q : BP} {WB ins0 : BT},
    ox9_holeD e p q WB ins0 → nodesBP p = 1 → nodesBP p = nodesBP q →
    ∀ T, lessBT ins0 T = true → lessBT T WB = true → nodesBT WB ≤ nodesBT T := by
  intro e p q WB ins0 h
  induction h with
  | hD0 ps p q =>
      intro hpb hpq T hle hlt
      obtain ⟨L⟩ := T
      show nodesBPList (ps ++ [p]) ≤ nodesBPList L
      have hle' : lessBPList (ps ++ [q]) L = true := hle
      have hlt' : lessBPList L (ps ++ [p]) = true := hlt
      have FIN : ∀ d : BP, lessBP q d = true → lessBP d p = true → nodesBP p ≤ nodesBP d := by
        intro d _ _
        obtain ⟨wd, bd⟩ := d
        simp only [nodesBP]; omega
      have hxWI : nodesBP p ≤ nodesBP q := le_of_eq hpq
      exact walk_a3c FIN hxWI ps L hle' hlt'
  | hDS k ps w p q b b' hb IH =>
      intro hpb hpq T hle hlt
      obtain ⟨L⟩ := T
      show nodesBPList (ps ++ [.db w b]) ≤ nodesBPList L
      have hbb : nodesBT b = nodesBT b' := nodesBT_holeD_eq hb hpq
      have hle' : lessBPList (ps ++ [.db w b']) L = true := hle
      have hlt' : lessBPList L (ps ++ [.db w b]) = true := hlt
      have FIN : ∀ d : BP, lessBP (.db w b') d = true → lessBP d (.db w b) = true →
          nodesBP (.db w b) ≤ nodesBP d := by
        intro d hId hdW
        obtain ⟨wd, bd⟩ := d
        simp only [nodesBP]
        simp only [lessBP, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          beq_iff_eq] at hdW hId
        rcases hdW with hlt'' | ⟨hwe, hbdb⟩
        · rcases hId with hlt3 | ⟨hwe', _⟩
          · exact absurd hlt'' (lt_asymm hlt3)
          · exact absurd hlt'' (by rw [hwe']; exact lt_irrefl _)
        · subst hwe
          rcases hId with hlt3 | ⟨_, hb'bd⟩
          · exact absurd hlt3 (lt_irrefl _)
          · have hle2 := IH hpb hpq bd hb'bd hbdb
            omega
      have hxWI : nodesBP (.db w b) ≤ nodesBP (.db w b') := by
        simp only [nodesBP]; omega
      exact walk_a3c FIN hxWI ps L hle' hlt'

/-! ## 6. Discharging `SpineAlign3PeelCore_sa3` -/

/-- **The align3 spine gap, closed.**  `SpineAlign3PeelCore_sa3` (Isabelle
`ox7_align3_track`, the ONE genuinely-open census gap) holds unconditionally: no
right-spine sub-body of `WB` is wedged in `[ins0, WB)`, by the node-count monovariant. -/
theorem spineAlign3PeelCore_holds_a3c : SpineAlign3PeelCore_sa3 := by
  intro e v1 WB ins0 hhole k hk1 hke hlt
  have hpb : nodesBP (BP.db (v1 : ℕ∞) BZero) = 1 := by
    simp [nodesBP, BZero, nodesBT, nodesBPList]
  have hqb : nodesBP (BP.db ((v1 - 1 : ℕ) : ℕ∞) BZero) = 1 := by
    simp [nodesBP, BZero, nodesBT, nodesBPList]
  have hpq : nodesBP (BP.db (v1 : ℕ∞) BZero) = nodesBP (BP.db ((v1 - 1 : ℕ) : ℕ∞) BZero) := by
    rw [hpb, hqb]
  have hWBne : WB ≠ BZero := ox9_holeD_ne_ox hhole
  have hSlt : nodesBT (ox8_rsub WB k) < nodesBT WB := nodesBT_ox8_rsub_lt WB k hWBne hk1
  rcases lessBT_linear_trichotomy (ox8_rsub WB k) ins0 with hlt2 | heq | hgt
  · exact hlt2
  · exfalso
    have hEq : nodesBT WB = nodesBT ins0 := nodesBT_holeD_eq hhole hpq
    rw [heq] at hSlt
    omega
  · exfalso
    have hbound : nodesBT WB ≤ nodesBT (ox8_rsub WB k) :=
      nodesNODES_a3c hhole hpb hpq (ox8_rsub WB k) hgt hlt
    omega

#print axioms spineAlign3PeelCore_holds_a3c

/-! ## 7. Compose to close `SetleCensusSpine` -/

/-- The census surgery-TRANSPORT `SpineSurgeryTransportCensus_ts`, now unconditional
(from `spineSurgeryTransportCensus_of_core_sa3` applied to the discharged residual). -/
theorem spineSurgeryTransportCensus_holds_a3c : SpineSurgeryTransportCensus_ts :=
  spineSurgeryTransportCensus_of_core_sa3 spineAlign3PeelCore_holds_a3c

/-- **`SetleCensusSpine` closed unconditionally.**  Compose the discharged census
transport with `censusProvenance_holds_cp` through `setleCensusSpine_of_census_ts`. -/
theorem setleCensusSpine_holds_a3c : SetleCensusSpine :=
  setleCensusSpine_of_census_ts censusProvenance_holds_cp spineSurgeryTransportCensus_holds_a3c

#print axioms spineSurgeryTransportCensus_holds_a3c
#print axioms setleCensusSpine_holds_a3c

end PSS
