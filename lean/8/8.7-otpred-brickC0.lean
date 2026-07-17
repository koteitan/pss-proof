import «8».«8.7-otdisp-OTpred»
import «7».«7.4-Mark-Trans-repr»
import «8».«8.1-diagSeq-Trans»

/-!
# §8.7 OTpred Brick C0 — the condition-(VI) non-admissible `c₁` shape

Port of Isabelle `od4_condVI_nadm_c1` (`layerC/pss_scratch.thy`:479–621), the ONLY
`transC2` branch of Brick C (`od4_site_c2`, `pss_scratch.thy`:634) that needs
structural knowledge of `t₂`.  Under condition (VI) with `¬ adm M j₀`
(`j₀ = Lng M - 2`), the whole backward run `(j₋₁, j₀]` (`j₋₁ = Adm M j₀`) is
non-admissible, so both coefficient rows step `+1` along it; the reduced backward
slice is literally the diagonal `diagSeq u (u+d)`, whose `Trans` is the explicit
two-level tower.  Hence `t₂ = D_{M₁,j₀} 0`.

## Public theorems (Isabelle name → Lean name)
* `wnx_run_entries`      (`pss_wip.thy`:80739) → `wnx_run_entries`
* `od4_condVI_nadm_c1`   (`pss_scratch.thy`:479) → `od4_condVI_nadm_c1`

## Engines (imported, built tree)
* `m_7_4_Mark_Trans_repr` → `Mark_Trans_repr`  (`«7».«7.4-Mark-Trans-repr»`)
* `m_8_1_diagSeq_Trans`   → `diagSeq_Trans`    (`«8».«8.1-diagSeq-Trans»`)
* `m_6_6_ancestor_slice_Red_IncrFirst` → `ancestor_slice_Red_IncrFirst`,
  `m_6_5_Lng_Red` → `Lng_Red_invariance`, `m_6_6_reduced_coeff` → `reduced_coeff`,
  `Trans_IncrFirst_Red`, `mono_hasParent_row0`, `Marked_Pred_Adm`, `RTPS_Pred`,
  `adm_row1_ancestry`, `row1_implies_row0` (`= m_le1_imp_le0`), `RTPS_iff_condAB`,
  `RedCondA_apply`, `Adm_max`, `Adm_le`, `Adm_adm`.

## Reconstructed here (no Lean twin in the built tree)
The whole `wnx_` run-arithmetic cluster (`pss_wip.thy`:80586–80763):
`wnx_le0_adjacent_step`, `wnx_adjacent_parent0/1` (via a filter-singleton argument
matching Lean's `parents = filter`-based `parent`/`hasParent`), `wnx_condA_step`,
`wnx_run_nadm`, `wnx_run_step_entries`, `wnx_run_entries`, plus `slice`/`IncrFirstN`
transport (`Trans_slice_eq_Red` bypassed via `Trans_IncrFirstN_bC0`), `nadm_Adm_lt`.

- 依存: 上記 import 3 本の推移閉包（すべて committed-green）。
- 状態: ✅ GREEN（`sorry` 0、axioms = propext/Classical.choice/Quot.sound）。
  `od4_site_c2`（Brick C 全体、残り 5 branch）は未移植（"needs" 参照）。
-/

namespace PSS

/-! ### le0 adjacency: a single step -/

private theorem le0Aux_index_bC0 (M : PS) :
    ∀ (fuel a b : ℕ), le0Aux M fuel a b = true → a ≤ b
  | 0, a, b, h => by
      simp only [le0Aux, beq_iff_eq] at h; omega
  | fuel + 1, a, b, h => by
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true] at h
      rcases h with h | ⟨j, hj, hnx, hrec⟩
      · omega
      · have hrec' := le0Aux_index_bC0 M fuel a j hrec
        have hjb : j < b := List.mem_range.mp hj
        omega

private theorem le0Aux_adjacent_bC0 (M : PS) (t : ℕ) :
    ∀ fuel, le0Aux M fuel t (t + 1) = true → nextrel0 M t (t + 1) = true
  | 0, h => by simp only [le0Aux, beq_iff_eq] at h; omega
  | fuel + 1, h => by
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true] at h
      rcases h with h | ⟨j, hj, hnx, hrec⟩
      · omega
      · have hle := le0Aux_index_bC0 M fuel t j hrec
        have hjb : j < t + 1 := List.mem_range.mp hj
        have hjt : j = t := by omega
        subst hjt
        exact hnx

/-- Isabelle `wnx_le0_adjacent_step` (layerB/pss_wip.thy:80586). -/
private theorem wnx_le0_adjacent_step_bC0 (M : PS) (t : ℕ)
    (hle : le0 M t (t + 1) = true) : nextrel0 M t (t + 1) = true := by
  have haux : le0Aux M (Lng M) t (t + 1) = true := by
    have h := hle
    simp only [le0, Bool.and_eq_true] at h
    exact h.2
  exact le0Aux_adjacent_bC0 M t (Lng M) haux

/-! ### adjacent unique parent -/

private theorem parents_adjacent_singleton_bC0 (M : PS) (i s : ℕ)
    (_hspos : 0 < s) (hsL : s - 1 < Lng M)
    (hnx : nextR M i (s - 1) s = true)
    (huniq : ∀ j', nextR M i j' s = true → j' = s - 1) :
    parents M i s = [s - 1] := by
  have hmem : s - 1 ∈ parents M i s := by
    rw [parents, List.mem_filter]
    exact ⟨List.mem_range.mpr hsL, hnx⟩
  have hnodup : (parents M i s).Nodup := by
    rw [parents]; exact (List.nodup_range).filter _
  have hall : ∀ b ∈ parents M i s, b = s - 1 := by
    intro b hb
    rw [parents, List.mem_filter] at hb
    exact huniq b hb.2
  have hrep : parents M i s = List.replicate (parents M i s).length (s - 1) := by
    rw [List.eq_replicate_iff]; exact ⟨rfl, hall⟩
  have hle : (parents M i s).length ≤ 1 := by
    have := hnodup
    rw [hrep, List.nodup_replicate] at this
    exact this
  have hge : 1 ≤ (parents M i s).length :=
    List.length_pos_iff_ne_nil.mpr (List.ne_nil_of_mem hmem)
  have hlen1 : (parents M i s).length = 1 := le_antisymm hle hge
  rw [hrep, hlen1]; rfl

private theorem parent_adj_of_singleton_bC0 (M : PS) (i s : ℕ)
    (h : parents M i s = [s - 1]) :
    hasParent M i s = true ∧ parent M i s = s - 1 := by
  refine ⟨?_, ?_⟩
  · simp [hasParent, h]
  · simp [parent, h]

/-- Row-0 adjacent parent. -/
private theorem parent_adj0_bC0 (M : PS) (s : ℕ)
    (hspos : 0 < s) (hsL : s < Lng M)
    (hnx : nextrel0 M (s - 1) s = true) :
    hasParent M 0 s = true ∧ parent M 0 s = s - 1 := by
  have hstrict : entry M 0 (s - 1) < entry M 0 s := by
    have hh := hnx
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.2
  have huniq : ∀ j', nextR M 0 j' s = true → j' = s - 1 := by
    intro j' hj'
    have hn : nextrel0 M j' s = true := by simpa [nextR] using hj'
    have hh := hn
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hh
    have hlt : j' < s := hh.1.1.2
    by_contra hne
    have hjs : j' < s - 1 := by omega
    have hc := hh.2 (s - 1) (List.mem_range.mpr (by omega))
    have : entry M 0 s ≤ entry M 0 (s - 1) := by
      have := hc
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq] at this
      rcases this with hcon | hcon
      · omega
      · exact hcon
    omega
  have hsm : s - 1 < Lng M := by omega
  have hnxR : nextR M 0 (s - 1) s = true := by simpa [nextR] using hnx
  exact parent_adj_of_singleton_bC0 M 0 s
    (parents_adjacent_singleton_bC0 M 0 s hspos hsm hnxR huniq)

/-- Row-1 adjacent parent. -/
private theorem parent_adj1_bC0 (M : PS) (s : ℕ)
    (hspos : 0 < s) (_hsL : s < Lng M)
    (hnx : nextrel1 M (s - 1) s = true) :
    hasParent M 1 s = true ∧ parent M 1 s = s - 1 := by
  have hh0 := hnx
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh0
  have hstrict : entry M 1 (s - 1) < entry M 1 s := hh0.1.1.2
  have hle0 : le0 M (s - 1) s = true := hh0.1.2
  have huniq : ∀ j', nextR M 1 j' s = true → j' = s - 1 := by
    intro j' hj'
    have hn : nextrel1 M j' s = true := by simpa [nextR] using hj'
    have hh := hn
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hh
    have hlt : j' < s := hh.1.1.1.2
    by_contra hne
    have hjs : j' < s - 1 := by omega
    have hd1 : decide (j' < s - 1) = true := decide_eq_true_eq.mpr hjs
    have hc := hh.2 (s - 1) (List.mem_range.mpr (by omega))
    rw [hd1, hle0] at hc
    simp only [Bool.true_and, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc
    omega
  have hsm : s - 1 < Lng M := by omega
  have hnxR : nextR M 1 (s - 1) s = true := by simpa [nextR] using hnx
  exact parent_adj_of_singleton_bC0 M 1 s
    (parents_adjacent_singleton_bC0 M 1 s hspos hsm hnxR huniq)

/-! ### condA step and run entries -/

/-- Isabelle `wnx_condA_step` (layerB/pss_wip.thy:80685). -/
private theorem wnx_condA_step_bC0 (M : PS) (hR : RTPS M) (i j : ℕ)
    (hi : i < 2) (hj : j < Lng M) (hp : hasParent M i j = true) :
    entry M i (parent M i j) + 1 = entry M i j := by
  have hM : TPS M := RTPS_TPS M hR
  have hA : RedCondA M = true := ((RTPS_iff_condAB M hM).mp hR).1
  exact RedCondA_apply M hA i j hi hj hp

/-- Isabelle `wnx_run_nadm` (layerB/pss_wip.thy:80695). -/
private theorem wnx_run_nadm_bC0 (M : PS) (j0 s : ℕ)
    (_nadm0 : adm M j0 = false) (lo : Adm M j0 < s) (hi : s ≤ j0) :
    adm M s = false := by
  by_cases hb : adm M s = true
  · exact absurd (Adm_max M s j0 hb hi) (by omega)
  · simp only [Bool.not_eq_true] at hb; exact hb

/-- Isabelle `wnx_run_step_entries` (layerB/pss_wip.thy:80710). -/
private theorem wnx_run_step_entries_bC0 (M : PS) (hR : RTPS M) (j0 s : ℕ)
    (jL : j0 < Lng M) (nadm0 : adm M j0 = false)
    (lo : Adm M j0 < s) (hi : s ≤ j0) :
    entry M 0 s = entry M 0 (s - 1) + 1 ∧
      entry M 1 s = entry M 1 (s - 1) + 1 := by
  have hspos : 0 < s := by omega
  have hsL : s < Lng M := by omega
  have nadms : adm M s = false := wnx_run_nadm_bC0 M j0 s nadm0 lo hi
  have hnadm : nadm M s = true := by
    have : nadm M s = true := by
      have h := nadms; simp only [adm, Bool.not_eq_false'] at h; exact h
    exact this
  have hnx1 : nextR M 1 (s - 1) s = true := by
    have hh := hnadm
    simp only [nadm, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hh
    rcases hh with hcon | hcon
    · omega
    · exact hcon.1
  have hnr1 : nextrel1 M (s - 1) s = true := by simpa [nextR] using hnx1
  have hh1 := hnr1
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh1
  have hle0 : le0 M (s - 1) s = true := hh1.1.2
  -- row 1
  obtain ⟨hp1, hpe1⟩ := parent_adj1_bC0 M s hspos hsL hnr1
  have e1 := wnx_condA_step_bC0 M hR 1 s (by omega) hsL hp1
  rw [hpe1] at e1
  -- row 0
  have hnr0 : nextrel0 M (s - 1) s = true := by
    have : le0 M (s - 1) s = true := hle0
    have h01 : s - 1 + 1 = s := by omega
    have := wnx_le0_adjacent_step_bC0 M (s - 1) (by rw [h01]; exact hle0)
    rwa [h01] at this
  obtain ⟨hp0, hpe0⟩ := parent_adj0_bC0 M s hspos hsL hnr0
  have e0 := wnx_condA_step_bC0 M hR 0 s (by omega) hsL hp0
  rw [hpe0] at e0
  exact ⟨e0.symm, e1.symm⟩

/-- Isabelle `wnx_run_entries` (layerB/pss_wip.thy:80739). -/
theorem wnx_run_entries (M : PS) (hR : RTPS M) (j0 t : ℕ)
    (jL : j0 < Lng M) (nadm0 : adm M j0 = false)
    (ht : t ≤ j0 - Adm M j0) :
    entry M 0 (Adm M j0 + t) = entry M 0 (Adm M j0) + t ∧
      entry M 1 (Adm M j0 + t) = entry M 1 (Adm M j0) + t := by
  have hAle : Adm M j0 ≤ j0 := Adm_le M j0
  induction t with
  | zero => simp
  | succ t ih =>
      have htle : t ≤ j0 - Adm M j0 := by omega
      obtain ⟨ih0, ih1⟩ := ih htle
      have lo : Adm M j0 < Adm M j0 + (t + 1) := by omega
      have hiJ : Adm M j0 + (t + 1) ≤ j0 := by omega
      obtain ⟨s0, s1⟩ :=
        wnx_run_step_entries_bC0 M hR j0 (Adm M j0 + (t + 1)) jL nadm0 lo hiJ
      have hsm : Adm M j0 + (t + 1) - 1 = Adm M j0 + t := by omega
      rw [hsm] at s0 s1
      refine ⟨?_, ?_⟩
      · rw [s0, ih0]; omega
      · rw [s1, ih1]; omega

/-! ### `Trans` / `entry` under `IncrFirstN` -/

private theorem TPS_IncrFirst_bC0 (M : PS) (hM : TPS M) : TPS (IncrFirst M) := by
  simpa [TPS, IncrFirst] using hM

private theorem Trans_IncrFirstN_bC0 :
    ∀ (k : ℕ) (M : PS), TPS M → Trans (IncrFirstN k M) = Trans M
  | 0, M, _ => by simp [IncrFirstN]
  | k + 1, M, hM => by
      rw [IncrFirstN,
        Trans_IncrFirstN_bC0 k (IncrFirst M) (TPS_IncrFirst_bC0 M hM)]
      exact (Trans_IncrFirst_Red M hM).2.symm

private theorem entry_IncrFirstN0_bC0 (k : ℕ) (M : PS) (j : ℕ) (hj : j < Lng M) :
    entry (IncrFirstN k M) 0 j = entry M 0 j + k := by
  rw [IncrFirstN_eq_map]
  simp only [entry, List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some]
  simp

private theorem entry_IncrFirstN1_bC0 (k : ℕ) (M : PS) (j : ℕ) (hj : j < Lng M) :
    entry (IncrFirstN k M) 1 j = entry M 1 j := by
  rw [IncrFirstN_eq_map]
  simp only [entry, List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some]
  simp

/-! ### MAIN — Brick C0 -/

/-- Isabelle `od4_condVI_nadm_c1` (layerC/pss_scratch.thy:479). -/
theorem od4_condVI_nadm_c1 (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hcond : transCondVI M = true) (hj1 : 1 < Lng M - 1)
    (hnadm : adm M (transJ0 M) = false) :
    transC1 M = Dprin (entry M 1 (transJm1 M) : ℕ∞)
                  (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero) ∧
      transT2 M = Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero := by
  have hM : TPS M := RTPS_TPS M hR
  have hL : 1 < Lng M := by omega
  have hL3 : 2 < Lng M := by omega
  -- j₀ = Lng M - 2
  have hcv : transJ0 M + 1 = Lng M - 1 := by
    have h := hcond
    simp only [transCondVI, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      lastIdx, lastParent] at h
    simpa [transJ0, lastParent, lastIdx] using h.2
  have hj0eq : transJ0 M = Lng M - 2 := by omega
  have j0L : transJ0 M < Lng M := by omega
  -- j₋₁ < j₀
  have hjm1lt : transJm1 M < transJ0 M := by
    have hle := Adm_le M (transJ0 M)
    have hadm := Adm_adm M (transJ0 M)
    rcases Nat.lt_or_ge (Adm M (transJ0 M)) (transJ0 M) with h | h
    · exact h
    · exfalso
      have heq : Adm M (transJ0 M) = transJ0 M := by omega
      rw [heq] at hadm
      rw [hnadm] at hadm
      simp at hadm
  set d := transJ0 M - transJm1 M with hd
  have hdpos : 0 < d := by omega
  have hjm1d : transJm1 M + d = transJ0 M := by omega
  set u := entry M 1 (transJm1 M) with hu
  -- Marked pair + Mark–Trans representation
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have mkd : Marked (Pred M) (transJm1 M) := Marked_Pred_Adm M hM hL hp0
  have predRT : RTPS (Pred M) := RTPS_Pred M hR
  have LP : Lng (Pred M) = Lng M - 1 := length_Pred M hL
  have jm1P : transJm1 M < Lng (Pred M) - 1 := by rw [LP]; omega
  have repr : Mark (Pred M) (transJm1 M) =
      Trans (seg (Pred M) (transJm1 M) (Lng (Pred M) - 1)) :=
    Mark_Trans_repr (Pred M) (transJm1 M) mkd predRT jm1P
  have segP : seg (Pred M) (transJm1 M) (Lng (Pred M) - 1) =
      seg M (transJm1 M) (Lng M - 2) := by
    rw [LP]
    have h2 : Lng M - 1 - 1 = Lng M - 2 := by omega
    rw [h2]
    exact seg_Pred_eq M (transJm1 M) (Lng M - 2) hL (by omega) (by omega)
  -- ancestry leR M 0 j₋₁ (Lng M - 2)
  have le1a : leR M 1 (transJm1 M) (transJ0 M) = true :=
    adm_row1_ancestry M (transJ0 M) hM (by omega)
  have le0a : leR M 0 (transJm1 M) (transJ0 M) = true :=
    row1_implies_row0 M (transJm1 M) (transJ0 M) hM le1a
  have leab : leR M 0 (transJm1 M) (Lng M - 2) = true := by rw [← hj0eq]; exact le0a
  have ablt : transJm1 M < Lng M - 2 := by omega
  have bLe : Lng M - 2 ≤ Lng M - 1 := by omega
  -- reduced slice geometry
  obtain ⟨hRR, hmonoR, hSIF⟩ :=
    ancestor_slice_Red_IncrFirst M (transJm1 M) (Lng M - 2) hR ablt bLe leab
  set S := seg M (transJm1 M) (Lng M - 2) with hS
  set R := Red S with hRdef
  -- lengths
  have hLSraw : Lng (seg M (transJm1 M) (Lng M - 2)) = (Lng M - 2) + 1 - transJm1 M := by
    simp [seg]
  have hLS : Lng S = Lng M - 1 - transJm1 M := by rw [hS, hLSraw]; omega
  have hSne : S ≠ [] := by
    have hpos : 0 < Lng S := by rw [hLS]; omega
    exact List.length_pos_iff_ne_nil.mp hpos
  have hST : TPS S := hSne
  have hLR : Lng R = Lng S := by rw [hRdef]; exact Lng_Red_invariance S hST
  have hLRd : Lng R = d + 1 := by rw [hLR, hLS]; omega
  have hRne : R ≠ [] := by
    have hpos : 0 < Lng R := by rw [hLRd]; omega
    exact List.length_pos_iff_ne_nil.mp hpos
  have hRT : TPS R := hRne
  -- run entries transported
  have runE : ∀ t, t ≤ d →
      entry M 0 (transJm1 M + t) = entry M 0 (transJm1 M) + t ∧
        entry M 1 (transJm1 M + t) = entry M 1 (transJm1 M) + t := by
    intro t ht
    have hfuel : t ≤ transJ0 M - Adm M (transJ0 M) := by
      have hid : Adm M (transJ0 M) = transJm1 M := rfl
      rw [hid]; omega
    have hw := wnx_run_entries M hR (transJ0 M) t j0L hnadm hfuel
    exact hw
  have cf : entry M 1 (transJm1 M) ≤ entry M 0 (transJm1 M) :=
    reduced_coeff M hR (transJm1 M) (by omega)
  -- entries of R
  have eR : ∀ t, t < d + 1 → entry R 0 t = u + t ∧ entry R 1 t = u + t := by
    intro t htd
    have tR : t < Lng R := by rw [hLRd]; omega
    have tS : t < Lng S := hLR ▸ tR
    have tSseg : t < Lng (seg M (transJm1 M) (Lng M - 2)) := hS ▸ tS
    have eS0 : entry S 0 t = entry M 0 (transJm1 M + t) := by
      rw [hS]; exact entry_seg M (transJm1 M) (Lng M - 2) 0 t tSseg
    have eS1 : entry S 1 t = entry M 1 (transJm1 M + t) := by
      rw [hS]; exact entry_seg M (transJm1 M) (Lng M - 2) 1 t tSseg
    have run := runE t (by omega)
    have f1 : entry S 1 t = entry R 1 t := by
      rw [hSIF]
      exact entry_IncrFirstN1_bC0
        (entry M 0 (transJm1 M) - entry M 1 (transJm1 M)) R t tR
    have f0 : entry S 0 t
        = entry R 0 t + (entry M 0 (transJm1 M) - entry M 1 (transJm1 M)) := by
      rw [hSIF]
      exact entry_IncrFirstN0_bC0
        (entry M 0 (transJm1 M) - entry M 1 (transJm1 M)) R t tR
    refine ⟨?_, ?_⟩
    · have hA : entry M 0 (transJm1 M) + t
          = entry R 0 t + (entry M 0 (transJm1 M) - entry M 1 (transJm1 M)) := by
        rw [← run.1, ← eS0, f0]
      rw [hu]; omega
    · have hB : entry M 1 (transJm1 M) + t = entry R 1 t := by
        rw [← run.2, ← eS1, f1]
      rw [hu]; omega
  -- R is the diagonal
  have entryR0 : ∀ (t : ℕ) (h : t < Lng R), entry R 0 t = (R[t]'h).1 := by
    intro t h; simp [entry, List.getElem?_eq_getElem h]
  have entryR1 : ∀ (t : ℕ) (h : t < Lng R), entry R 1 t = (R[t]'h).2 := by
    intro t h; simp [entry, List.getElem?_eq_getElem h]
  have Rdiag : R = diagSeq u (u + d) := by
    apply List.ext_getElem
    · simp only [diagSeq, List.length_map, List.length_range']
      have hRl : R.length = d + 1 := hLRd
      omega
    · intro t h1 h2
      have htd : t < d + 1 := by rw [← hLRd]; exact h1
      have e0 := (eR t htd).1
      have e1 := (eR t htd).2
      rw [entryR0 t h1] at e0
      rw [entryR1 t h1] at e1
      have hrhs : (diagSeq u (u + d))[t]'h2 = (u + t, u + t) := by
        simp [diagSeq, List.getElem_map, List.getElem_range']
      rw [hrhs]
      apply Prod.ext
      · simpa using e0
      · simpa using e1
  -- Trans of R and S
  have TransR : Trans R = Dprin (u : ℕ∞) (Dprin ((u + d : ℕ) : ℕ∞) BZero) := by
    rw [Rdiag]; exact diagSeq_Trans u (u + d) (by omega)
  have TransS : Trans S = Trans R := by
    rw [hSIF]
    exact Trans_IncrFirstN_bC0
      (entry M 0 (transJm1 M) - entry M 1 (transJm1 M)) R hRT
  -- read back c₁ and t₂
  have ud : u + d = entry M 1 (transJ0 M) := by
    have hrun := (runE d (le_refl _)).2
    rw [hjm1d] at hrun
    rw [hu]; omega
  have c1eq : transC1 M = Trans S := by
    simp only [transC1]
    rw [repr, segP]
  have key : transC1 M = Dprin (u : ℕ∞) (Dprin ((u + d : ℕ) : ℕ∞) BZero) := by
    rw [c1eq, TransS, TransR]
  rw [ud] at key
  refine ⟨key, ?_⟩
  calc transT2 M = bpHeadT (transC1 M) := rfl
    _ = bpHeadT (Dprin (u : ℕ∞)
          (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) := by rw [key]
    _ = Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero := rfl

#print axioms wnx_run_entries
#print axioms od4_condVI_nadm_c1

end PSS
