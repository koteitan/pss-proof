import «8».«8.4-exch84-regs»
import «8».«8.1-part4-setup»
import «5».«5.1-ancestor-tree»
import «5».«5.1-ancestor-basic»
import «6».«6.3-admof-slice»
import «6».«6.3-adm-slice»
import «6».«6.2-P-fseq»
import «6».«6.6-P-condAB»
import «6».«6.6-condAB-coeff»
import «6».«6.4-FirstNodes-TrMax-Joints»
import «6».«6.4-FirstNodes-Joints-mono»
import «6».«6.4-mono-slice»
import «6».«6.4-mono-slice-next»
import «6».«6.5-Lng-Red-invariance»
import «6».«6.5-Red-IncrFirst-invariance»
import «6».«6.5-Red-le-core»
import «6».«6.5-Red-welldefined»
import «6».«6.5-monoT-Red»
import «6».«6.6-ancestor-slice-Red-IncrFirst»
import «6».«6.6-reduced-iff-condAB»
import «6».«6.6-reduced-coeff»
import «6».«6.6-reduced-leftend»
import «6».«6.7-standard-reduced»
import «8».«8.2-standard-slice-Red-strongmono»
import «8».«8.2-condV-rightmost-parent»

/-!
# §8.4 交換パッケージ `REGS` 脚の残差 Prop の discharge（`Regs_jm3Marked` / `Regs_MCOND`）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
- 移植元（Isabelle）:
  * `Regs_jm3Marked` = `s84d_jm3_Marked` (`isabelle/layerB/pss_wip.thy:58783`):
    `(M, j₋₃) ∈ Marked ∧ j₋₃ ≤ j₋₂ ∧ j₋₂ < Lng M - 1`。
  * `crx_trmax_run` (`isabelle/layerB/pss_wip.thy:89879`): run bound
    `(j₋₂-j₋₃)+1 ≤ TrMax (Red (s84x_N M))`。本ファイルでは private `crx_trmax_run_mc`。
  * `Regs_MCOND` = `mcx_MCOND_RN` (`isabelle/layerB/pss_wip.thy:93796`, ~200 行):
    sharp な対角残差（`m < 最終 joint`、または `m = 最終 joint` かつ最終枝左端が対角）。

- `8.4-exch84-regs` の 3 残差 Prop のうち 2 本（`Regs_jm3Marked`, `Regs_MCOND`）を
  house pattern（Prop を定理の型に）で discharge。3 本目 `Regs_jm2_lt_transJ0`
  （= `m_8_4_oper_props_1(1)`）は `MCOND` 本体で必要になるので、公開の親最大性
  primitive `nextR0_largest_below`（§6.4）から本ファイル内で private 再証明
  （`jm2_lt_transJ0_mc`）する。

- 使用する公開補題:
  `adm_row1_ancestry_ps`（8.1-part4-setup）, `row1_implies_row0_at`/`row0_transitive`
  （5.1-ancestor-tree）, `Adm_le`/`Adm_adm`/`Adm_max`（6.3）, `s84c1_jm2_basic`/
  `s84c1_nextR1_jm2`（8.4-s84x-vocab-run）, `nextR0_largest_below`/`nextR0_leR`/
  `ancestor_basic_1`, `mono_hasParent_row0`/`no_parent_zero`/`RedCondB_head_eq`,
  `hasParent_next_fseq`/`hasParent_iff_unique_fseq`/`parent_eq_of_unique_fseq`,
  `Joints_getD`/`FirstNodes_getD`/`FirstNodes_TrMax_Joints`/`mono_slice_next`,
  `standard_slice_Red_strongmono`/`DTPS_iff`, `Lng_Red_invariance`/
  `ancestor_slice_Red_IncrFirst`/`nextR_IncrFirstN_ri`/`nextR1_seg_adm`,
  `TrMax_trunk_step`/`le_TrMax_intro_wd`, `trunk_entries_offset`/`RedCondA_apply`,
  `wf21_Br_eq_seg`/`Br_component_nonmulti`/`le0_monoT_seg_into_list`,
  `reduced_coeff`/`RTPS_condAB`, `nextR1_unique_mr`, `P_nonempty`。

- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
- Private helper suffix: `_mc`。
-/

namespace PSS

/-! ## 1. `Regs_jm3Marked`（= `s84d_jm3_Marked`）の drop-in -/

/-- Isabelle `s84d_jm3_Marked` (layerB/pss_wip.thy:58783) の house-pattern drop-in。
`j₋₃ = Adm M j₋₂` は基点で、`j₋₃ ≤ j₋₂ < Lng M - 1`。 -/
theorem Regs_jm3Marked_holds : Regs_jm3Marked := by
  intro M hMR hMT hp
  have jm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have jm2L : s84x_jm2 M ≤ Lng M - 1 := le_of_lt jm2lt
  -- `s84x_jm3 M = Adm M (s84x_jm2 M)` は定義上等しい
  have jm3le : s84x_jm3 M ≤ s84x_jm2 M := Adm_le M (s84x_jm2 M)
  have admjm3 : adm M (s84x_jm3 M) = true := Adm_adm M (s84x_jm2 M)
  have le1a : leR M 1 (s84x_jm3 M) (s84x_jm2 M) = true :=
    adm_row1_ancestry_ps M (s84x_jm2 M) hMT jm2L
  have le0a : leR M 0 (s84x_jm3 M) (s84x_jm2 M) = true :=
    row1_implies_row0_at M (s84x_jm3 M) (s84x_jm2 M) hMT le1a
  have le0b : leR M 0 (s84x_jm2 M) (Lng M - 1) = true := by
    have h := (s84c1_jm2_basic M hp).2.2
    simpa [leR] using h
  have le0c : leR M 0 (s84x_jm3 M) (Lng M - 1) = true :=
    row0_transitive M (s84x_jm3 M) (s84x_jm2 M) (Lng M - 1) hMT le0a le0b
  exact ⟨⟨hMT, admjm3, le0c⟩, jm3le, jm2lt⟩

/-! ## 2. private helpers -/

/-- `le0Aux` の反射性。 -/
private theorem le0Aux_refl_mc (M : PS) (fuel a : ℕ) : le0Aux M fuel a a = true := by
  cases fuel <;> simp [le0Aux]

/-- `le0` の反射性（`a < Lng M`）。 -/
private theorem le0_refl_mc (M : PS) (a : ℕ) (ha : a < Lng M) : le0 M a a = true := by
  simp [le0, ha, le0Aux_refl_mc]

/-- Isabelle `a1_FN_hasParent` (pss_mechanized.thy:33161)。枝成分の左端は行0の親を持つ。 -/
private theorem FN_hasParent_mc (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) :
    hasParent M 0 ((FirstNodes M).getD J 0) = true := by
  have hbound := TrMax_bound M hM
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    have hBr0 : Br M = [] := by simp [Br, heq]
    rw [hBr0] at hJ; simp at hJ
  have htrlt : TrMax M < Lng M - 1 := by omega
  have hBr : Br M = P (seg M (TrMax M + 1) (Lng M - 1)) := by simp [Br, hne]
  have hJQ : J ≤ (P (seg M (TrMax M + 1) (Lng M - 1))).length - 1 := by rw [← hBr]; omega
  have hn := mono_slice_next M (TrMax M + 1) J hM hmono (by omega) (by omega) hJQ
  have hfn := FirstNodes_getD M J hJ
  rw [hfn, hBr]
  exact hn.1

/-- Isabelle `Joints_parent_nextR` (pss_mechanized.thy:6170)。 -/
private theorem Joints_parent_nextR_mc (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) :
    nextR M 0 ((Joints M).getD J 0) ((FirstNodes M).getD J 0) = true := by
  have hp := FN_hasParent_mc M J hM hmono hJ
  have hnext := hasParent_next_fseq M 0 ((FirstNodes M).getD J 0) hp
  rw [Joints_getD M J hJ]
  exact hnext

/-- Isabelle `a1_FN_lt` (pss_mechanized.thy:33186)。 -/
private theorem FN_lt_mc (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) :
    (FirstNodes M).getD J 0 < Lng M := by
  have h := Joints_parent_nextR_mc M J hM hmono hJ
  have hn : nextrel0 M ((Joints M).getD J 0) ((FirstNodes M).getD J 0) = true := by
    simpa [nextR] using h
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hn
  exact hn.1.1.1.2

/-- Isabelle `m_8_4_oper_props_1(1)` (layerB/pss_wip.thy:52810) の内訳:
条件(III)/(IV) の下で行1の親 `j₋₂` は行0の親 `transJ0` より真に手前。
公開の親最大性 `nextR0_largest_below`（§6.4）で `j₋₂ ≤ transJ0`、行1係数比較で
`j₋₂ ≠ transJ0`。 -/
private theorem jm2_lt_transJ0_mc (M : PS)
    (hMT : TPS M) (hmono : monoT M = true) (hp : hasParent M 1 (Lng M - 1) = true)
    (j1gt : 1 < Lng M - 1) (branch : transCondIII M = true ∨ transCondIV M = true) :
    s84x_jm2 M < transJ0 M := by
  have jm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hMT hmono (Lng M - 1) (by omega) (by omega)
  have hnext0 : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
    show nextR M 0 (parent M 0 (Lng M - 1)) (Lng M - 1) = true
    exact hasParent_next_fseq M 0 (Lng M - 1) hp0
  have le0jm2 : leR M 0 (s84x_jm2 M) (Lng M - 1) = true := by
    have h := (s84c1_jm2_basic M hp).2.2
    simpa [leR] using h
  have hent0 : entry M 0 (s84x_jm2 M) < entry M 0 (Lng M - 1) :=
    ancestor_basic_1 M (s84x_jm2 M) (Lng M - 1) (Lng M - 1) hMT jm2lt (le_refl _) le0jm2
  have jm2le : s84x_jm2 M ≤ transJ0 M :=
    nextR0_largest_below M (transJ0 M) (s84x_jm2 M) (Lng M - 1) hnext0 jm2lt hent0
  have hge : entry M 1 (Lng M - 1) ≤ entry M 1 (transJ0 M) := by
    rcases branch with h | h
    · have h' := h
      simp only [transCondIII, Bool.and_eq_true, decide_eq_true_eq] at h'
      show entry M 1 (lastIdx M) ≤ entry M 1 (lastParent M)
      exact h'.1.2
    · have h' := h
      simp only [transCondIV, Bool.and_eq_true, decide_eq_true_eq] at h'
      show entry M 1 (lastIdx M) ≤ entry M 1 (lastParent M)
      exact h'.1.2
  have hlt1 : entry M 1 (s84x_jm2 M) < entry M 1 (Lng M - 1) := (s84c1_jm2_basic M hp).2.1
  have hne : s84x_jm2 M ≠ transJ0 M := by
    intro heq
    rw [heq] at hlt1
    omega
  omega

/-- Isabelle `crx_trmax_run` (layerB/pss_wip.thy:89879)。非許容 run `(j₋₃, j₋₂]` の
各点で行1後続辺が立つので、簡約スライスへ転送すると `TrMax` の下界が出る。 -/
private theorem crx_trmax_run_mc (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (guard : s84x_jm3 M < s84x_jm2 M) :
    s84x_jm2 M - s84x_jm3 M + 1 ≤ TrMax (Red (s84x_N M)) := by
  have MT : TPS M := RTPS_TPS M hMR
  have jm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have jm3le : s84x_jm3 M ≤ s84x_jm2 M := Adm_le M (s84x_jm2 M)
  have jm3lt : s84x_jm3 M < Lng M - 1 := lt_trans guard jm2lt
  have mM3 : Marked M (s84x_jm3 M) := (Regs_jm3Marked_holds M hMR MT hp).1
  have leR3 : leR M 0 (s84x_jm3 M) (Lng M - 1) = true := mM3.2.2
  have hlenN : Lng (s84x_N M) = Lng M - s84x_jm3 M := by
    show Lng (seg M (s84x_jm3 M) (Lng M - 1)) = Lng M - s84x_jm3 M
    rw [length_seg]; omega
  have NT : TPS (s84x_N M) := by
    have hpos : 0 < Lng (s84x_N M) := by rw [hlenN]; omega
    intro hnil; rw [hnil] at hpos; simp [Lng] at hpos
  have LngRN : Lng (Red (s84x_N M)) = Lng (s84x_N M) := Lng_Red_invariance (s84x_N M) NT
  have hLngRNval : Lng (Red (s84x_N M)) = Lng M - s84x_jm3 M := LngRN.trans hlenN
  have RNT : TPS (Red (s84x_N M)) := by
    intro hnil
    have h0 : Lng (Red (s84x_N M)) = 0 := by rw [hnil]; rfl
    rw [hLngRNval] at h0; omega
  have segIF : s84x_N M
      = IncrFirstN (entry M 0 (s84x_jm3 M) - entry M 1 (s84x_jm3 M)) (Red (s84x_N M)) :=
    (ancestor_slice_Red_IncrFirst M (s84x_jm3 M) (Lng M - 1) hMR jm3lt (le_refl _) leR3).2.2
  -- 非許容 run
  have nadmk : ∀ k, s84x_jm3 M < k → k ≤ s84x_jm2 M → nadm M k = true := by
    intro k hk1 hk2
    by_contra hcon
    have hnf : nadm M k = false := by
      cases h : nadm M k with
      | false => rfl
      | true => exact absurd h hcon
    have hadm : adm M k = true := by simp [adm, hnf]
    have hle3 : k ≤ s84x_jm3 M := Adm_max M k (s84x_jm2 M) hadm hk2
    omega
  have stepM : ∀ k, s84x_jm3 M ≤ k → k ≤ s84x_jm2 M → nextR M 1 k (k + 1) = true := by
    intro k hk1 hk2
    by_cases hkeq : k = s84x_jm2 M
    · have hnadm : nadm M (s84x_jm2 M) = true := nadmk (s84x_jm2 M) guard (le_refl _)
      rw [hkeq]
      simp only [nadm, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hnadm
      rcases hnadm with h | h
      · exact absurd h (by omega)
      · exact h.2
    · have hklt : k < s84x_jm2 M := lt_of_le_of_ne hk2 hkeq
      have hnadm : nadm M (k + 1) = true := nadmk (k + 1) (by omega) (by omega)
      simp only [nadm, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hnadm
      rcases hnadm with h | h
      · exact absurd h (by omega)
      · have hh := h.1
        rwa [show k + 1 - 1 = k from by omega] at hh
  -- reduced スライスへ転送
  have jm3leLm1 : s84x_jm3 M ≤ Lng M - 1 := le_of_lt jm3lt
  have j1L : Lng M - 1 < Lng M := by omega
  have stepRN : ∀ j', j' < (s84x_jm2 M - s84x_jm3 M) + 1 →
      nextR (Red (s84x_N M)) 1 j' (j' + 1) = true := by
    intro j' jlt
    have ha : j' < Lng (seg M (s84x_jm3 M) (Lng M - 1)) := by rw [length_seg]; omega
    have hb : j' + 1 < Lng (seg M (s84x_jm3 M) (Lng M - 1)) := by rw [length_seg]; omega
    have kk1 : s84x_jm3 M ≤ s84x_jm3 M + j' := by omega
    have kk2 : s84x_jm3 M + j' ≤ s84x_jm2 M := by omega
    have hstepM : nextR M 1 (s84x_jm3 M + j') (s84x_jm3 M + (j' + 1)) = true := by
      have h := stepM (s84x_jm3 M + j') kk1 kk2
      rwa [show s84x_jm3 M + j' + 1 = s84x_jm3 M + (j' + 1) from by omega] at h
    have hseg := nextR1_seg_adm M (s84x_jm3 M) (Lng M - 1) j' (j' + 1) jm3leLm1 j1L ha hb
    have hsegVal : nextR (s84x_N M) 1 j' (j' + 1) = true := by
      show nextR (seg M (s84x_jm3 M) (Lng M - 1)) 1 j' (j' + 1) = true
      rw [hseg]; exact hstepM
    rw [segIF] at hsegVal
    rwa [nextR_IncrFirstN_ri] at hsegVal
  have allsteps : ∀ j' < (s84x_jm2 M - s84x_jm3 M) + 1,
      nextR (Red (s84x_N M)) 1 j' (j' + 1) = true := stepRN
  exact le_TrMax_intro_wd (Red (s84x_N M)) ((s84x_jm2 M - s84x_jm3 M) + 1) RNT allsteps

/-! ## 3. `Regs_MCOND`（= `mcx_MCOND_RN`）の drop-in -/

/-- Isabelle `mcx_MCOND_RN` (layerB/pss_wip.thy:93796, ~200 行) の house-pattern drop-in。
`≤` core（`d < TrMax RN < fn ≤ T` から `d ≤ jl`）＋ 等号枝の対角性
（`d = jl` ⟹ `Red(N)_{0,fn} = Red(N)_{1,fn}`：RedCondA 行0/行1・trunk-offset・
valley・reduced-coeff の挟み撃ち）。 -/
theorem Regs_MCOND_holds : Regs_MCOND := by
  intro M hST hmono hp j1gt branch guard
  rw [show VEj1p (Red (s84x_N M))
        = (FirstNodes (Red (s84x_N M))).getD ((Br (Red (s84x_N M))).length - 1) 0 from rfl]
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have jm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have jm3le : s84x_jm3 M ≤ s84x_jm2 M := Adm_le M (s84x_jm2 M)
  have jm3lt : s84x_jm3 M < Lng M - 1 := lt_of_le_of_lt jm3le jm2lt
  have mM3 : Marked M (s84x_jm3 M) := (Regs_jm3Marked_holds M hMR hMT hp).1
  have leR3 : leR M 0 (s84x_jm3 M) (Lng M - 1) = true := mM3.2.2
  have ND : DTPS (Red (s84x_N M)) :=
    standard_slice_Red_strongmono M (s84x_jm3 M) (Lng M - 1) hST jm3lt (le_refl _) leR3
  have RNRT : RTPS (Red (s84x_N M)) := ((DTPS_iff _).mp ND).1
  have monoRN : monoT (Red (s84x_N M)) = true := ((DTPS_iff _).mp ND).2.1
  have RNT : TPS (Red (s84x_N M)) := RTPS_TPS _ RNRT
  have hlenN : Lng (s84x_N M) = Lng M - s84x_jm3 M := by
    show Lng (seg M (s84x_jm3 M) (Lng M - 1)) = Lng M - s84x_jm3 M
    rw [length_seg]; omega
  have NT : TPS (s84x_N M) := by
    have hpos : 0 < Lng (s84x_N M) := by rw [hlenN]; omega
    intro hnil; rw [hnil] at hpos; simp [Lng] at hpos
  have LngRN : Lng (Red (s84x_N M)) = Lng (s84x_N M) := Lng_Red_invariance (s84x_N M) NT
  have hLngRNval : Lng (Red (s84x_N M)) = Lng M - s84x_jm3 M := LngRN.trans hlenN
  have segIF : s84x_N M
      = IncrFirstN (entry M 0 (s84x_jm3 M) - entry M 1 (s84x_jm3 M)) (Red (s84x_N M)) :=
    (ancestor_slice_Red_IncrFirst M (s84x_jm3 M) (Lng M - 1) hMR jm3lt (le_refl _) leR3).2.2
  -- j₋₂ < transJ0 < Lng M - 1 ⟹ j₋₂ < Lng M - 2
  have jm2ltj0 : s84x_jm2 M < transJ0 M := jm2_lt_transJ0_mc M hMT hmono hp j1gt branch
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hMT hmono (Lng M - 1) (by omega) (by omega)
  have j0lt : transJ0 M < Lng M - 1 := by
    show lastParent M < Lng M - 1
    show parent M 0 (lastIdx M) < Lng M - 1
    exact parent_lt_of_hasParent M 0 (Lng M - 1) hp0
  have jm2lt1 : s84x_jm2 M < Lng M - 2 := by omega
  have notnx1 : nextR M 1 (Lng M - 1 - 1) (Lng M - 1) = true → False := by
    intro H
    have huniq := nextR1_unique_mr M (Lng M - 1 - 1) (s84x_jm2 M) (Lng M - 1) H
      (s84c1_nextR1_jm2 M hp)
    omega
  have run0 : s84x_jm2 M - s84x_jm3 M + 1 ≤ TrMax (Red (s84x_N M)) :=
    crx_trmax_run_mc M hMR hp guard
  set RN := Red (s84x_N M) with hRN
  have LRN2 : 2 ≤ Lng RN := by rw [hLngRNval]; omega
  have jm3leLm1 : s84x_jm3 M ≤ Lng M - 1 := le_of_lt jm3lt
  have j1L : Lng M - 1 < Lng M := by omega
  -- `Br RN ≠ []`（regs の Brne と同一構造）
  have a1 : Lng RN - 2 < Lng (seg M (s84x_jm3 M) (Lng M - 1)) := by rw [length_seg]; omega
  have a2 : Lng RN - 1 < Lng (seg M (s84x_jm3 M) (Lng M - 1)) := by rw [length_seg]; omega
  have hseg := nextR1_seg_adm M (s84x_jm3 M) (Lng M - 1) (Lng RN - 2) (Lng RN - 1)
    jm3leLm1 j1L a1 a2
  have idxA : s84x_jm3 M + (Lng RN - 2) = Lng M - 1 - 1 := by omega
  have idxB : s84x_jm3 M + (Lng RN - 1) = Lng M - 1 := by omega
  have Brne : Br RN ≠ [] := by
    intro Bemp
    have trmaxeq : TrMax RN = Lng RN - 1 := by
      by_contra ne
      have hBr : Br RN = P (seg RN (TrMax RN + 1) (Lng RN - 1)) := by
        unfold Br; rw [if_neg ne]
      rw [hBr] at Bemp
      exact P_nonempty _ Bemp
    have lt2 : Lng RN - 2 < TrMax RN := by rw [trmaxeq]; omega
    have stepN_seg : nextR (seg M (s84x_jm3 M) (Lng M - 1)) 1 (Lng RN - 2) (Lng RN - 1)
        = true := by
      have e : seg M (s84x_jm3 M) (Lng M - 1) = s84x_N M := rfl
      rw [e, segIF, nextR_IncrFirstN_ri]
      have step2 := TrMax_trunk_step RN (Lng RN - 2) RNT lt2
      rwa [show Lng RN - 2 + 1 = Lng RN - 1 from by omega] at step2
    rw [hseg, idxA, idxB] at stepN_seg
    exact notnx1 stepN_seg
  set d := s84x_jm2 M - s84x_jm3 M with hd_def
  set last := (Br RN).length - 1 with hlast_def
  have hposBr : 0 < (Br RN).length := List.length_pos_of_ne_nil Brne
  have lastLt : last < (Br RN).length := by rw [hlast_def]; omega
  -- `≤` core
  have dltTr : d < TrMax RN := by omega
  have trfn : TrMax RN < (FirstNodes RN).getD last 0 :=
    (FirstNodes_TrMax_Joints RN last RNT monoRN lastLt).2
  have dltfn : d < (FirstNodes RN).getD last 0 := by omega
  have fnLt : (FirstNodes RN).getD last 0 < Lng RN := FN_lt_mc RN last RNT monoRN lastLt
  have fnleT : (FirstNodes RN).getD last 0 ≤ Lng RN - 1 := by omega
  have nxM1 : nextR M 1 (s84x_jm2 M) (Lng M - 1) = true := s84c1_nextR1_jm2 M hp
  have dLtLN : d < Lng (seg M (s84x_jm3 M) (Lng M - 1)) := by rw [length_seg]; omega
  have TLtLN : Lng RN - 1 < Lng (seg M (s84x_jm3 M) (Lng M - 1)) := by rw [length_seg]; omega
  have segb1 := nextR1_seg_adm M (s84x_jm3 M) (Lng M - 1) d (Lng RN - 1)
    jm3leLm1 j1L dLtLN TLtLN
  have idxd : s84x_jm3 M + d = s84x_jm2 M := by omega
  have idxT : s84x_jm3 M + (Lng RN - 1) = Lng M - 1 := by omega
  have nxN1 : nextR (s84x_N M) 1 d (Lng RN - 1) = true := by
    show nextR (seg M (s84x_jm3 M) (Lng M - 1)) 1 d (Lng RN - 1) = true
    rw [segb1, idxd, idxT]; exact nxM1
  have nxRN1 : nextR RN 1 d (Lng RN - 1) = true := by
    rw [segIF] at nxN1
    rwa [nextR_IncrFirstN_ri] at nxN1
  have le0dT : le0 RN d (Lng RN - 1) = true := by
    have hn : nextrel1 RN d (Lng RN - 1) = true := by simpa [nextR] using nxRN1
    simp only [nextrel1, Bool.and_eq_true] at hn
    exact hn.1.2
  have leRdT : leR RN 0 d (Lng RN - 1) = true := by simpa [leR] using le0dT
  have ent : entry RN 0 d < entry RN 0 ((FirstNodes RN).getD last 0) :=
    ancestor_basic_1 RN d ((FirstNodes RN).getD last 0) (Lng RN - 1) RNT dltfn fnleT leRdT
  have nxjl : nextR RN 0 ((Joints RN).getD last 0) ((FirstNodes RN).getD last 0) = true :=
    Joints_parent_nextR_mc RN last RNT monoRN lastLt
  have dlejl : d ≤ (Joints RN).getD last 0 :=
    nextR0_largest_below RN ((Joints RN).getD last 0) d ((FirstNodes RN).getD last 0)
      nxjl dltfn ent
  by_cases hdj : d = (Joints RN).getD last 0
  · -- 等号枝: 対角性
    right
    refine ⟨hdj, ?_⟩
    obtain ⟨condA_RN, condB_RN⟩ := RTPS_condAB RN RNRT
    have hpfn0 : hasParent RN 0 ((FirstNodes RN).getD last 0) = true :=
      FN_hasParent_mc RN last RNT monoRN lastLt
    have parfn : parent RN 0 ((FirstNodes RN).getD last 0) = (Joints RN).getD last 0 :=
      (Joints_getD RN last lastLt).symm
    have pfd : parent RN 0 ((FirstNodes RN).getD last 0) = d := by rw [parfn, ← hdj]
    have e0fn : entry RN 0 (parent RN 0 ((FirstNodes RN).getD last 0)) + 1
        = entry RN 0 ((FirstNodes RN).getD last 0) :=
      RedCondA_apply RN condA_RN 0 ((FirstNodes RN).getD last 0) (by norm_num) fnLt hpfn0
    have e0fn' : entry RN 0 d + 1 = entry RN 0 ((FirstNodes RN).getD last 0) := by
      rw [← pfd]; exact e0fn
    have dTr : d ≤ TrMax RN := by omega
    have e00 : entry RN 0 0 = entry RN 1 0 := RedCondB_head_eq RN RNT condB_RN
    have offs := trunk_entries_offset RN RNT condA_RN d dTr
    have ediag_d : entry RN 0 d = entry RN 1 d := by rw [offs.1, offs.2, e00]
    have e0fn_v : entry RN 0 ((FirstNodes RN).getD last 0) = entry RN 1 d + 1 := by
      rw [← e0fn', ediag_d]
    -- 終端 `T = Lng RN - 1` での行1親
    have huniqT : ∀ y, nextR RN 1 y (Lng RN - 1) = true → y = d :=
      fun y hy => nextR1_unique_mr RN y d (Lng RN - 1) hy nxRN1
    have hp1T : hasParent RN 1 (Lng RN - 1) = true :=
      (hasParent_iff_unique_fseq RN 1 (Lng RN - 1)).mpr ⟨d, nxRN1, huniqT⟩
    have par1T : parent RN 1 (Lng RN - 1) = d :=
      parent_eq_of_unique_fseq RN 1 (Lng RN - 1) d nxRN1 huniqT
    have TLtRN : Lng RN - 1 < Lng RN := by omega
    have e1T : entry RN 1 (parent RN 1 (Lng RN - 1)) + 1 = entry RN 1 (Lng RN - 1) :=
      RedCondA_apply RN condA_RN 1 (Lng RN - 1) (by norm_num) TLtRN hp1T
    have e1T' : entry RN 1 d + 1 = entry RN 1 (Lng RN - 1) := by rw [← par1T]; exact e1T
    -- `le0 RN fn T`（最終枝成分が monoT）
    have le0fnT : le0 RN ((FirstNodes RN).getD last 0) (Lng RN - 1) = true := by
      by_cases hfnT : (FirstNodes RN).getD last 0 = Lng RN - 1
      · rw [hfnT]; exact le0_refl_mc RN (Lng RN - 1) TLtRN
      · have fltT : (FirstNodes RN).getD last 0 < Lng RN - 1 := lt_of_le_of_ne fnleT hfnT
        have blkeq : (Br RN).getD last []
            = seg RN ((FirstNodes RN).getD last 0) (Lng RN - 1) := by
          have h := wf21_Br_eq_seg RN RNT Brne
          rw [hlast_def]; exact h
        have znm := Br_component_nonmulti RN last RNT lastLt
        have LblkGe2 : 2 ≤ Lng ((Br RN).getD last []) := by
          rw [blkeq, length_seg]; omega
        have notz : zeroT ((Br RN).getD last []) ≠ true := by
          intro hz
          simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
          omega
        have monoblk : monoT ((Br RN).getD last []) = true := by
          rcases znm with h | h
          · exact absurd h notz
          · exact h
        rw [blkeq] at monoblk
        exact le0_monoT_seg_into_list RN ((FirstNodes RN).getD last 0) (Lng RN - 1)
          (Lng RN - 1) RNT monoblk fnleT (le_refl _) TLtRN
    -- valley
    have nr1 : nextrel1 RN d (Lng RN - 1) = true := by simpa [nextR] using nxRN1
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at nr1
    obtain ⟨_, hF⟩ := nr1
    have hfnrange : (FirstNodes RN).getD last 0 ∈ List.range (Lng RN) :=
      List.mem_range.mpr fnLt
    have hbody := hF ((FirstNodes RN).getD last 0) hfnrange
    have hdfn : decide (d < (FirstNodes RN).getD last 0) = true := by
      simp only [decide_eq_true_eq]; exact dltfn
    rw [hdfn, le0fnT] at hbody
    simp only [Bool.and_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hbody
    have lower : entry RN 1 d + 1 ≤ entry RN 1 ((FirstNodes RN).getD last 0) := by
      rw [e1T']; exact hbody
    have upper : entry RN 1 ((FirstNodes RN).getD last 0)
        ≤ entry RN 0 ((FirstNodes RN).getD last 0) :=
      reduced_coeff RN RNRT ((FirstNodes RN).getD last 0) fnLt
    omega
  · left
    omega

#print axioms Regs_jm3Marked_holds
#print axioms Regs_MCOND_holds

end PSS
