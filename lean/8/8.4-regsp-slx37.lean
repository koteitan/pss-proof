import «8».«8.4-exch84-regsp»
import «8».«8.4-exch84-mcond»
import «6».«6.5-Red-Pred-commute»
import «7».«7.4-Mark-Trans-repr»

/-!
# §8.4 交換パッケージ `REGSP` 脚の共通鍵 `Regsp_slx37_regSP`（= Isabelle `slx37_regSP_uncond`）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
- 対象: ビルド済みの named Prop `Regsp_slx37_regSP`（«8».«8.4-exch84-regsp»:144、
  Isabelle `slx37_regSP_uncond` layerB/pss_wip.thy:97329 の Lean 語彙形）。
  `slicepkg` の `REGSP` 脚と `NestScbD4aReducedValue` の共通鍵。

## Isabelle 側のルート（本ファイルが移植するもの）

`slx37_regSP_uncond` は `lb2x_regSP_of_lt_eqd[OF … slx37_strictlt_eqd]`（:96435）で、
これは 2 段に分かれる:

1. `mcx_regSP_of_diag`（:94051）: 前スライス `RN' = Red (Pred (s84x_N M))` に対して
   `d ≤ jlp`（`d = j₋₂-j₋₃`, `jlp = Joints RN' ! last`）を**祖先木**で示し
   （`crx_trmax_run` + `TrMax` 経由 ＋ `leR0_seg_adm`/`leR_IncrFirstN` の切片転送）、
   等号枝の対角性 `DIAG` を仮定として `cfbx_reg`（= `VEReg`）の論理和を組む。
2. `dgx_regSP_diag_of_lt`（:94864）: `d = jlp` の下で尖った不等式
   `RN'_{1,d} < RN'_{1,fnp}`（= `strictlt`）から対角性 `RN'_{0,fnp} = RN'_{1,fnp}` を
   `RedCondA` 行0 ＋ 幹対角 ＋ `reduced_coeff` の挟み撃ちで出す。

これらを合わせると `Regsp_slx37_regSP` は **ただ 1 本の尖った不等式 `strictlt`**
（Isabelle `slx37_strictlt_eqd` :97052、`eqd` 仮定付き）に還元される。

## 本ファイルの成果物（house pattern）

- `RegspStrictlt_sx`（named Prop）: Isabelle `slx37_strictlt_eqd` を Lean 語彙で述べた
  尖った残差（`d = jlp` の下で `RN'_{1,d} < RN'_{1,fnp}`）。
- `Regsp_disj_sharp_of_strictlt`: `RegspStrictlt_sx → Regsp_disj_sharp`（«8».«8.4-exch84-regsp»）。
  `mcx_regSP_of_diag` の `≤` core ＋ `dgx_regSP_diag_of_lt` の対角挟み撃ちを完全移植。
- `Regsp_slx37_regSP_of_strictlt`: `RegspStrictlt_sx → Regsp_slx37_regSP`。
  ビルド済みの `Regsp_of_disj_sharp`（«8».«8.4-exch84-regsp»）と `Regs_jm3Marked_holds`
  （«8».«8.4-exch84-mcond»）に接続。

つまり `REGSP` 脚 ＝ `NestScbD4aReducedValue` の共通鍵は、残る**単一の尖った不等式**
`RegspStrictlt_sx`（Isabelle `slx37_strictlt_eqd`、`wid_*_Pred`/`mcx_MCOND_RN` 依存の
last-branch tie-break）に無条件還元された。

- 依存（すべてビルド済み・committed）: «8».«8.4-exch84-regsp»（`Regsp_slx37_regSP`/
  `Regsp_disj_sharp`/`Regsp_of_disj_sharp`）、«8».«8.4-exch84-mcond»（`Regs_jm3Marked_holds`
  ＋推移的に `standard_slice_Red_strongmono`/`ancestor_slice_Red_IncrFirst`/`leR0_seg_adm`/
  `leR_IncrFirstN`/`ancestor_tree_1`/`ancestor_basic_1`/`nextR0_largest_below`/
  `Joints_nextR_FirstNodes`/`FirstNodes_TrMax_Joints`/`trunk_entries_offset`/
  `RedCondA_apply`/`RedCondB_head_eq`/`reduced_coeff`/`nextR1_seg_adm`/
  `nextR_IncrFirstN_ri`/`le_TrMax_intro_wd`/`mono_slice_next`/`Adm_*`/`s84c1_*`）、
  «6».«6.5-Red-Pred-commute»（`Red_Pred`）、«7».«7.4-Mark-Trans-repr»
  （`Pred_Red_terminal_slice`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  残差 = 単一 named Prop `RegspStrictlt_sx`。
- Private helper suffix: `_sx`。
-/

namespace PSS

/-! ## 1. private 補助（suffix `_sx`） -/

/-- Isabelle `a1_FN_hasParent` (pss_mechanized.thy:33161)。枝成分の左端は行0の親を持つ。
（«8».«8.4-exch84-mcond» の private 版 `FN_hasParent_mc` の再掲、public 基本列言い換え版）。 -/
private theorem FN_hasParent_sx (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
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

/-- Isabelle `a1_FN_lt` (pss_mechanized.thy:33186)。枝成分の左端は `Lng` 未満。 -/
private theorem FN_lt_sx (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) :
    (FirstNodes M).getD J 0 < Lng M := by
  have h := Joints_nextR_FirstNodes M J hM hmono hJ
  have hn : nextrel0 M ((Joints M).getD J 0) ((FirstNodes M).getD J 0) = true := by
    simpa [nextR] using h
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hn
  exact hn.1.1.1.2

/-- Isabelle `m_8_4_oper_props_1(1)` (layerB/pss_wip.thy:52810) の内訳:
条件(III)/(IV) の下で行1の親 `j₋₂` は行0の親 `transJ0` より真に手前。
（«8».«8.4-exch84-mcond» の private 版 `jm2_lt_transJ0_mc` の再掲。） -/
private theorem jm2_lt_transJ0_sx (M : PS)
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

/-- Isabelle `crx_trmax_run` (layerB/pss_wip.thy:89879) の**前スライス版**。
非許容 run `(j₋₃, j₋₂]` の各点で行1後続辺が立ち、前スライス
`Np = seg M j₋₃ (Lng M - 2)` へ直接転送すると `TrMax (Red Np)` の下界が出る
（全スライス経由 ＋ `TrMax_Pred` を要しない）。 -/
private theorem trmax_run_pre_sx (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hmono : monoT M = true)
    (j1gt : 1 < Lng M - 1) (branch : transCondIII M = true ∨ transCondIV M = true)
    (guard : s84x_jm3 M < s84x_jm2 M) :
    s84x_jm2 M - s84x_jm3 M + 1 ≤ TrMax (Red (seg M (s84x_jm3 M) (Lng M - 2))) := by
  have MT : TPS M := RTPS_TPS M hMR
  have jm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have jm3le : s84x_jm3 M ≤ s84x_jm2 M := Adm_le M (s84x_jm2 M)
  have jm2ltj0 : s84x_jm2 M < transJ0 M := jm2_lt_transJ0_sx M MT hmono hp j1gt branch
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M MT hmono (Lng M - 1) (by omega) (by omega)
  have j0lt : transJ0 M < Lng M - 1 := by
    show lastParent M < Lng M - 1
    show parent M 0 (lastIdx M) < Lng M - 1
    exact parent_lt_of_hasParent M 0 (Lng M - 1) hp0
  have jm2lt1 : s84x_jm2 M < Lng M - 2 := by omega
  have jm3ltLm2 : s84x_jm3 M < Lng M - 2 := lt_trans guard jm2lt1
  have jm3leLm2 : s84x_jm3 M ≤ Lng M - 2 := le_of_lt jm3ltLm2
  have leR3 : leR M 0 (s84x_jm3 M) (Lng M - 1) = true :=
    (Regs_jm3Marked_holds M hMR MT hp).1.2.2
  have leR3Lm2 : leR M 0 (s84x_jm3 M) (Lng M - 2) = true :=
    ancestor_tree_1 M (s84x_jm3 M) (Lng M - 2) (Lng M - 1) MT leR3 jm3leLm2 (by omega)
  have NpT : TPS (seg M (s84x_jm3 M) (Lng M - 2)) := by
    have hpos : 0 < Lng (seg M (s84x_jm3 M) (Lng M - 2)) := by rw [length_seg]; omega
    intro hnil; rw [hnil] at hpos; simp [Lng] at hpos
  have segIF : seg M (s84x_jm3 M) (Lng M - 2)
      = IncrFirstN (entry M 0 (s84x_jm3 M) - entry M 1 (s84x_jm3 M))
          (Red (seg M (s84x_jm3 M) (Lng M - 2))) :=
    (ancestor_slice_Red_IncrFirst M (s84x_jm3 M) (Lng M - 2) hMR jm3ltLm2 (by omega) leR3Lm2).2.2
  have RNpT : TPS (Red (seg M (s84x_jm3 M) (Lng M - 2))) := by
    intro hnil
    have h0 : Lng (Red (seg M (s84x_jm3 M) (Lng M - 2))) = 0 := by rw [hnil]; rfl
    rw [Lng_Red_invariance _ NpT, length_seg] at h0; omega
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
  have stepRN : ∀ j', j' < (s84x_jm2 M - s84x_jm3 M) + 1 →
      nextR (Red (seg M (s84x_jm3 M) (Lng M - 2))) 1 j' (j' + 1) = true := by
    intro j' jlt
    have ha : j' < Lng (seg M (s84x_jm3 M) (Lng M - 2)) := by rw [length_seg]; omega
    have hb : j' + 1 < Lng (seg M (s84x_jm3 M) (Lng M - 2)) := by rw [length_seg]; omega
    have kk1 : s84x_jm3 M ≤ s84x_jm3 M + j' := by omega
    have kk2 : s84x_jm3 M + j' ≤ s84x_jm2 M := by omega
    have hstepM : nextR M 1 (s84x_jm3 M + j') (s84x_jm3 M + (j' + 1)) = true := by
      have h := stepM (s84x_jm3 M + j') kk1 kk2
      rwa [show s84x_jm3 M + j' + 1 = s84x_jm3 M + (j' + 1) from by omega] at h
    have hseg := nextR1_seg_adm M (s84x_jm3 M) (Lng M - 2) j' (j' + 1) jm3leLm2 (by omega) ha hb
    have hsegVal : nextR (seg M (s84x_jm3 M) (Lng M - 2)) 1 j' (j' + 1) = true := by
      rw [hseg]; exact hstepM
    rw [segIF, nextR_IncrFirstN_ri] at hsegVal
    exact hsegVal
  exact le_TrMax_intro_wd (Red (seg M (s84x_jm3 M) (Lng M - 2)))
    ((s84x_jm2 M - s84x_jm3 M) + 1) RNpT stepRN

/-! ## 2. `Regsp_disj_sharp` を単一の尖った `strictlt` から組む -/

/-- 前スライス `RN' = Red (Pred (s84x_N M))` に対して、`mcx_regSP_of_diag` の `≤` core
（祖先木で `d ≤ jlp`）と `dgx_regSP_diag_of_lt` の対角挟み撃ち（`d = jlp` の下で
`strictlt_eq` から対角性）を合わせ、`Regsp_disj_sharp` の論理和を組む。 -/
private theorem regsp_disj_of_strictlt_sx (M : PS)
    (hST : STPS M) (hmono : monoT M = true) (hp : hasParent M 1 (Lng M - 1) = true)
    (j1gt : 1 < Lng M - 1) (branch : transCondIII M = true ∨ transCondIV M = true)
    (guard : s84x_jm3 M < s84x_jm2 M)
    (Brne' : Br (Red (Pred (s84x_N M))) ≠ [])
    (strictlt_eq : s84x_jm2 M - s84x_jm3 M
          = (Joints (Red (Pred (s84x_N M)))).getD
              ((Br (Red (Pred (s84x_N M)))).length - 1) 0 →
        entry (Red (Pred (s84x_N M))) 1 (s84x_jm2 M - s84x_jm3 M)
          < entry (Red (Pred (s84x_N M))) 1
              ((FirstNodes (Red (Pred (s84x_N M)))).getD
                ((Br (Red (Pred (s84x_N M)))).length - 1) 0)) :
    (s84x_jm2 M - s84x_jm3 M
        < (Joints (Red (Pred (s84x_N M)))).getD
            ((Br (Red (Pred (s84x_N M)))).length - 1) 0
      ∨ (s84x_jm2 M - s84x_jm3 M
           = (Joints (Red (Pred (s84x_N M)))).getD
               ((Br (Red (Pred (s84x_N M)))).length - 1) 0
         ∧ entry (Red (Pred (s84x_N M))) 0 (VEj1p (Red (Pred (s84x_N M))))
           = entry (Red (Pred (s84x_N M))) 1 (VEj1p (Red (Pred (s84x_N M)))))) := by
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have jm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have jm3le : s84x_jm3 M ≤ s84x_jm2 M := Adm_le M (s84x_jm2 M)
  have jm3lt : s84x_jm3 M < Lng M - 1 := lt_of_le_of_lt jm3le jm2lt
  have leR3 : leR M 0 (s84x_jm3 M) (Lng M - 1) = true :=
    (Regs_jm3Marked_holds M hMR hMT hp).1.2.2
  -- j₋₂ < Lng M - 2
  have jm2ltj0 : s84x_jm2 M < transJ0 M := jm2_lt_transJ0_sx M hMT hmono hp j1gt branch
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hMT hmono (Lng M - 1) (by omega) (by omega)
  have j0lt : transJ0 M < Lng M - 1 := by
    show lastParent M < Lng M - 1
    show parent M 0 (lastIdx M) < Lng M - 1
    exact parent_lt_of_hasParent M 0 (Lng M - 1) hp0
  have jm2lt1 : s84x_jm2 M < Lng M - 2 := by omega
  have jm3ltLm2 : s84x_jm3 M < Lng M - 2 := lt_trans guard jm2lt1
  have jm3leLm2 : s84x_jm3 M ≤ Lng M - 2 := le_of_lt jm3ltLm2
  -- s84x_N と NT
  have hlenN : Lng (s84x_N M) = Lng M - s84x_jm3 M := by
    show Lng (seg M (s84x_jm3 M) (Lng M - 1)) = Lng M - s84x_jm3 M
    rw [length_seg]; omega
  have NT : TPS (s84x_N M) := by
    have hpos : 0 < Lng (s84x_N M) := by rw [hlenN]; omega
    intro hnil; rw [hnil] at hpos; simp [Lng] at hpos
  -- 前スライス恒等式 RN' = Red (seg M j₋₃ (Lng M-2))
  have hNpeq : Red (Pred (s84x_N M)) = Red (seg M (s84x_jm3 M) (Lng M - 2)) := by
    have h1 : Red (Pred (s84x_N M)) = Pred (Red (s84x_N M)) := Red_Pred (s84x_N M) NT
    have h2 : Pred (Red (s84x_N M)) = Red (seg M (s84x_jm3 M) (Lng M - 1 - 1)) :=
      Pred_Red_terminal_slice M (s84x_jm3 M) (Lng M - 1) jm3lt
    rw [h1, h2, show Lng M - 1 - 1 = Lng M - 2 from by omega]
  have NpT : TPS (seg M (s84x_jm3 M) (Lng M - 2)) := by
    have hpos : 0 < Lng (seg M (s84x_jm3 M) (Lng M - 2)) := by rw [length_seg]; omega
    intro hnil; rw [hnil] at hpos; simp [Lng] at hpos
  have leR3Lm2 : leR M 0 (s84x_jm3 M) (Lng M - 2) = true :=
    ancestor_tree_1 M (s84x_jm3 M) (Lng M - 2) (Lng M - 1) hMT leR3 jm3leLm2 (by omega)
  -- 前スライスの DTPS
  set RNp := Red (Pred (s84x_N M)) with hRNp
  have hDT : DTPS RNp := by
    rw [hNpeq]
    exact standard_slice_Red_strongmono M (s84x_jm3 M) (Lng M - 2) hST jm3ltLm2 (by omega) leR3Lm2
  obtain ⟨RNpRT, monoRNp, _descRNp⟩ := (DTPS_iff _).mp hDT
  have RNpT : TPS RNp := RTPS_TPS RNp RNpRT
  obtain ⟨condA', condB'⟩ := RTPS_condAB RNp RNpRT
  -- 長さ
  have LngRNpVal : Lng RNp = Lng M - 1 - s84x_jm3 M := by
    rw [hNpeq, Lng_Red_invariance _ NpT, length_seg]; omega
  -- 最終枝
  set lastp := (Br RNp).length - 1 with hlastp
  have hposBr : 0 < (Br RNp).length := List.length_pos_of_ne_nil Brne'
  have lastLtp : lastp < (Br RNp).length := by rw [hlastp]; omega
  -- run: d < TrMax RN'
  have run : s84x_jm2 M - s84x_jm3 M + 1 ≤ TrMax RNp := by
    rw [hNpeq]
    exact trmax_run_pre_sx M hMR hp hmono j1gt branch guard
  -- d < fnp, fnp ≤ Lng RN' - 1
  obtain ⟨_htj, htf⟩ := FirstNodes_TrMax_Joints RNp lastp RNpT monoRNp lastLtp
  have dltfn : s84x_jm2 M - s84x_jm3 M < (FirstNodes RNp).getD lastp 0 := by omega
  have fnLtp : (FirstNodes RNp).getD lastp 0 < Lng RNp := FN_lt_sx RNp lastp RNpT monoRNp lastLtp
  have fnleTp : (FirstNodes RNp).getD lastp 0 ≤ Lng RNp - 1 := by omega
  -- leR RN' 0 d (Lng RN' - 1)：切片転送
  have segIF : seg M (s84x_jm3 M) (Lng M - 2)
      = IncrFirstN (entry M 0 (s84x_jm3 M) - entry M 1 (s84x_jm3 M))
          (Red (seg M (s84x_jm3 M) (Lng M - 2))) :=
    (ancestor_slice_Red_IncrFirst M (s84x_jm3 M) (Lng M - 2) hMR jm3ltLm2 (by omega) leR3Lm2).2.2
  have le0jm2Lm1 : le0 M (s84x_jm2 M) (Lng M - 1) = true := (s84c1_jm2_basic M hp).2.2
  have leRjm2Lm1 : leR M 0 (s84x_jm2 M) (Lng M - 1) = true := by simpa [leR] using le0jm2Lm1
  have leRjm2Lm2 : leR M 0 (s84x_jm2 M) (Lng M - 2) = true :=
    ancestor_tree_1 M (s84x_jm2 M) (Lng M - 2) (Lng M - 1) hMT leRjm2Lm1 (by omega) (by omega)
  have leRdTp : leR RNp 0 (s84x_jm2 M - s84x_jm3 M) (Lng RNp - 1) = true := by
    have ha : (s84x_jm2 M - s84x_jm3 M) < Lng (seg M (s84x_jm3 M) (Lng M - 2)) := by
      rw [length_seg]; omega
    have hb : (Lng RNp - 1) < Lng (seg M (s84x_jm3 M) (Lng M - 2)) := by
      rw [length_seg]; omega
    have hseg := leR0_seg_adm M (s84x_jm3 M) (Lng M - 2) (s84x_jm2 M - s84x_jm3 M)
      (Lng RNp - 1) jm3leLm2 (by omega) ha hb
    rw [show s84x_jm3 M + (s84x_jm2 M - s84x_jm3 M) = s84x_jm2 M from by omega,
       show s84x_jm3 M + (Lng RNp - 1) = Lng M - 2 from by omega] at hseg
    rw [segIF, leR_IncrFirstN] at hseg
    rw [← hNpeq] at hseg
    rw [hseg]; exact leRjm2Lm2
  -- 祖先木: d ≤ jlp
  have ent : entry RNp 0 (s84x_jm2 M - s84x_jm3 M)
      < entry RNp 0 ((FirstNodes RNp).getD lastp 0) :=
    ancestor_basic_1 RNp (s84x_jm2 M - s84x_jm3 M) ((FirstNodes RNp).getD lastp 0)
      (Lng RNp - 1) RNpT dltfn fnleTp leRdTp
  have nxjlp : nextR RNp 0 ((Joints RNp).getD lastp 0) ((FirstNodes RNp).getD lastp 0) = true :=
    Joints_nextR_FirstNodes RNp lastp RNpT monoRNp lastLtp
  have dlejlp : (s84x_jm2 M - s84x_jm3 M) ≤ (Joints RNp).getD lastp 0 :=
    nextR0_largest_below RNp ((Joints RNp).getD lastp 0) (s84x_jm2 M - s84x_jm3 M)
      ((FirstNodes RNp).getD lastp 0) nxjlp dltfn ent
  -- VEj1p RN' = fnp を露出
  have hVE : VEj1p RNp = (FirstNodes RNp).getD lastp 0 := rfl
  rw [hVE]
  by_cases hdj : (s84x_jm2 M - s84x_jm3 M) = (Joints RNp).getD lastp 0
  · -- 等号枝: 対角性（dgx_regSP_diag_of_lt の挟み撃ち）
    right
    refine ⟨hdj, ?_⟩
    -- strictlt を残差から取り出す（strictlt_eq は set で RN' 形に畳まれている）
    have strictlt : entry RNp 1 (s84x_jm2 M - s84x_jm3 M)
        < entry RNp 1 ((FirstNodes RNp).getD lastp 0) := strictlt_eq hdj
    -- RedCondA 行0 で fnp の親 = jlp = d
    have parfnp : parent RNp 0 ((FirstNodes RNp).getD lastp 0) = (Joints RNp).getD lastp 0 :=
      (Joints_getD RNp lastp lastLtp).symm
    have pfd : parent RNp 0 ((FirstNodes RNp).getD lastp 0) = s84x_jm2 M - s84x_jm3 M := by
      rw [parfnp, ← hdj]
    have hpfnp0 : hasParent RNp 0 ((FirstNodes RNp).getD lastp 0) = true :=
      FN_hasParent_sx RNp lastp RNpT monoRNp lastLtp
    have e0fn : entry RNp 0 (parent RNp 0 ((FirstNodes RNp).getD lastp 0)) + 1
        = entry RNp 0 ((FirstNodes RNp).getD lastp 0) :=
      RedCondA_apply RNp condA' 0 ((FirstNodes RNp).getD lastp 0) (by norm_num) fnLtp hpfnp0
    have e0fn' : entry RNp 0 (s84x_jm2 M - s84x_jm3 M) + 1
        = entry RNp 0 ((FirstNodes RNp).getD lastp 0) := by rw [← pfd]; exact e0fn
    -- 幹対角 at d
    have dTr : (s84x_jm2 M - s84x_jm3 M) ≤ TrMax RNp := by omega
    have e00 : entry RNp 0 0 = entry RNp 1 0 := RedCondB_head_eq RNp RNpT condB'
    have offs := trunk_entries_offset RNp RNpT condA' (s84x_jm2 M - s84x_jm3 M) dTr
    have ediag_d : entry RNp 0 (s84x_jm2 M - s84x_jm3 M)
        = entry RNp 1 (s84x_jm2 M - s84x_jm3 M) := by rw [offs.1, offs.2, e00]
    have e0fn_v : entry RNp 0 ((FirstNodes RNp).getD lastp 0)
        = entry RNp 1 (s84x_jm2 M - s84x_jm3 M) + 1 := by rw [← e0fn', ediag_d]
    have upper : entry RNp 1 ((FirstNodes RNp).getD lastp 0)
        ≤ entry RNp 0 ((FirstNodes RNp).getD lastp 0) :=
      reduced_coeff RNp RNpRT ((FirstNodes RNp).getD lastp 0) fnLtp
    have lower : entry RNp 1 (s84x_jm2 M - s84x_jm3 M) + 1
        ≤ entry RNp 1 ((FirstNodes RNp).getD lastp 0) := strictlt
    omega
  · left
    omega

/-! ## 3. named 残差 `RegspStrictlt_sx` と reduction -/

/-- Isabelle `slx37_strictlt_eqd` (layerB/pss_wip.thy:97052) を Lean 語彙で述べた
尖った残差。`d = jlp`（最終枝の joint）の下で、前スライス `RN' = Red (Pred (s84x_N M))`
の行1で `RN'_{1,d} < RN'_{1,fnp}`（`fnp = FirstNodes RN' ! last`）。

Isabelle の証明は `RN' = butlast (Red (s84x_N M))` の last-branch を全スライス
`RN = Red (s84x_N M)` の index `lastp` へ `wid_*_Pred` で移し、`mcx_MCOND_RN`
（= `Regs_MCOND_holds`）の対角性 ＋ `descending (Br RN)` の tie-break で組む。 -/
def RegspStrictlt_sx : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    s84x_jm3 M < s84x_jm2 M →
    Br (Red (Pred (s84x_N M))) ≠ [] →
    s84x_jm2 M - s84x_jm3 M
        = (Joints (Red (Pred (s84x_N M)))).getD
            ((Br (Red (Pred (s84x_N M)))).length - 1) 0 →
    entry (Red (Pred (s84x_N M))) 1 (s84x_jm2 M - s84x_jm3 M)
      < entry (Red (Pred (s84x_N M))) 1
          ((FirstNodes (Red (Pred (s84x_N M)))).getD
            ((Br (Red (Pred (s84x_N M)))).length - 1) 0)

/-- `RegspStrictlt_sx` から `Regsp_disj_sharp`（«8».«8.4-exch84-regsp»）を出す。 -/
theorem Regsp_disj_sharp_of_strictlt (h : RegspStrictlt_sx) : Regsp_disj_sharp := by
  intro M hST hmono hp hj1 hcond guard Brne'
  exact regsp_disj_of_strictlt_sx M hST hmono hp hj1 hcond guard Brne'
    (h M hST hmono hp hj1 hcond guard Brne')

/-- 共通鍵 `Regsp_slx37_regSP`（= Isabelle `slx37_regSP_uncond`）を、単一の尖った
残差 `RegspStrictlt_sx`（= `slx37_strictlt_eqd`）へ無条件還元する。
membership 骨格と `Regs_jm3Marked` はビルド済みの `Regsp_of_disj_sharp`
（«8».«8.4-exch84-regsp»）と `Regs_jm3Marked_holds`（«8».«8.4-exch84-mcond»）が担う。 -/
theorem Regsp_slx37_regSP_of_strictlt (h : RegspStrictlt_sx) : Regsp_slx37_regSP :=
  Regsp_of_disj_sharp Regs_jm3Marked_holds (Regsp_disj_sharp_of_strictlt h)

#print axioms Regsp_disj_sharp_of_strictlt
#print axioms Regsp_slx37_regSP_of_strictlt

end PSS
