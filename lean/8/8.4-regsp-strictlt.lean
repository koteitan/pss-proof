import «8».«8.4-regsp-slx37»
import «8».«8.4-parent-max»

/-!
# §8.4 尖った last-branch tie-break `RegspStrictlt_sx` の discharge（= Isabelle `slx37_strictlt_eqd`）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
- 対象: ビルド済みの named 残差 `RegspStrictlt_sx`（«8».«8.4-regsp-slx37»:372、
  Isabelle `slx37_strictlt_eqd` layerB/pss_wip.thy:97052 の Lean 語彙形）。
  これを閉じると `Regsp_slx37_regSP`（= Isabelle `slx37_regSP_uncond`）が無条件化し、
  `slicepkg` の `REGSP` 脚と `NestScbD4aReducedValue` が解錠される。

## Isabelle `slx37_strictlt_eqd` の証明（本ファイルが移植するもの）

全スライス `RN = Red (s84x_N M)` の**最終枝**（index `last = Lng (Br RN) - 1`）と、
前スライス `RN' = Red (Pred (s84x_N M)) = Pred RN = butlast RN` の最終枝
（index `lastp = Lng (Br RN') - 1`）を突き合わせる:

1. `RN' = Pred RN` なので Pred 枝コア（`Br/FirstNodes/Joints_Pred_core`,
   «6».«6.5-Red-Pred-commute»）で `fnp = FirstNodes RN' ! lastp = FirstNodes RN ! lastp = fJ`,
   `jlp = Joints RN' ! lastp = Joints RN ! lastp` へ持ち上げ、guard `d = jlp` を
   `d = Joints RN ! lastp` へ。
2. `Regs_MCOND_holds`（«8».«8.4-exch84-mcond»、= `mcx_MCOND_RN`）が最終枝で
   `d < jl ∨ (d = jl ∧ RN_{0,fn} = RN_{1,fn})`。`descending (Br RN)` の tie-break
   （`lastp ≤ last`、`standard_slice_Red_strongmono`/`DTPS`）＋ RedCondA 行0 ＋
   幹対角（`trunk_entries_offset`）で `d = jl` を強制、`fn` の対角性を得る。
3. `RedCondB` 頭 ＋ trunk offset で `RN_{0,d} = RN_{1,d}`、組み立てて
   `RN_{1,fn} = RN_{1,d} + 1`、tie-break `RN_{1,fn} ≤ RN_{1,fJ}` から
   `RN_{1,d} < RN_{1,fJ}`（= strictlt）。`butlast`（`entry_Pred`）で `RN'` 座標へ輸送。

## 本ファイルの成果物（house pattern）

- `RegspStrictlt_holds : RegspStrictlt_sx` — 上記の完全移植。
- `Regsp_slx37_regSP_holds : Regsp_slx37_regSP` — `Regsp_slx37_regSP_of_strictlt`
  （«8».«8.4-regsp-slx37»）へ接続、無条件化。

- 依存（すべてビルド済み・committed）: «8».«8.4-regsp-slx37»（`RegspStrictlt_sx`/
  `Regsp_slx37_regSP_of_strictlt`）、«8».«8.4-parent-max»（`regs_jm2_lt_transJ0_holds`）、
  推移的に «8».«8.4-exch84-mcond»（`Regs_MCOND_holds`/`Regs_jm3Marked_holds`）,
  «6».«6.5-Red-Pred-commute»（`Br/FirstNodes/Joints_Pred_core`, `Red_Pred`,
  `entry_Pred`, `TrMax_Pred_nontrunk`, `monoT_Pred_long`, `RTPS_Pred`）,
  «7».«7.4-Mark-Trans-repr»（`Pred_Red_terminal_slice`）,
  «8».«8.2-standard-slice-Red-strongmono»（`DTPS_iff`/`descendingB_iff`/`cdomB_iff`）。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
- Private helper suffix: `_sl`。
-/

namespace PSS

/-! ## 1. private 補助（suffix `_sl`） -/

/-- `le0Aux` の反射性（`Regs_MCOND_holds` の private `le0Aux_refl_mc` の再掲）。 -/
private theorem le0Aux_refl_sl (M : PS) (fuel a : ℕ) : le0Aux M fuel a a = true := by
  cases fuel <;> simp [le0Aux]

/-- Isabelle `a1_FN_hasParent` (pss_mechanized.thy:33161)。枝成分の左端は行0の親を持つ。
（«8».«8.4-regsp-slx37» の private `FN_hasParent_sx` の再掲。） -/
private theorem FN_hasParent_sl (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
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

/-- Isabelle `a1_FN_lt` (pss_mechanized.thy:33186)。枝成分の左端は `Lng` 未満。
（«8».«8.4-regsp-slx37» の private `FN_lt_sx` の再掲。） -/
private theorem FN_lt_sl (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) :
    (FirstNodes M).getD J 0 < Lng M := by
  have h := Joints_nextR_FirstNodes M J hM hmono hJ
  have hn : nextrel0 M ((Joints M).getD J 0) ((FirstNodes M).getD J 0) = true := by
    simpa [nextR] using h
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hn
  exact hn.1.1.1.2

/-- 全トランク（`TrMax M = Lng M - 1`）は `Pred` で保存され、`Br (Pred M) = []`。
`Br (Pred RN) ≠ []`（前スライスに枝）から全スライス `Br RN ≠ []` を出す対偶に使う。 -/
private theorem Br_Pred_trunk_sl (M : PS) (hM : TPS M) (hlen : 1 < Lng M)
    (htr : TrMax M = Lng M - 1) : Br (Pred M) = [] := by
  have hPredT : TPS (Pred M) := Pred_TPS M hM
  have hPL : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hpred : Pred M = M.take (Lng M - 1) := Pred_eq_take M hlen
  have hbound := TrMax_bound (Pred M) hPredT
  have hlower : Lng (Pred M) - 1 ≤ TrMax (Pred M) := by
    apply le_TrMax_intro_wd (Pred M) (Lng (Pred M) - 1) hPredT
    intro j hj
    rw [hPL] at hj
    have hjtr : j < TrMax M := by rw [htr]; omega
    have hs := TrMax_trunk_step M j hM hjtr
    rw [hpred, nextR_take_adm M (Lng M - 1) 1 j (j + 1) (by omega) (by omega) (by omega)]
    exact hs
  have heq : TrMax (Pred M) = Lng (Pred M) - 1 := by omega
  simp [Br, heq]

/-- Isabelle `crx_trmax_run` (layerB/pss_wip.thy:89879)。非許容 run `(j₋₃, j₋₂]` の
各点で行1後続辺が立つので、簡約スライスへ転送すると `TrMax` の下界が出る。
（«8».«8.4-exch84-mcond» の private `crx_trmax_run_mc` の再掲。） -/
private theorem crx_trmax_run_sl (M : PS) (hMR : RTPS M)
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
  exact le_TrMax_intro_wd (Red (s84x_N M)) ((s84x_jm2 M - s84x_jm3 M) + 1) RNT stepRN

/-! ## 2. named 残差 `RegspStrictlt_sx` の discharge -/

/-- Isabelle `slx37_strictlt_eqd` (layerB/pss_wip.thy:97052) の完全移植。 -/
theorem RegspStrictlt_holds : RegspStrictlt_sx := by
  intro M hST hmono hp j1gt branch guard Brne' eqd
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have jm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have jm3le : s84x_jm3 M ≤ s84x_jm2 M := Adm_le M (s84x_jm2 M)
  have jm3lt : s84x_jm3 M < Lng M - 1 := lt_of_le_of_lt jm3le jm2lt
  have leR3 : leR M 0 (s84x_jm3 M) (Lng M - 1) = true :=
    (Regs_jm3Marked_holds M hMR hMT hp).1.2.2
  -- j₋₂ < transJ0 < Lng M - 1 ⟹ jm2 < Lng M - 2
  have jm2ltj0 : s84x_jm2 M < transJ0 M :=
    regs_jm2_lt_transJ0_holds M hST hmono hp j1gt branch
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hMT hmono (Lng M - 1) (by omega) (by omega)
  have j0lt : transJ0 M < Lng M - 1 := by
    show lastParent M < Lng M - 1
    show parent M 0 (lastIdx M) < Lng M - 1
    exact parent_lt_of_hasParent M 0 (Lng M - 1) hp0
  -- RN facts（全スライス）
  have hlenN : Lng (s84x_N M) = Lng M - s84x_jm3 M := by
    show Lng (seg M (s84x_jm3 M) (Lng M - 1)) = Lng M - s84x_jm3 M
    rw [length_seg]; omega
  have NT : TPS (s84x_N M) := by
    have hpos : 0 < Lng (s84x_N M) := by rw [hlenN]; omega
    intro hnil; rw [hnil] at hpos; simp [Lng] at hpos
  have ND : DTPS (Red (s84x_N M)) :=
    standard_slice_Red_strongmono M (s84x_jm3 M) (Lng M - 1) hST jm3lt (le_refl _) leR3
  have RNRT : RTPS (Red (s84x_N M)) := ((DTPS_iff _).mp ND).1
  have monoRN : monoT (Red (s84x_N M)) = true := ((DTPS_iff _).mp ND).2.1
  have descRN : descendingB (Br (Red (s84x_N M))) = true := ((DTPS_iff _).mp ND).2.2
  have RNT : TPS (Red (s84x_N M)) := RTPS_TPS _ RNRT
  obtain ⟨condA_RN, condB_RN⟩ := RTPS_condAB (Red (s84x_N M)) RNRT
  have LngRN : Lng (Red (s84x_N M)) = Lng (s84x_N M) := Lng_Red_invariance (s84x_N M) NT
  have hLngRNval : Lng (Red (s84x_N M)) = Lng M - s84x_jm3 M := LngRN.trans hlenN
  have PredRN0 : Pred (Red (s84x_N M)) = Red (Pred (s84x_N M)) := (Red_Pred (s84x_N M) NT).symm
  have run0 : s84x_jm2 M - s84x_jm3 M + 1 ≤ TrMax (Red (s84x_N M)) :=
    crx_trmax_run_sl M hMR hp guard
  have mcond0 := Regs_MCOND_holds M hST hmono hp j1gt branch guard
  -- 短縮
  set RN := Red (s84x_N M) with hRN_def
  set RNp := Red (Pred (s84x_N M)) with hRNp_def
  have PredRN : Pred RN = RNp := PredRN0
  have LngRNgt1 : 1 < Lng RN := by rw [hLngRNval]; omega
  -- Br RN ≠ [] （前スライスに枝がある対偶）
  have Brne : Br RN ≠ [] := by
    intro hnil
    have htr : TrMax RN = Lng RN - 1 := by
      by_contra hne0
      rw [Br, if_neg hne0] at hnil
      exact P_nonempty _ hnil
    have hBrP : Br (Pred RN) = [] := Br_Pred_trunk_sl RN RNT LngRNgt1 htr
    rw [PredRN] at hBrP
    exact Brne' hBrP
  have hne : TrMax RN ≠ Lng RN - 1 := by
    intro heq; exact Brne (by simp [Br, heq])
  have lastLt : (Br RN).length - 1 < (Br RN).length :=
    Nat.sub_lt (List.length_pos_of_ne_nil Brne) one_pos
  have lastLtp : (Br RNp).length - 1 < (Br RNp).length :=
    Nat.sub_lt (List.length_pos_of_ne_nil Brne') one_pos
  -- Pred 枝コア at lastp
  have hJp : (Br RNp).length - 1 < (Br (Pred RN)).length := by rw [PredRN]; exact lastLtp
  have fnp_core : (FirstNodes (Pred RN)).getD ((Br RNp).length - 1) 0
      = (FirstNodes RN).getD ((Br RNp).length - 1) 0 :=
    FirstNodes_Pred_core RN RNT LngRNgt1 hne ((Br RNp).length - 1) hJp
  have jlp_core : (Joints (Pred RN)).getD ((Br RNp).length - 1) 0
      = (Joints RN).getD ((Br RNp).length - 1) 0 :=
    Joints_Pred_core RN RNT monoRN LngRNgt1 hne ((Br RNp).length - 1) hJp
  -- lastp < Lng (Br RN)
  have hlen_le : (Br (Pred RN)).length ≤ (Br RN).length := by
    rw [Br_Pred_core_nontrunk RN RNT LngRNgt1 hne]
    by_cases hd : Lng ((Br RN).getLastD []) ≤ 1
    · rw [if_pos hd]
      simp only [List.append_nil, List.length_dropLast]
      omega
    · rw [if_neg hd]
      simp only [List.length_append, List.length_dropLast, List.length_singleton]
      have := List.length_pos_of_ne_nil Brne
      omega
  have lastp_ltBrRN : (Br RNp).length - 1 < (Br RN).length := lt_of_lt_of_le hJp hlen_le
  -- guard を RN 座標へ
  have parfJ : parent RN 0 ((FirstNodes RN).getD ((Br RNp).length - 1) 0)
      = (Joints RN).getD ((Br RNp).length - 1) 0 :=
    (Joints_getD RN ((Br RNp).length - 1) lastp_ltBrRN).symm
  have jlp_eq : (Joints RNp).getD ((Br RNp).length - 1) 0
      = (Joints RN).getD ((Br RNp).length - 1) 0 := by
    have h := jlp_core; rw [PredRN] at h; exact h
  have eqd_RN : s84x_jm2 M - s84x_jm3 M = (Joints RN).getD ((Br RNp).length - 1) 0 :=
    eqd.trans jlp_eq
  have pfJd : parent RN 0 ((FirstNodes RN).getD ((Br RNp).length - 1) 0)
      = s84x_jm2 M - s84x_jm3 M := by rw [parfJ, ← eqd_RN]
  have hpfJ0 : hasParent RN 0 ((FirstNodes RN).getD ((Br RNp).length - 1) 0) = true :=
    FN_hasParent_sl RN ((Br RNp).length - 1) RNT monoRN lastp_ltBrRN
  have fJLt : (FirstNodes RN).getD ((Br RNp).length - 1) 0 < Lng RN :=
    FN_lt_sl RN ((Br RNp).length - 1) RNT monoRN lastp_ltBrRN
  have e0fJ : entry RN 0 (s84x_jm2 M - s84x_jm3 M) + 1
      = entry RN 0 ((FirstNodes RN).getD ((Br RNp).length - 1) 0) := by
    have h := RedCondA_apply RN condA_RN 0 ((FirstNodes RN).getD ((Br RNp).length - 1) 0)
      (by norm_num) fJLt hpfJ0
    rw [pfJd] at h; exact h
  -- 最終枝 fn/jl
  have parfn : parent RN 0 ((FirstNodes RN).getD ((Br RN).length - 1) 0)
      = (Joints RN).getD ((Br RN).length - 1) 0 :=
    (Joints_getD RN ((Br RN).length - 1) lastLt).symm
  have hpfn0 : hasParent RN 0 ((FirstNodes RN).getD ((Br RN).length - 1) 0) = true :=
    FN_hasParent_sl RN ((Br RN).length - 1) RNT monoRN lastLt
  have fnLt : (FirstNodes RN).getD ((Br RN).length - 1) 0 < Lng RN :=
    FN_lt_sl RN ((Br RN).length - 1) RNT monoRN lastLt
  have e0fn : entry RN 0 ((Joints RN).getD ((Br RN).length - 1) 0) + 1
      = entry RN 0 ((FirstNodes RN).getD ((Br RN).length - 1) 0) := by
    have h := RedCondA_apply RN condA_RN 0 ((FirstNodes RN).getD ((Br RN).length - 1) 0)
      (by norm_num) fnLt hpfn0
    rw [parfn] at h; exact h
  -- MCOND
  have mcond : s84x_jm2 M - s84x_jm3 M < (Joints RN).getD ((Br RN).length - 1) 0
      ∨ (s84x_jm2 M - s84x_jm3 M = (Joints RN).getD ((Br RN).length - 1) 0
         ∧ entry RN 0 ((FirstNodes RN).getD ((Br RN).length - 1) 0)
           = entry RN 1 ((FirstNodes RN).getD ((Br RN).length - 1) 0)) := by
    have h := mcond0
    rw [show VEj1p RN = (FirstNodes RN).getD ((Br RN).length - 1) 0 from rfl] at h
    exact h
  have dlejl : s84x_jm2 M - s84x_jm3 M ≤ (Joints RN).getD ((Br RN).length - 1) 0 := by
    rcases mcond with h | ⟨h, _⟩ <;> omega
  -- trunk bounds
  have dltTr : s84x_jm2 M - s84x_jm3 M < TrMax RN := by omega
  have dTr : s84x_jm2 M - s84x_jm3 M ≤ TrMax RN := le_of_lt dltTr
  have jl_le_Tr : (Joints RN).getD ((Br RN).length - 1) 0 ≤ TrMax RN :=
    (FirstNodes_TrMax_Joints RN ((Br RN).length - 1) RNT monoRN lastLt).1
  have offd := trunk_entries_offset RN RNT condA_RN (s84x_jm2 M - s84x_jm3 M) dTr
  have offjl := trunk_entries_offset RN RNT condA_RN
    ((Joints RN).getD ((Br RN).length - 1) 0) jl_le_Tr
  -- descending at (lastp, last)
  have lastp_le_last : (Br RNp).length - 1 ≤ (Br RN).length - 1 := by omega
  have hcd := (descendingB_iff (Br RN)).mp descRN ((Br RNp).length - 1) ((Br RN).length - 1)
    lastp_le_last lastLt
  rw [cdomB_iff] at hcd
  have bh0_lastp : entry RN 0 ((FirstNodes RN).getD ((Br RNp).length - 1) 0)
      = entry ((Br RN).getD ((Br RNp).length - 1) []) 0 0 :=
    entry_FirstNodes_eq_component_mr RN ((Br RNp).length - 1) 0 RNT lastp_ltBrRN
  have bh1_lastp : entry RN 1 ((FirstNodes RN).getD ((Br RNp).length - 1) 0)
      = entry ((Br RN).getD ((Br RNp).length - 1) []) 1 0 :=
    entry_FirstNodes_eq_component_mr RN ((Br RNp).length - 1) 1 RNT lastp_ltBrRN
  have bh0_last : entry RN 0 ((FirstNodes RN).getD ((Br RN).length - 1) 0)
      = entry ((Br RN).getD ((Br RN).length - 1) []) 0 0 :=
    entry_FirstNodes_eq_component_mr RN ((Br RN).length - 1) 0 RNT lastLt
  have bh1_last : entry RN 1 ((FirstNodes RN).getD ((Br RN).length - 1) 0)
      = entry ((Br RN).getD ((Br RN).length - 1) []) 1 0 :=
    entry_FirstNodes_eq_component_mr RN ((Br RN).length - 1) 1 RNT lastLt
  have desc0 : entry RN 0 ((FirstNodes RN).getD ((Br RN).length - 1) 0)
      ≤ entry RN 0 ((FirstNodes RN).getD ((Br RNp).length - 1) 0) := by
    rw [bh0_last, bh0_lastp]; exact hcd.1
  -- d = jl
  have deqjl : s84x_jm2 M - s84x_jm3 M = (Joints RN).getD ((Br RN).length - 1) 0 := by
    have a1 : entry RN 0 ((Joints RN).getD ((Br RN).length - 1) 0) + 1
        ≤ entry RN 0 (s84x_jm2 M - s84x_jm3 M) + 1 := by rw [e0fn, e0fJ]; exact desc0
    have o1 := offd.1
    have o2 := offjl.1
    omega
  -- 対角性 at fn
  have diagfn : entry RN 0 ((FirstNodes RN).getD ((Br RN).length - 1) 0)
      = entry RN 1 ((FirstNodes RN).getD ((Br RN).length - 1) 0) := by
    rcases mcond with h | ⟨_, hdiag⟩
    · omega
    · exact hdiag
  -- 幹対角 at d
  have e00 : entry RN 0 0 = entry RN 1 0 := RedCondB_head_eq RN RNT condB_RN
  have ediag_d : entry RN 0 (s84x_jm2 M - s84x_jm3 M)
      = entry RN 1 (s84x_jm2 M - s84x_jm3 M) := by rw [offd.1, offd.2, e00]
  -- tie-break: row-0 heads equal ⟹ RN_{1,fn} ≤ RN_{1,fJ}
  have fJfn0 : entry RN 0 ((FirstNodes RN).getD ((Br RNp).length - 1) 0)
      = entry RN 0 ((FirstNodes RN).getD ((Br RN).length - 1) 0) := by
    rw [← e0fJ, ← e0fn, deqjl]
  have head0eq : entry ((Br RN).getD ((Br RNp).length - 1) []) 0 0
      = entry ((Br RN).getD ((Br RN).length - 1) []) 0 0 := by
    rw [← bh0_lastp, ← bh0_last]; exact fJfn0
  have tie1 : entry RN 1 ((FirstNodes RN).getD ((Br RN).length - 1) 0)
      ≤ entry RN 1 ((FirstNodes RN).getD ((Br RNp).length - 1) 0) := by
    have h := hcd.2 head0eq
    rw [← bh1_last, ← bh1_lastp] at h
    exact h
  -- RN_{1,fn} = RN_{1,d} + 1
  have e1fn : entry RN 1 ((FirstNodes RN).getD ((Br RN).length - 1) 0)
      = entry RN 1 (s84x_jm2 M - s84x_jm3 M) + 1 := by
    rw [← diagfn, ← e0fn, ← deqjl, ediag_d]
  -- strictlt in RN
  have strictRN : entry RN 1 (s84x_jm2 M - s84x_jm3 M)
      < entry RN 1 ((FirstNodes RN).getD ((Br RNp).length - 1) 0) := by omega
  -- 前スライス RNp = Pred RN へ輸送
  have RNpRT : RTPS RNp := by rw [← PredRN]; exact RTPS_Pred RN RNRT
  have RNpT : TPS RNp := RTPS_TPS RNp RNpRT
  have LngRNp : Lng RNp = Lng RN - 1 := by rw [← PredRN]; exact length_Pred RN LngRNgt1
  have LngRNp2 : 2 ≤ Lng RNp := by
    by_contra hlt
    have hpos : 0 < Lng RNp := List.length_pos_of_ne_nil RNpT
    have hb := TrMax_bound RNp RNpT
    have htrp : TrMax RNp = Lng RNp - 1 := by omega
    exact Brne' (by simp [Br, htrp])
  have RNlong : 2 < Lng RN := by omega
  have monoRNp : monoT RNp = true := by rw [← PredRN]; exact monoT_Pred_long RN RNT monoRN RNlong
  have fnpLtp : (FirstNodes RNp).getD ((Br RNp).length - 1) 0 < Lng RNp :=
    FN_lt_sl RNp ((Br RNp).length - 1) RNpT monoRNp lastLtp
  have fnp_eq : (FirstNodes RNp).getD ((Br RNp).length - 1) 0
      = (FirstNodes RN).getD ((Br RNp).length - 1) 0 := by
    have h := fnp_core; rw [PredRN] at h; exact h
  have fJltLm1 : (FirstNodes RN).getD ((Br RNp).length - 1) 0 < Lng RN - 1 := by
    have h := fnpLtp; rw [fnp_eq, LngRNp] at h; exact h
  have dltLm1 : s84x_jm2 M - s84x_jm3 M < Lng RN - 1 := by
    have hb := TrMax_bound RN RNT; omega
  have e_d : entry RNp 1 (s84x_jm2 M - s84x_jm3 M) = entry RN 1 (s84x_jm2 M - s84x_jm3 M) := by
    have h := entry_Pred RN 1 (s84x_jm2 M - s84x_jm3 M) dltLm1; rw [PredRN] at h; exact h
  have e_fJ : entry RNp 1 ((FirstNodes RN).getD ((Br RNp).length - 1) 0)
      = entry RN 1 ((FirstNodes RN).getD ((Br RNp).length - 1) 0) := by
    have h := entry_Pred RN 1 ((FirstNodes RN).getD ((Br RNp).length - 1) 0) fJltLm1
    rw [PredRN] at h; exact h
  rw [fnp_eq, e_d, e_fJ]
  exact strictRN

/-! ## 3. 共通鍵 `Regsp_slx37_regSP` の無条件化 -/

/-- 単一の尖った残差 `RegspStrictlt_sx` を discharge したので、`Regsp_slx37_regSP`
（= Isabelle `slx37_regSP_uncond`）が無条件で成立する。 -/
theorem Regsp_slx37_regSP_holds : Regsp_slx37_regSP :=
  Regsp_slx37_regSP_of_strictlt RegspStrictlt_holds

#print axioms RegspStrictlt_holds
#print axioms Regsp_slx37_regSP_holds

end PSS
