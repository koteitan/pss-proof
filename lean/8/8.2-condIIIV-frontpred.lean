import «8».«8.2-condIIIV-peel-values»

/-!
# §8.2 条件(II)/(IV) VE34 run-peel — **BASE-run-step 残差 2 本の討伐**
  (`TerminalSliceReadyD_pv` ＝終切片 ready ＋ `FrontPredBaseTransportD_pv` ＝前置切片 `Pred` 転送)

- 背景: `8.2-condIIIV-peel-values` は descending 体制 `VE34Reg4D` 上の BASE-run-step
  組立 `BaseRunStep_of_geomD_pv` を、終切片転送 `TermPredBaseTransportD_pv`（`jeqBaseD_pv`
  で無条件討伐済）を内部で消し、残差 `{PIN_bd, TSPIN_bd, TerminalSliceReadyD_pv,
  FrontPredBaseTransportD_pv}` の 4 本にまで削減した。本ファイルはこの 4 本のうち
  §7.4/§6.4 幾何を要する 2 本 `{TerminalSliceReadyD_pv, FrontPredBaseTransportD_pv}` を
  無条件討伐する。

- **(1) `TerminalSliceReadyD_pv`**（Isabelle `bux_terminal_slice_ready` 99317）: run-step
  BASE ホスト（descending 体制）で終切片 `Mp = seg N (Joints N ! (Lng(Br N)-1)) (Lng N-1)` が
  `keystone` を適用できる状態（`RTPS ∧ monoT ∧ Br≠[] ∧ 1 < Lng Mp - 1`）にあること。
  Isabelle は `vg8x_terminal_slice_DT`（＝`m_8_2_strongmono_slice`）で `Mp ∈ DT_PS` を得て
  `DT_PS = RT_PS ∧ monoT ∧ descending(Br)` から `RTPS`/`monoT` を、`TrMax_seg_ancestor` ＋
  `Lng_seg` ＋ `baseU_Br_empty_TrMax` で `Br Mp ≠ []` と `1 < Lng Mp - 1` を示す。
  Lean 版は公開の `strongmono_slice`（`8.2-strongmono-slice`）で `DTPS Mp` を得て同型に組む
  （`TrMax_seg_ancestor` は本ファイルで `_fp` として再導出）。

- **(2) `FrontPredBaseTransportD_pv`**（Isabelle `bfx_front_Pred_base` 104988）: run-step BASE
  ホストで前置切片 `Pred N` は `N` の前置切片に一致する（`Pred` は末尾列を落とすだけ）。
  Isabelle は `m_7_4_seg_Pred_eq`（＝`seg_Pred_eq`、前置は `Pred` 不変）＋ `bfx_FN_Pred_LS_base`
  （＝`FN_Pred_LS_base_pv`、`FirstNodes` 転送、公開済）＋ `bfx_LastStep_Pred_base`
  （`LastStep (Pred N) = LastStep N`、find? 最小性転送）で組む。本ファイルは
  `bfx_LastStep_Pred_base` を Lean の `List.find?` 版に移植する（`lastStepPred_fp`）。
  その要は Isabelle `bfx_finset_mem_lt_base`（枝頭述語が枝剥がし下で J < Lng(Br(Pred N)) で
  一致）で、これは枝頭一致 `Br_Pred_col0_agree_fp`（＝`wid_Br_Pred_col0_agree`）＋ 目標枝頭
  一致 `tgtPred_fp`（run 前枝頭 = 最終枝頭、`bfx_run_prev(1)`）から従う。else-case 判定は
  最終枝ガード `gtN_fp`/`gtP_fp`（`bfx_gtN`/`bfx_gtP_base`）で分岐する。

- 訂正: なし（Isabelle 済補題の逐語移植 ＋ 既公開 `_pv` 群の再利用）。

- 依存 module: `8.2-condIIIV-peel-values`（`TerminalSliceReadyD_pv`/`FrontPredBaseTransportD_pv`/
  `FN_Pred_LS_base_pv`/`BrLen_Pred_base_pv`/`VE34Reg4D`/`VE34Reg4`/`VEj1p`/`LastStep`/`Br`/
  `Joints`/`FirstNodes`/`seg`/`Pred` を推移的に）。`strongmono_slice`/`DTPS`/`DTPS_iff`
  （`8.2-strongmono-slice`/`8.2-standard-slice-Red-strongmono`、推移的に到達可能）、
  `TrMax_bound`/`length_seg`/`baseU_Br_empty_TrMax`/`Br_Pred_core_nontrunk`/`FirstNodes_Pred_core`/
  `entry_FirstNodes_eq_component_mr`/`seg_Pred_eq`/`m1_bounds`/`LastStep_lt_Lng_Br`/
  `le_TrMax_intro_wd`/`nextR1_seg_adm`/`TrMax_trunk_step`/`TrMax_stop_uncond`/
  `Joints_nextR_FirstNodes`/`FirstNodes_TrMax_Joints`/`descendingB`/`length_Pred`。

- 状態: ⚠️ 部分（sorry 0、rc=0、公理 `[propext, Classical.choice, Quot.sound]` のみ）。
  (1) `terminalSliceReadyD_holds`、(2) `frontPredBaseTransportD_holds` を放出。
  private suffix: `_fp`。
-/

namespace PSS

/-! ## private 補助（幹根切片の幹整列）— Isabelle `TrMax_seg_ancestor` -/

/-- 幹根切片の幹の整列（Isabelle `TrMax_seg_ancestor`、`8.2-strongmono-slice` の
`TrMax_seg_ancestor_sms` が private ゆえ再掲）: `j₀' ≤ TrMax M < j₁' < Lng M` なら
`TrMax (seg M j₀' j₁') = TrMax M - j₀'`。 -/
private theorem TrMax_seg_ancestor_fp (M : PS) (j₀' j₁' : ℕ) (hM : TPS M)
    (hj₀ : j₀' ≤ TrMax M) (hTr : TrMax M < j₁') (hj₁ : j₁' < Lng M) :
    TrMax (seg M j₀' j₁') = TrMax M - j₀' := by
  have hlt : j₀' < j₁' := by omega
  have hLS : Lng (seg M j₀' j₁') = j₁' + 1 - j₀' := by simp [seg]
  have hST : TPS (seg M j₀' j₁') := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (seg M j₀' j₁')
    omega
  have hge : TrMax M - j₀' ≤ TrMax (seg M j₀' j₁') := by
    apply le_TrMax_intro_wd (seg M j₀' j₁') (TrMax M - j₀') hST
    intro j hj
    have ha : j < Lng (seg M j₀' j₁') := by omega
    have hb : j + 1 < Lng (seg M j₀' j₁') := by omega
    rw [nextR1_seg_adm M j₀' j₁' j (j + 1) hlt.le hj₁ ha hb]
    have hstep := TrMax_trunk_step M (j₀' + j) hM (by omega)
    have harr : j₀' + (j + 1) = j₀' + j + 1 := by omega
    rw [harr]
    exact hstep
  have hle : TrMax (seg M j₀' j₁') ≤ TrMax M - j₀' := by
    by_contra hnot
    have hgt : TrMax M - j₀' < TrMax (seg M j₀' j₁') := by omega
    have hstep := TrMax_trunk_step (seg M j₀' j₁') (TrMax M - j₀') hST hgt
    have ha : TrMax M - j₀' < Lng (seg M j₀' j₁') := by omega
    have hb : TrMax M - j₀' + 1 < Lng (seg M j₀' j₁') := by
      have := TrMax_bound (seg M j₀' j₁') hST
      omega
    rw [nextR1_seg_adm M j₀' j₁' (TrMax M - j₀') (TrMax M - j₀' + 1)
      hlt.le hj₁ ha hb] at hstep
    have he1 : j₀' + (TrMax M - j₀') = TrMax M := by omega
    have he2 : j₀' + (TrMax M - j₀' + 1) = TrMax M + 1 := by omega
    rw [he1, he2] at hstep
    have hstop := TrMax_stop_uncond M hM
    rw [hstop] at hstep
    cases hstep
  omega

/-! ## (1) `TerminalSliceReadyD_pv`（Isabelle `bux_terminal_slice_ready`, 99317） -/

/-- **`terminalSliceReadyD_holds`**（Isabelle `bux_terminal_slice_ready` 99317）: run-step BASE
descending ホストで終切片は `keystone` を適用できる状態にある。 -/
theorem terminalSliceReadyD_holds : TerminalSliceReadyD_pv := by
  intro N regD hbase hdeep hrun
  obtain ⟨⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, hj0pos, hj0lt⟩, hdesc⟩ := regD
  have hM : TPS N := RTPS_TPS N hR
  have htrlt : TrMax N < Lng N - 1 := by omega
  have hL1 : 1 < Lng N := by omega
  set j0 := (Joints N).getD ((Br N).length - 1) 0 with hj0def
  have hj0ltj1 : j0 < Lng N - 1 := by omega
  -- N ∈ DT_PS, 終切片も DT_PS（`strongmono_slice`）
  have hND : DTPS N := (DTPS_iff N).mpr ⟨hR, hmono, hdesc⟩
  have hMpD : DTPS (seg N j0 (Lng N - 1)) :=
    strongmono_slice N j0 (Lng N - 1) hND hj0ltj1 (le_refl _) (le_refl _)
  obtain ⟨hMpR, hMpMono, _hMpDesc⟩ := (DTPS_iff _).mp hMpD
  refine ⟨hMpR, hMpMono, ?_, ?_⟩
  · -- Br Mp ≠ []（幹整列 ＋ baseU_Br_empty_TrMax）
    intro hBrEmpty
    have hTrMp := baseU_Br_empty_TrMax (seg N j0 (Lng N - 1)) hBrEmpty
    have hTrMpEq : TrMax (seg N j0 (Lng N - 1)) = TrMax N - j0 :=
      TrMax_seg_ancestor_fp N j0 (Lng N - 1) hM (le_of_lt hj0lt) htrlt (by omega)
    have hLngMp : Lng (seg N j0 (Lng N - 1)) = (Lng N - 1) + 1 - j0 :=
      length_seg N j0 (Lng N - 1)
    rw [hTrMpEq, hLngMp] at hTrMp
    omega
  · -- 1 < Lng Mp - 1
    rw [length_seg]
    omega

/-! ## (2) `FrontPredBaseTransportD_pv`（Isabelle `bfx_front_Pred_base`, 104988）

要は `LastStep (Pred N) = LastStep N`（Isabelle `bfx_LastStep_Pred_base` 104893）。両ホストは
else-case（最終枝頭が非対角）で、`LastStep` は `find?`＋既定値 `J₁` の枝に落ちる。枝剥がし下で
枝頭述語が `J < Lng(Br(Pred N))` の範囲で一致することを、枝頭一致（`Br_Pred_col0_agree_fp`）＋
run 前枝頭一致（`run_prev_fp`）で示し、`find?` の最小性で `LastStep` を同定する。 -/

/-! ### list 補助（`8.2-strongmono-props` の private helper 再掲、suffix `_fp`） -/

private theorem getD_default_fp {α : Type} (l : List α) (n : ℕ) (d d' : α)
    (h : n < l.length) : l.getD n d = l.getD n d' := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h]
  rfl

private theorem getLastD_cons_eq_fp {α : Type} :
    ∀ (l : List α) (a d : α), (a :: l).getLastD d = (a :: l).getD l.length d := by
  intro l
  induction l with
  | nil => intro a d; rfl
  | cons b bs ih =>
      intro a d
      have hstep : (a :: b :: bs).getLastD d = (b :: bs).getLastD a := rfl
      rw [hstep, ih b a]
      simp only [List.length_cons, List.getD_cons_succ]
      exact getD_default_fp (b :: bs) bs.length a d (by simp)

private theorem getLastD_eq_getD_fp {α : Type} (l : List α) (d : α) (hl : l ≠ []) :
    l.getLastD d = l.getD (l.length - 1) d := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a as => simpa using getLastD_cons_eq_fp as a d

private theorem getD_append_left_fp {α : Type} (l r : List α) (J : ℕ) (d : α)
    (h : J < l.length) : (l ++ r).getD J d = l.getD J d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h]

private theorem getD_append_single_fp {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem?_getD]
  simp

private theorem getD_dropLast_fp {α : Type} (l : List α) (J : ℕ) (d : α)
    (h : J < l.length - 1) : l.dropLast.getD J d = l.getD J d := by
  have hJl : J < l.length := by omega
  have h1 : J < l.dropLast.length := by rw [List.length_dropLast]; omega
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h1, List.getElem?_eq_getElem hJl]
  simp [List.getElem_dropLast]

private theorem entry_dropLast_fp (l : PS) (i j : ℕ) (hj : j < Lng l - 1) :
    entry l.dropLast i j = entry l i j := by
  rw [List.dropLast_eq_take]
  exact entry_take l (l.length - 1) i j hj

/-- `Br M ≠ []` から `TrMax M ≠ Lng M - 1`（Isabelle は `Br_def` の場合分け）。 -/
private theorem trmax_ne_of_Brne_fp (M : PS) (hBrne : Br M ≠ []) :
    TrMax M ≠ Lng M - 1 := by
  intro heq
  exact hBrne (by simp [Br, heq])

/-- Isabelle `wid_BrLen_Pred` 相当: `Br (Pred M)` の長さ（`8.2-strongmono-props`
`Br_Pred_length_smp` の再掲）。 -/
private theorem Br_Pred_length_fp (M : PS) (hM : TPS M) (hlen : 1 < Lng M)
    (hBrne : Br M ≠ []) :
    (Br (Pred M)).length =
      (if Lng ((Br M).getLastD []) ≤ 1 then (Br M).length - 1 else (Br M).length) := by
  have hne := trmax_ne_of_Brne_fp M hBrne
  have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  rw [Br_Pred_core_nontrunk M hM hlen hne]
  by_cases hcase : Lng ((Br M).getLastD []) ≤ 1
  · rw [if_pos hcase, if_pos hcase]
    have hl : ((Br M).dropLast ++ ([] : List PS)).length = (Br M).length - 1 := by simp
    rw [hl]
  · rw [if_neg hcase, if_neg hcase]
    have hl : ((Br M).dropLast ++ [((Br M).getLastD []).dropLast]).length
        = (Br M).length - 1 + 1 := by simp
    rw [hl]
    omega

/-- `Br (Pred M)` の各成分は `Br M` の同添字成分と行 0/行 1 の左端が一致する
（Isabelle `wid_Br_Pred_col0_agree`、`8.2-strongmono-props` `Br_Pred_col0_agree_smp` の再掲）。 -/
private theorem Br_Pred_col0_agree_fp (M : PS) (hM : TPS M) (hlen : 1 < Lng M)
    (hBrne : Br M ≠ []) (J : ℕ) (hJ : J < (Br (Pred M)).length) (i : ℕ) :
    entry ((Br (Pred M)).getD J []) i 0 = entry ((Br M).getD J []) i 0 := by
  have hne := trmax_ne_of_Brne_fp M hBrne
  have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hcore := Br_Pred_core_nontrunk M hM hlen hne
  have hlenP := Br_Pred_length_fp M hM hlen hBrne
  by_cases hcase : Lng ((Br M).getLastD []) ≤ 1
  · rw [if_pos hcase] at hlenP
    rw [hcore, if_pos hcase]
    simp only [List.append_nil]
    exact congrArg (fun q => entry q i 0) (getD_dropLast_fp (Br M) J [] (by omega))
  · rw [if_neg hcase] at hlenP
    rw [hcore, if_neg hcase]
    by_cases hJlt : J < (Br M).length - 1
    · rw [getD_append_left_fp _ _ _ _ (by rw [List.length_dropLast]; omega)]
      exact congrArg (fun q => entry q i 0) (getD_dropLast_fp (Br M) J [] hJlt)
    · have hJeq : J = (Br M).length - 1 := by omega
      have hdl : (Br M).dropLast.length = (Br M).length - 1 := by simp
      rw [hJeq, ← hdl, getD_append_single_fp]
      rw [hdl, ← getLastD_eq_getD_fp (Br M) [] hBrne]
      exact entry_dropLast_fp ((Br M).getLastD []) i 0 (by omega)

/-! ### else-case `LastStep` の道具（`8.2-condIIIV-peel-values` / `8.2-condIIIV-deep3` の
private helper 再掲、suffix `_fp`） -/

/-- 最終枝頭ガード `gtN`（Isabelle `bfx_gtN` 104527、peel-values `gtN_pv` の再掲）。 -/
private theorem gtN_fp (N : PS) (hM : TPS N) (hBrne : Br N ≠ [])
    (hguard : entry N 1 (VEj1p N) < entry N 0 (VEj1p N)) :
    entry ((Br N).getD ((Br N).length - 1) []) 1 0
      < entry ((Br N).getD ((Br N).length - 1) []) 0 0 := by
  have hJ1 : (Br N).length - 1 < (Br N).length := by
    have := List.length_pos_of_ne_nil hBrne; omega
  have h0 := entry_FirstNodes_eq_component_mr N ((Br N).length - 1) 0 hM hJ1
  have h1 := entry_FirstNodes_eq_component_mr N ((Br N).length - 1) 1 hM hJ1
  rw [← h0, ← h1]
  simpa only [VEj1p] using hguard

/-- `LastStep N` の枝所属（Isabelle `bfx_run_prev` の `LSmem`、peel-values `LastStep_mem_pv`
の再掲）。 -/
private theorem LastStep_mem_fp (N : PS) (hBrne : Br N ≠ [])
    (hgtN : entry ((Br N).getD ((Br N).length - 1) []) 1 0
          < entry ((Br N).getD ((Br N).length - 1) []) 0 0) :
    entry ((Br N).getD ((Br N).length - 1) []) 0 0
      = entry ((Br N).getD (LastStep N) []) 0 0
    ∧ entry ((Br N).getD (LastStep N) []) 1 0
      < entry ((Br N).getD (LastStep N) []) 0 0 := by
  have hLpos : 0 < (Br N).length := List.length_pos_of_ne_nil hBrne
  have hL : (Br N).length ≠ 0 := by omega
  have hnd : entry ((Br N).getD ((Br N).length - 1) []) 0 0
           ≠ entry ((Br N).getD ((Br N).length - 1) []) 1 0 := by omega
  have hLSval : LastStep N
      = ((List.range (Br N).length).find? (fun J =>
          decide (entry ((Br N).getD ((Br N).length - 1) []) 0 0 = entry ((Br N).getD J []) 0 0) &&
          decide (entry ((Br N).getD J []) 1 0 < entry ((Br N).getD J []) 0 0))).getD
            ((Br N).length - 1) := by
    unfold LastStep
    simp only [hL, if_false]
    split
    · next heq => exact absurd heq hnd
    · rfl
  rw [hLSval]
  cases hfind : (List.range (Br N).length).find? (fun J =>
      decide (entry ((Br N).getD ((Br N).length - 1) []) 0 0 = entry ((Br N).getD J []) 0 0) &&
      decide (entry ((Br N).getD J []) 1 0 < entry ((Br N).getD J []) 0 0)) with
  | none =>
      rw [Option.getD_none]
      exact ⟨rfl, hgtN⟩
  | some c =>
      rw [Option.getD_some]
      have hp := List.find?_some hfind
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
      exact hp

/-- run 前枝の事実（Isabelle `bfx_run_prev` 104581 の両結論）: descending 弱降順で
`J₁-1` 枝頭 row-0 は最終枝頭に一致し（(1)）、それ自身がガードされる（(2)）。 -/
private theorem run_prev_fp (N : PS) (hBrne : Br N ≠ [])
    (hdesc : descendingB (Br N) = true)
    (hgtN : entry ((Br N).getD ((Br N).length - 1) []) 1 0
          < entry ((Br N).getD ((Br N).length - 1) []) 0 0)
    (hrun : LastStep N < (Br N).length - 1) :
    entry ((Br N).getD ((Br N).length - 2) []) 0 0
      = entry ((Br N).getD ((Br N).length - 1) []) 0 0
    ∧ entry ((Br N).getD ((Br N).length - 2) []) 1 0
      < entry ((Br N).getD ((Br N).length - 2) []) 0 0 := by
  obtain ⟨hLS0, hLS1⟩ := LastStep_mem_fp N hBrne hgtN
  have hJ1lt : (Br N).length - 1 < (Br N).length := by omega
  have hJmlt : (Br N).length - 2 < (Br N).length := by omega
  -- cdomB (LastStep, Jm) と cdomB (Jm, J₁)
  have d1 := (cdomB_iff _ _).mp ((descendingB_iff (Br N)).mp hdesc
    (LastStep N) ((Br N).length - 2) (by omega) hJmlt)
  have d2 := (cdomB_iff _ _).mp ((descendingB_iff (Br N)).mp hdesc
    ((Br N).length - 2) ((Br N).length - 1) (by omega) hJ1lt)
  -- (1) h0eq : head0(Jm) = head0(J₁)
  have h0eq : entry ((Br N).getD ((Br N).length - 2) []) 0 0
            = entry ((Br N).getD ((Br N).length - 1) []) 0 0 := by
    have hd1 := d1.1; have hd2 := d2.1
    omega
  refine ⟨h0eq, ?_⟩
  -- head0(LastStep) = head0(Jm)
  have hLSJm : entry ((Br N).getD (LastStep N) []) 0 0
             = entry ((Br N).getD ((Br N).length - 2) []) 0 0 := by
    have := hLS0; omega
  -- tie : head1(Jm) ≤ head1(LastStep)
  have htie := d1.2 hLSJm
  omega

/-- `LastStep` の最小性（Isabelle `vgx_LastStep_elsecase` の全域版、deep3 `LastStep_find_min_d3`
の再掲）: 非対角ガード下で `k < LastStep M` の枝 `k` は `S`-述語を満たさない。 -/
private theorem LastStep_find_min_fp (M : PS) (hBrne : Br M ≠ [])
    (hnd : entry ((Br M).getD ((Br M).length - 1) []) 0 0
         ≠ entry ((Br M).getD ((Br M).length - 1) []) 1 0)
    (k : ℕ) (hk : k < LastStep M) :
    ¬ (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD k []) 0 0
       ∧ entry ((Br M).getD k []) 1 0 < entry ((Br M).getD k []) 0 0) := by
  have hLpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hL : (Br M).length ≠ 0 := by omega
  rintro ⟨heq0, hlt0⟩
  have hpk : (decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD k []) 0 0)
             && decide (entry ((Br M).getD k []) 1 0 < entry ((Br M).getD k []) 0 0)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨heq0, hlt0⟩
  have hLSval : LastStep M
      = ((List.range (Br M).length).find? (fun J =>
          decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD J []) 0 0) &&
          decide (entry ((Br M).getD J []) 1 0 < entry ((Br M).getD J []) 0 0))).getD
            ((Br M).length - 1) := by
    unfold LastStep
    simp only [hL, if_false]
    split
    · next heq => exact absurd heq hnd
    · rfl
  rw [hLSval] at hk
  cases hfind : (List.range (Br M).length).find? (fun J =>
      decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD J []) 0 0) &&
      decide (entry ((Br M).getD J []) 1 0 < entry ((Br M).getD J []) 0 0)) with
  | none =>
      simp only [hfind, Option.getD_none] at hk
      have hkmem : k ∈ List.range (Br M).length := List.mem_range.mpr (by omega)
      exact (List.find?_eq_none.mp hfind) k hkmem hpk
  | some c =>
      simp only [hfind, Option.getD_some] at hk
      have hf' : (List.range' 0 (Br M).length).find? (fun J =>
          decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD J []) 0 0) &&
          decide (entry ((Br M).getD J []) 1 0 < entry ((Br M).getD J []) 0 0)) = some c := by
        simpa using hfind
      have hmin := (List.find?_range'_eq_some.mp hf').2.2 k (Nat.zero_le k) hk
      rw [hpk] at hmin
      simp at hmin

/-! ### `LastStep` の枝剥がし転送（Isabelle `bfx_LastStep_Pred_base`, 104893） -/

/-- **`lastStepPred_fp`**（Isabelle `bfx_LastStep_Pred_base` 104893）: run-step BASE descending
ホストで `LastStep (Pred N) = LastStep N`。両ホスト else-case、枝頭述語が `J < Lng(Br(Pred N))`
で一致（`Br_Pred_col0_agree_fp` ＋ `run_prev_fp`）ゆえ `find?` 最小性で同定する。 -/
private theorem lastStepPred_fp (N : PS) (hM : TPS N)
    (hBrne : Br N ≠ []) (hdesc : descendingB (Br N) = true) (hL1 : 1 < Lng N)
    (htrne : TrMax N ≠ Lng N - 1)
    (hguard : entry N 1 (VEj1p N) < entry N 0 (VEj1p N))
    (hbase : VEj1p N = Lng N - 1)
    (hrun : LastStep N < (Br N).length - 1) :
    LastStep (Pred N) = LastStep N := by
  -- 枝数減少と `Br (Pred N) ≠ []`
  have hBrlenP : (Br (Pred N)).length = (Br N).length - 1 :=
    BrLen_Pred_base_pv N hM hBrne hL1 htrne hbase
  have hBrPne : Br (Pred N) ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hBrlenP]; omega
  have hidxP : (Br (Pred N)).length - 1 = (Br N).length - 2 := by rw [hBrlenP]; omega
  -- 最終枝ガード `gtN` と非対角
  have hgtN := gtN_fp N hM hBrne hguard
  have hndN : entry ((Br N).getD ((Br N).length - 1) []) 0 0
            ≠ entry ((Br N).getD ((Br N).length - 1) []) 1 0 := by omega
  -- run 前枝の事実
  have hrp := run_prev_fp N hBrne hdesc hgtN hrun
  -- col0 一致（最終枝位置）
  have hJ1Plt : (Br (Pred N)).length - 1 < (Br (Pred N)).length := by
    have := List.length_pos_of_ne_nil hBrPne; omega
  have hcolP0 := Br_Pred_col0_agree_fp N hM hL1 hBrne ((Br (Pred N)).length - 1) hJ1Plt 0
  have hcolP1 := Br_Pred_col0_agree_fp N hM hL1 hBrne ((Br (Pred N)).length - 1) hJ1Plt 1
  -- 目標枝頭一致 `tgtEq` と Pred-else-case ガード `gtP`
  have tgtEq : entry ((Br (Pred N)).getD ((Br (Pred N)).length - 1) []) 0 0
             = entry ((Br N).getD ((Br N).length - 1) []) 0 0 := by
    rw [hcolP0, hidxP]; exact hrp.1
  have gtP : entry ((Br (Pred N)).getD ((Br (Pred N)).length - 1) []) 1 0
           < entry ((Br (Pred N)).getD ((Br (Pred N)).length - 1) []) 0 0 := by
    rw [hcolP1, hcolP0, hidxP]; exact hrp.2
  have hndP : entry ((Br (Pred N)).getD ((Br (Pred N)).length - 1) []) 0 0
            ≠ entry ((Br (Pred N)).getD ((Br (Pred N)).length - 1) []) 1 0 := by omega
  -- `LastStep` 所属（両ホスト）
  obtain ⟨hLS0N, hLS1N⟩ := LastStep_mem_fp N hBrne hgtN
  obtain ⟨hLS0P, hLS1P⟩ := LastStep_mem_fp (Pred N) hBrPne gtP
  -- 範囲性
  have hLSltP0 : LastStep (Pred N) < (Br (Pred N)).length := LastStep_lt_Lng_Br (Pred N) hBrPne
  have hLSNltP : LastStep N < (Br (Pred N)).length := by rw [hBrlenP]; omega
  -- col0 一致（両 LastStep 位置）
  have hcolLN0 := Br_Pred_col0_agree_fp N hM hL1 hBrne (LastStep N) hLSNltP 0
  have hcolLN1 := Br_Pred_col0_agree_fp N hM hL1 hBrne (LastStep N) hLSNltP 1
  have hcolLP0 := Br_Pred_col0_agree_fp N hM hL1 hBrne (LastStep (Pred N)) hLSltP0 0
  have hcolLP1 := Br_Pred_col0_agree_fp N hM hL1 hBrne (LastStep (Pred N)) hLSltP0 1
  -- 述語成立（`predP` を `LastStep N` で、`predN` を `LastStep (Pred N)` で）
  have hpredP : entry ((Br (Pred N)).getD ((Br (Pred N)).length - 1) []) 0 0
                = entry ((Br (Pred N)).getD (LastStep N) []) 0 0
              ∧ entry ((Br (Pred N)).getD (LastStep N) []) 1 0
                < entry ((Br (Pred N)).getD (LastStep N) []) 0 0 :=
    ⟨by omega, by omega⟩
  have hpredN : entry ((Br N).getD ((Br N).length - 1) []) 0 0
                = entry ((Br N).getD (LastStep (Pred N)) []) 0 0
              ∧ entry ((Br N).getD (LastStep (Pred N)) []) 1 0
                < entry ((Br N).getD (LastStep (Pred N)) []) 0 0 :=
    ⟨by omega, by omega⟩
  -- 最小性による両向きの不等式
  have hnA : ¬ LastStep N < LastStep (Pred N) := fun hlt =>
    LastStep_find_min_fp (Pred N) hBrPne hndP (LastStep N) hlt hpredP
  have hnB : ¬ LastStep (Pred N) < LastStep N := fun hlt =>
    LastStep_find_min_fp N hBrne hndN (LastStep (Pred N)) hlt hpredN
  omega

/-! ## 前置切片 `Pred` 転送の放出（Isabelle `bfx_front_Pred_base`, 104988） -/

/-- **`frontPredBaseTransportD_holds`**（Isabelle `bfx_front_Pred_base` 104988）: run-step BASE
descending ホストで前置切片 `Pred N` は `N` の前置切片に一致する。`LastStep` 転送
（`lastStepPred_fp`）＋ `FirstNodes` 転送（`FN_Pred_LS_base_pv`）＋ 前置 `Pred` 不変
（`seg_Pred_eq`）で組む。 -/
theorem frontPredBaseTransportD_holds : FrontPredBaseTransportD_pv := by
  intro N regD hbase hdeep hrun
  obtain ⟨⟨⟨⟨hR, hmono, hBrne⟩, hguard⟩, _hj0pos, _hj0lt⟩, hdesc⟩ := regD
  have hM : TPS N := RTPS_TPS N hR
  have hL1 : 1 < Lng N := by omega
  have htrne : TrMax N ≠ Lng N - 1 := by omega
  -- `LastStep (Pred N) = LastStep N`
  have hLSP : LastStep (Pred N) = LastStep N :=
    lastStepPred_fp N hM hBrne hdesc hL1 htrne hguard hbase hrun
  -- `FirstNodes` の `Pred` 転送（公開）
  have hFNP : (FirstNodes (Pred N)).getD (LastStep N) 0 = (FirstNodes N).getD (LastStep N) 0 :=
    FN_Pred_LS_base_pv N hM hBrne hL1 htrne hbase hrun
  -- 前置境界と前置 `Pred` 不変
  have hm1 : (FirstNodes N).getD (LastStep N) 0 - 1 < Lng N - 1 :=
    (m1_bounds N hM hmono hBrne).2
  have hseg : seg (Pred N) 0 ((FirstNodes N).getD (LastStep N) 0 - 1)
            = seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1) :=
    seg_Pred_eq N 0 ((FirstNodes N).getD (LastStep N) 0 - 1) hL1 (Nat.zero_le _) hm1
  rw [hLSP, hFNP]
  exact hseg

#print axioms terminalSliceReadyD_holds
#print axioms frontPredBaseTransportD_holds

end PSS
