import «8».«8.5-Trans-fseq-condV»
import «7».«7.4-RightNodes-Mark»
import «7».«7.3-Mark-rightmost1»
import «7».«7.4-RightAnces-RightNodes»

/-!
# §8.5 exchV の named Prop の解消（`ExchV_*` の drop-in）

- 原文: `tmp/content.md` §8.5「補題（条件(V)の下での各種scb分解）」(5213) と
  その周辺（`c₁` の形・`t₂ ≠ 0`・再帰の guard）。
- 対象: ビルド済み «8».«8.5-Trans-fseq-condV» が green-modulo に残した 6 本の
  named Prop。本ファイルは **4 本を無条件に discharge** し、**1 本を削減**する
  （house pattern: 定理の型が Prop そのもの＝drop-in が elaborator により保証される）。
  | Prop | 本ファイル | 状態 |
  |---|---|---|
  | `ExchV_condV_setup` | `condV_setup_holds` | ✅ 無条件 |
  | `ExchV_scbdec_c1_shape` | `c1_shape_holds` | ✅ 無条件 |
  | `ExchV_t2_nonzero_condV` | `t2_nonzero_condV_holds` | ✅ 無条件 |
  | `ExchV_scbdec_fseq_condV` | `fseq_condV_holds` | ✅ 無条件 |
  | `ExchV_scbdec_adm_forms` | `adm_forms_holds` | ⚠️ `ExchVres_adm_towers` 上 |
  | `ExchV_nf3x` | — | ❌ scope 外（§8.4 クラスタ） |
- Isabelle（設計図）:
  - `ExchV_condV_setup` = `s85b_condV_setup` (isabelle/layerB/pss_wip.thy:57120)
  - `ExchV_scbdec_c1_shape` = `m_8_5_scbdec_c1_shape` (同 :51286)
  - `ExchV_t2_nonzero_condV` = `m_8_5_scbdec_t2_nonzero_condV` (同 :57150)
  - `ExchV_scbdec_fseq_condV` = `m_8_5_scbdec_fseq_condV` (同 :51466) の (2)(3)
    ＝ `trans_surgery_localized` (同 :23635) ＋ `m_8_5_TransCondV_producer`
    (同 :38761、crux は `m_8_5_condV_uv` 同 :38509 ＋ `viB_suffix_max` 同 :4177)
  - `ExchV_scbdec_adm_forms` = `m_8_5_scbdec_adm_forms` (同 :57556)
- 構造（Isabelle と 1:1、ただし Lean 側の資産で短縮）:
  - setup: `transJ1 > 0` は条件(V) の算術（`s85b_condV_bridge(1)`, 同 :57072 の
    `1 < transJ1 M` に対応）。`transT1 ≠ 0_B` は `Trans_preserves_zeroT`
    （= `m_7_3_Trans_zeroT`）の対偶＋`Lng (Pred M) = Lng M - 1 ≥ 2`。
  - c1_shape: `transC1_single_principal`＋`principal_reconstruct` で
    `c₁ = D_{transV} t₂`、頭部指標の読み出しは `Mark_leftend_form_proper`
    （= Isabelle `Mark_leftend_form` の proper 枝）＋右端枝は
    `Mark_rightmost1_forward`（Isabelle は `Mark_leftend_form` 一本で両枝を
    まとめているが、Lean 側は proper 枝と右端枝が別補題なので `Marked_index_le_last`
    で場合分けする）。`t₂ ∈ T_B` は `Mark_mem_T_B` からの `dfree` 読み出し
    （= Isabelle `m_7_3_Mark_in_T_B`）。`transJm1 < Lng M - 1` は
    `parent_lt_of_hasParent`＋`Adm_le`（= Isabelle `monoT_branch_hasParent`＋
    `adm_Adm_le`/`nadm_Adm_lt`）。
  - t2_nonzero: `t₂ = 0` なら `c₁ = D_{M₁,j₋₁} 0` となり、条件(V) の
    `j₋₁ ≤ j₀ < j₁ - 1`（= `Lng (Pred M) - 1` より真に手前）と
    `Mark_tail_nonzero` が矛盾する。Isabelle は同じ矛盾を
    `m_7_3_Mark_rightmost1` の ⟸ 向きで取っているが、Lean ではその ⟸ 向きの
    中身がそのまま `Mark_tail_nonzero` として公開されているので直接使う
    （`zeroT (Pred M) = false` の経由が不要になる）。
  - `ExchV_nf3x` = `atx_nf3x` (同 :86273)
- 依存（すべてビルド済み）: «8».«8.5-Trans-fseq-condV»（`ExchV_*` の Prop 本体、
  推移的に «7».«7.3-c1-c2-order» = `transC1_single_principal` /
  `principal_reconstruct` / `Marked_index_le_last`、«7».«7.3-Trans-welldefined»
  = `replaceScb_spec` / `Trans_Mark_mono_equations` / `Trans_Mark_invariant` /
  `transC2Core_properties`、«7».«7.2-add-scb» = `add_scb_marked`、
  «5».«5.3-pred-is-oper1» = `pred_is_oper1`）、«7».«7.4-RightNodes-Mark»
  （`Mark_leftend_form_proper`）、«7».«7.3-Mark-rightmost1»
  （`Mark_rightmost1_forward` / `Mark_tail_nonzero`）、
  «7».«7.4-RightAnces-RightNodes»（`RightNodes_transC2_tail`
  ＝ Isabelle `ra_RightNodes_transC2_tail`）。
- 訂正: なし（A28 は取り下げ済み、`corrections-old.md`:95）。
- ⚠️**先行ファイルの悲観的注記の訂正**: «8».«8.6-condVI-close»:315 は
  `ExchV_scbdec_c1_shape` / `ExchV_scbdec_fseq_condV` を
  「`trans_surgery_localized` の Lean 未移植ゆえ閉じられない」と報告しているが、
  これは**誤り**だった。`trans_surgery_localized` は Lean の `replaceScb_spec`
  （7.3-Trans-welldefined:318）で置き換えられ（しかも 1 対で両側が出るので
  Isabelle の uniqueness 段が不要）、両 Prop とも本ファイルで**無条件に閉じている**。
  真に未移植なのは **§8.4 の `s84x_L` / `m_8_4_oper_props_5` クラスタ**だけである。
- 非空虚性（`M = (0,0)(1,1)(1,1)`, `8.5-Trans-fseq-condV` ヘッダ報告の条件(V)
  最小ホスト）: `transCondV = monoT = reduced = adm M (transJ0 M) = true`、
  `(transJ1, transJ0, transJm1) = (2,0,0)`、`transT1 ≠ 0_B`、`transT2 ≠ 0_B`
  （`#eval` で確認）。＝6 本の Prop の仮定はすべて充足可能で、本ファイルが証明した
  `transT1 ≠ 0_B` / `transT2 ≠ 0_B` / `transJm1 = transJ0` は数値と一致する。
- 状態: GREEN（sorry 0）。4/6 無条件 discharge ＋ 1/6 削減。
  残差は `ExchVres_adm_towers`（本ファイル定義）と `ExchV_nf3x`（未着手）の 2 本で、
  **どちらも §8.4 scb 分解クラスタ（`m_8_4_oper_props_5` / `s84x_L` / `s84x_Np`）の
  Lean 未移植分**という単一の欠落に帰着する（`needs` 参照）。
-/

namespace PSS

/-! ## 条件(V) の算術（Isabelle `s85b_condV_bridge`, pss_wip.thy:57072） -/

/-- 条件 (V) の 3 連言を読み出す。 -/
private theorem condV_parts_xv {M : PS} (h : transCondV M = true) :
    0 < entry M 1 (lastIdx M) ∧
      entry M 1 (lastParent M) + 1 = entry M 1 (lastIdx M) ∧
      lastParent M + 1 < lastIdx M := by
  simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- Isabelle `s85b_condV_bridge(1)(2)`: 条件(V) は `1 < j₁` と `j₀ + 1 < j₁` を含む。 -/
private theorem condV_bridge_xv {M : PS} (h : transCondV M = true) :
    1 < transJ1 M ∧ transJ0 M + 1 < transJ1 M := by
  have hc := condV_parts_xv h
  refine ⟨by simp only [transJ1]; omega, by simp only [transJ1, transJ0]; omega⟩

/-! ## `ExchV_condV_setup`（Isabelle `s85b_condV_setup`, pss_wip.thy:57120） -/

theorem condV_setup_holds : ExchV_condV_setup := by
  intro M hR hM _hmono hcond
  have hbridge := condV_bridge_xv hcond
  have hj₁ : 0 < transJ1 M := by omega
  refine ⟨hj₁, ?_⟩
  -- `transT1 M = Trans (Pred M) ≠ 0_B`
  intro ht₁
  have hzP : zeroT (Pred M) = true :=
    (Trans_preserves_zeroT (Pred M) (Pred_TPS M hM)).2 ht₁
  -- `Lng M > 2` （条件(V) の `j₀ + 1 < j₁ = Lng M - 1`）なので `Lng (Pred M) ≥ 2`
  have hlen : 2 < Lng M := by
    have : 1 < transJ1 M := hbridge.1
    simp only [transJ1, lastIdx] at this
    omega
  have hLP : Lng (Pred M) = Lng M - 1 := by
    simp only [Pred]
    rw [if_neg (by omega)]
    simp
  have : Lng (Pred M) = 1 := by
    simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hzP
    exact hzP.1
  omega

/-! ## `ExchV_scbdec_c1_shape`（Isabelle `m_8_5_scbdec_c1_shape`, pss_wip.thy:51286） -/

/-- `Pred M = M.dropLast` は行 1 の entry を（末尾より手前で）保つ。 -/
private theorem entry_Pred_xv (M : PS) (j : ℕ) (hlen : 1 < Lng M)
    (hj : j < Lng M - 1) : entry (Pred M) 1 j = entry M 1 j := by
  rw [Pred_eq_take M hlen]
  exact entry_take M (Lng M - 1) 1 j (by omega)

/-- Isabelle `Mark_leftend_form` (pss_wip.thy:5368) の、`Trans` 非零下での
  非退化版（Lean の proper 枝と右端枝を貼り合わせたもの）。 -/
private theorem Mark_leftend_nonzero_xv (N : PS) (m : ℕ)
    (hm : Marked N m) (hR : RTPS N) (hT : Trans N ≠ BZero) :
    ∃ t, Mark N m = Dprin (entry N 1 m : ℕ∞) t := by
  have hlast := Marked_index_le_last hm
  by_cases hlt : m < Lng N - 1
  · exact Mark_leftend_form_proper N m hm hR hlt
  · have hmLast : m = Lng N - 1 := by omega
    have hz : zeroT N = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hz'
      exact hT ((Trans_preserves_zeroT N (RTPS_TPS N hR)).1 hz')
    exact ⟨BZero, by rw [hmLast]; exact Mark_rightmost1_forward N hR hz⟩

theorem c1_shape_holds : ExchV_scbdec_c1_shape := by
  intro M hR hM hmono hj₁ ht₁
  have hlen : 1 < Lng M := by
    simp only [transJ1, lastIdx] at hj₁; omega
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hmarked : Marked (Pred M) (transJm1 M) := by
    simpa [transJm1, transJ0, lastParent, lastIdx] using Marked_Pred_Adm M hM hlen hp
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  -- (4) `j₋₁ < Lng M - 1`
  have hjm1lt : transJm1 M < Lng M - 1 := by
    have hpl : parent M 0 (Lng M - 1) < Lng M - 1 := by
      have := parent_lt_of_hasParent M 0 (Lng M - 1) hp
      omega
    have hAdm := Adm_le M (parent M 0 (Lng M - 1))
    simp only [transJm1, transJ0, lastParent, lastIdx]
    omega
  -- `c₁` は単項
  have hc₁len := transC1_single_principal M hR hmono hj₁ ht₁
  have hc₁eq : transC1 M = Dprin (transV M) (transT2 M) := by
    simpa [transV, transT2] using principal_reconstruct hc₁len
  -- 頭部指標の読み出し
  have hmarkeq : transC1 M = Mark (Pred M) (transJm1 M) := rfl
  obtain ⟨t, ht⟩ := Mark_leftend_nonzero_xv (Pred M) (transJm1 M) hmarked hpredR ht₁
  have hentryP : entry (Pred M) 1 (transJm1 M) = entry M 1 (transJm1 M) :=
    entry_Pred_xv M (transJm1 M) hlen hjm1lt
  have hV : transV M = (entry M 1 (transJm1 M) : ℕ∞) := by
    have : transC1 M = Dprin (entry M 1 (transJm1 M) : ℕ∞) t := by
      rw [hmarkeq, ht, hentryP]
    rw [hc₁eq] at this
    simpa [Dprin] using congrArg bpHeadV this
  -- `t₂ ∈ T_B`
  have hc₁TB : transC1 M ∈ T_B := by
    simpa [transC1, transJm1, transJ0, lastParent, lastIdx] using
      Mark_mem_T_B (Pred M) _ hpredR hmarked
  have ht₂TB : transT2 M ∈ T_B := by
    rw [hc₁eq] at hc₁TB
    change dfree_BT (.trm [.db (transV M) (transT2 M)]) = true at hc₁TB
    simp only [dfree_BT, dfree_BPList, dfree_BP, Bool.and_eq_true] at hc₁TB
    exact hc₁TB.1.2
  exact ⟨hV, by rw [hc₁eq, hV], ht₂TB, hjm1lt⟩

/-! ## `ExchV_t2_nonzero_condV`（Isabelle `m_8_5_scbdec_t2_nonzero_condV`, :57150） -/

theorem t2_nonzero_condV_holds : ExchV_t2_nonzero_condV := by
  intro M hR hM hmono hcond
  obtain ⟨hj₁, ht₁⟩ := condV_setup_holds M hR hM hmono hcond
  obtain ⟨_hV, hc₁eq, _ht₂TB, _hjm1lt⟩ := c1_shape_holds M hR hM hmono hj₁ ht₁
  intro ht₂
  have hbridge := condV_bridge_xv hcond
  have hlen : 1 < Lng M := by
    simp only [transJ1, lastIdx] at hj₁; omega
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hmarked : Marked (Pred M) (transJm1 M) := by
    simpa [transJm1, transJ0, lastParent, lastIdx] using Marked_Pred_Adm M hM hlen hp
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hLP : Lng (Pred M) = Lng M - 1 := by
    simp only [Pred]
    rw [if_neg (by omega)]
    simp
  -- 条件(V): `j₋₁ ≤ j₀ < j₁ - 1 = Lng (Pred M) - 1`
  have hjm1lt : transJm1 M < Lng (Pred M) - 1 := by
    have hAdm := Adm_le M (transJ0 M)
    have h2 := hbridge.2
    simp only [transJm1, transJ1, lastIdx] at *
    omega
  have hentryP : entry (Pred M) 1 (transJm1 M) = entry M 1 (transJm1 M) :=
    entry_Pred_xv M (transJm1 M) hlen (by omega)
  have hbad : Mark (Pred M) (transJm1 M) =
      Dprin (entry (Pred M) 1 (transJm1 M) : ℕ∞) BZero := by
    have : transC1 M = Dprin (entry M 1 (transJm1 M) : ℕ∞) BZero := by
      rw [hc₁eq, ht₂]
    rw [hentryP]
    exact this
  exact Mark_tail_nonzero (Pred M) (transJm1 M) hmarked hpredR hjm1lt hbad

/-! ## `ExchV_scbdec_fseq_condV`（Isabelle `m_8_5_scbdec_fseq_condV`, :51466 の (2)(3)）

Isabelle は `trans_surgery_localized` (:23635) ＋ `m_8_5_TransCondV_producer` (:38761)
＋ `m_7_2_scb_unique_sb` の 3 段（＝2 つの witness 対を作ってから一意性で同一視する）
だが、Lean では `replaceScb_spec`（7.3-Trans-welldefined:318）が
**1 つの対 `(s,b)` で `Trans (Pred M)` 側と `Trans M` 側の scb 分解を同時に**出すので、
uniqueness 段（`m_7_2_scb_unique_sb`）は不要になる。producer の crux `k1` は
Isabelle と同じく `RightNodes (transC2 M) = [u, v]`（`RightNodes_transC2_tail`
＝ `ra_RightNodes_transC2_tail`）＋ 算術側条件 `uv` に落ちる。 -/

/-! ### 算術側条件 `uv`（Isabelle `m_8_5_condV_uv`, :38509） -/

/-- Isabelle `viB_suffix_max` (pss_wip.thy:4177) の step: `Adm M j₀ ≤ j < j₀` なら
  `j + 1` は非許容なので行 1 は真に増える。 -/
private theorem entry1_step_xv (M : PS) (j₀ j : ℕ) (hna : adm M j₀ = false)
    (hj₀ : j₀ < Lng M) (hge : Adm M j₀ ≤ j) (hlt : j < j₀) :
    entry M 1 j < entry M 1 (j + 1) := by
  -- `(Adm M j₀, j₀]` の点はすべて非許容（`Adm_max` の対偶）
  have hnaS : adm M (j + 1) = false := by
    by_contra hcon
    have hadm : adm M (j + 1) = true := by simpa using hcon
    rcases Nat.lt_or_ge (j + 1) j₀ with h | h
    · have := Adm_max M (j + 1) j₀ hadm (by omega)
      omega
    · have hEq : j + 1 = j₀ := by omega
      rw [hEq] at hadm
      rw [hadm] at hna
      exact absurd hna (by simp)
  -- `nadm` の分解: 長さ枝は `j + 1 ≤ j₀ < Lng M` で潰れる
  have hnadm : nadm M (j + 1) = true := by
    simpa [adm] using hnaS
  simp only [nadm, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hnadm
  have hlen : ¬ (Lng M < j + 1) := by omega
  rcases hnadm with h | h
  · exact absurd h hlen
  · have hn1 : nextrel1 M j (j + 1) = true := by
      simpa [nextR] using h.1
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hn1
    exact hn1.1.1.2

/-- Isabelle `viB_suffix_max` (pss_wip.thy:4177) の主張を、Max を経由せず
  そのまま必要な形（`entry M 1 (Adm M j₀) ≤ entry M 1 j₀`）で述べたもの。 -/
private theorem entry1_Adm_le_xv (M : PS) (j₀ : ℕ) (hj₀ : j₀ < Lng M) :
    entry M 1 (Adm M j₀) ≤ entry M 1 j₀ := by
  by_cases hadm : adm M j₀ = true
  · simp [Adm, hadm]
  · have hna : adm M j₀ = false := by simpa using hadm
    -- `Adm M j₀ ≤ a ≤ j₀` 上で行 1 は単調（`j₀ - a` に関する帰納）
    have hmono : ∀ d a, d = j₀ - a → Adm M j₀ ≤ a → a ≤ j₀ →
        entry M 1 a ≤ entry M 1 j₀ := by
      intro d
      induction d with
      | zero => intro a hd _ hle; have : a = j₀ := by omega
                rw [this]
      | succ d ih =>
          intro a hd hge hle
          have hlt : a < j₀ := by omega
          have hstep := entry1_step_xv M j₀ a hna hj₀ hge hlt
          have hnext : entry M 1 (a + 1) ≤ entry M 1 j₀ :=
            ih (a + 1) (by omega) (by omega) (by omega)
          omega
    exact hmono (j₀ - Adm M j₀) (Adm M j₀) rfl (le_refl _) (Adm_le M j₀)

/-- Isabelle `m_8_5_condV_uv` (pss_wip.thy:38509)。 -/
private theorem condV_uv_xv (M : PS) (hM : TPS M) (hmono : monoT M = true)
    (hj₁ : 0 < transJ1 M) (hcond : transCondV M = true) :
    entry M 1 (transJm1 M) < entry M 1 (transJ1 M) := by
  have hlen : 1 < Lng M := by
    simp only [transJ1, lastIdx] at hj₁; omega
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hj₀lt : transJ0 M < Lng M - 1 := by
    simpa [transJ0, lastParent, lastIdx] using
      parent_lt_of_hasParent M 0 (Lng M - 1) hp
  have hle : entry M 1 (transJm1 M) ≤ entry M 1 (transJ0 M) := by
    simpa [transJm1] using entry1_Adm_le_xv M (transJ0 M) (by omega)
  have hev := condV_parts_xv hcond
  simp only [transJ1, transJ0] at *
  omega

/-! ### 手術（Isabelle `trans_surgery_localized`, :23635） -/

/-- `c₁` は principal（`transC1_single_principal` の項レベル読み出し）。 -/
private theorem transC1_principal_xv (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj₁ : 0 < transJ1 M) (ht₁ : transT1 M ≠ BZero) :
    ∃ p, transC1 M = .trm [p] := by
  have h := principal_reconstruct (transC1_single_principal M hR hmono hj₁ ht₁)
  exact ⟨.db (transV M) (transT2 M), by simpa [Dprin] using h⟩

/-- `c₂` は principal（`transC2Core_principal` 相当を `transC2_condV_e5` の形から）。 -/
private theorem transC2_principal_xv (M : PS) (hcond : transCondV M = true) :
    ∃ p, transC2 M = .trm [p] := by
  have h : transC2 M = Dprin (transV M)
      (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) := by
    have hA : (transCondI M || transCondIII M || transCondV M) = true := by
      simp [hcond]
    simp [transC2, transC2Core, hA, transJ1]
  exact ⟨.db (transV M) _, by simpa [Dprin] using h⟩

/-- Isabelle `trans_surgery_localized` (pss_wip.thy:23635) の Lean 版。
  `replaceScb_spec` が両側の scb 分解を **1 つの対 `(s,b)`** で出すため、
  Isabelle の `trans_surgery_value` ＋ 読み戻しの段が不要になる。 -/
private theorem trans_surgery_localized_xv (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) (hj₁ : 0 < transJ1 M) (ht₁ : transT1 M ≠ BZero)
    (hc₂P : ∃ p, transC2 M = .trm [p]) :
    ∃ s b, scb_decomp (Trans (Pred M)) s (flatBT (transC1 M)) b ∧
      scb_decomp (Trans M) s (flatBT (transC2 M)) b := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by
    simp only [transJ1, lastIdx] at hj₁; omega
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hmarked : Marked (Pred M) (transJm1 M) := by
    simpa [transJm1, transJ0, lastParent, lastIdx] using Marked_Pred_Adm M hM hlen hp
  have hinv := (Trans_Mark_invariant (Pred M) hpredR).2.2 _ hmarked
  have ht₁TB : Trans (Pred M) ∈ T_B := (Trans_Mark_invariant (Pred M) hpredR).1
  have hc₁TB : transC1 M ∈ T_B := by
    simpa [transC1, transJm1, transJ0, lastParent, lastIdx] using hinv.1
  have hmb : (Trans (Pred M), transC1 M) ∈ MarkedB := by
    simpa [transT1, transC1, transJm1, transJ0, lastParent] using hinv.2
  have hc₁P := transC1_principal_xv M hR hmono hj₁ ht₁
  -- `c₂ ∈ T_B`
  have hc₂TB : transC2 M ∈ T_B := by
    have := transC2Core_properties M (transC1 M) hc₁TB hc₁P
    simpa [transC2, transV, transT2] using this.1
  obtain ⟨s, b, hd₁, _hflat, hd₂⟩ :=
    replaceScb_spec ht₁TB hc₁TB hc₁P hc₂TB hc₂P hmb
  refine ⟨s, b, hd₁, ?_⟩
  -- `Trans M = replaceScb (Trans (Pred M)) c₁ c₂`（mono 枝の再帰方程式）
  have hTM : Trans M = replaceScb (Trans (Pred M)) (transC1 M) (transC2 M) := by
    have heq := (Trans_Mark_mono_equations M hR hlen hmono).1
    have ht₁b : (Trans (Pred M) == BZero) = false := by
      simpa [beq_iff_eq, transT1] using ht₁
    simpa [transT1, transC1, transC2, transV, transT2, transJm1, transJ0,
      lastParent, ht₁b] using heq
  rw [hTM]
  exact hd₂

/-! ### 本体 -/

theorem fseq_condV_holds : ExchV_scbdec_fseq_condV := by
  intro M hR hM hmono hj₁ ht₁ hcond
  have hc₂P := transC2_principal_xv M hcond
  obtain ⟨s, b, hd₁, hd₂⟩ :=
    trans_surgery_localized_xv M hR hmono hj₁ ht₁ hc₂P
  obtain ⟨_hV, hc₁eq, _ht₂TB, _hjm1lt⟩ := c1_shape_holds M hR hM hmono hj₁ ht₁
  refine ⟨s, b, ?_, hd₂, ?_⟩
  · -- (2) 底: `M[1] = Pred M`、`c₁ = D_{M₁,j₋₁} t₂`
    have hlen : 1 < Lng M := by
      simp only [transJ1, lastIdx] at hj₁; omega
    rw [← pred_is_oper1 M hM hlen, ← hc₁eq]
    exact hd₁
  · -- (3) kind-1: `RightNodes (transC2 M) = [u, v]` と `u < v`
    intro p hp
    have hc₂ : transC2 M = .trm [p] := by
      apply flatBT_injective
      simpa [flatBT] using hp
    have hrn : RightNodes (.trm [p]) =
        [(transV M).toNat, entry M 1 (transJ1 M)] := by
      rw [← hc₂]
      have hA : (transCondI M || transCondIII M || transCondV M
        || transCondVI M) = true := by simp [hcond]
      simpa [hA] using RightNodes_transC2_tail M
    have huv : (transV M).toNat < entry M 1 (transJ1 M) := by
      have hV : transV M = (entry M 1 (transJm1 M) : ℕ∞) := _hV
      rw [hV]
      simpa using condV_uv_xv M hM hmono hj₁ hcond
    simp only [hrn]
    exact ⟨by simp, by simpa using huv, by intro j hj0 hj1; simp at hj1; omega⟩

/-! ## `ExchV_scbdec_adm_forms` の削減（Isabelle `m_8_5_scbdec_adm_forms`, :57556）

`ExchV_scbdec_adm_forms` の 5 連言のうち **(1)(2)(3) は本ファイルで無条件に証明**でき、
残るのは (4)(5)＝**塔の閉形式そのもの**だけである。Isabelle でその 2 本を出す
エンジンは `m_8_4_oper_props_5` (pss_wip.thy:54005)＋`s84x_L`/`s84x_Np`/`s84x_Lp`
＝**§8.4 の scb 分解クラスタ**であり、これは Lean 未移植（`8.6-condVI-close`:238 が
同じ欠落を `c6zx_L_tower` 経由で報告している。原文でも `8.4-scb-decompositions` /
`8.5-fseq-scb-decomposition` は pss_paper 上 DEFERRED）。

そこで残差を **`ExchV_nf3x` と同じ「対 `(s₀,s₁,b₀,b₁)` を仮定に取る」形**に
そろえた `ExchVres_adm_towers` に切り出す。差分は (1)(2)(3) が消えたこと＝
残差から scb 分解の生成（surgery / producer）が除去され、**§8.4 クラスタ由来の
塔の内容だけ**が残る。 -/

/-- **`ExchV_scbdec_adm_forms`（8.5-Trans-fseq-condV:106）の削減**。
Isabelle `m_8_5_scbdec_adm_forms` (pss_wip.thy:57556) の結論 (4)(5) のみ
（＝`m_8_4_oper_props_5` (同 :54005) ＋ `s84x_L` 帰納が出す塔の閉形式）。
(1)(2)(3) は `adm_forms_holds` が `add_scb_marked` ＋ `fseq_condV_holds` で
供給するので残差から消えている。 -/
def ExchVres_adm_towers : Prop :=
  ∀ (M : PS) (s₀ s₁ b₀ b₁ : List Sym), STPS M → monoT M = true →
    transCondV M = true → adm M (transJ0 M) = true →
    scb_decomp (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero))
      s₀ (flatBT (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) b₀ →
    scb_decomp (Trans (oper M 1)) s₁
      (flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞) (transT2 M))) b₁ →
    scb_kind1 (Trans M) s₁ (flatBT (transC2 M)) b₁ →
    (∀ n : ℕ, flatBT (operB (Trans M) (numBT n)) =
        s₁ ++ Sym.dsym (entry M 1 (transJ0 M) : ℕ∞) ::
          (List.replicate (n + 1)
              (s₀ ++ [Sym.dsym (entry M 1 (transJ0 M) : ℕ∞)])).flatten
          ++ [Sym.zero]
          ++ (List.replicate (n + 1) b₀).flatten ++ b₁) ∧
    (∀ k : ℕ, flatBT (Trans (oper M (k + 1))) =
        s₁ ++ Sym.dsym (entry M 1 (transJ0 M) : ℕ∞) ::
          (List.replicate k (s₀ ++ [Sym.dsym (entry M 1 (transJ0 M) : ℕ∞)])).flatten
          ++ flatBT (transT2 M)
          ++ (List.replicate k b₀).flatten ++ b₁)

/-- 許容枝では第 2 基点が潰れる（Isabelle `s85b_jm1_adm`, pss_wip.thy:57138）。 -/
private theorem jm1_adm_xv {M : PS} (h : adm M (transJ0 M) = true) :
    transJm1 M = transJ0 M := by
  simp [transJm1, Adm, h]

theorem adm_forms_holds (hres : ExchVres_adm_towers) : ExchV_scbdec_adm_forms := by
  intro M hST hmono hcond hadm
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := STPS_TPS M hST
  obtain ⟨hj₁, ht₁⟩ := condV_setup_holds M hR hM hmono hcond
  obtain ⟨_hV, _hc₁eq, ht₂TB, _hjm1lt⟩ := c1_shape_holds M hR hM hmono hj₁ ht₁
  have hjm1 : transJm1 M = transJ0 M := jm1_adm_xv hadm
  -- (1) 内側の対 `(s₀,b₀)`: `t₂ + D_{M₁,j₁} 0` の末尾 principal は marked
  have hdvTB : Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero ∈ T_B := by
    apply Dprin_mem_T_B (by simp)
    simp [T_B, BZero, dfree_BT, dfree_BPList]
  have hdvP : ∃ p, Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero = .trm [p] :=
    ⟨_, rfl⟩
  obtain ⟨s₀, b₀, hd₀⟩ := add_scb_marked (transT2 M)
    (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero) ht₂TB hdvTB hdvP
  -- (2)(3) 外側の対 `(s₁,b₁)`: 本ファイルの `fseq_condV_holds`
  obtain ⟨s₁, b₁, hd₁, hk₁⟩ := fseq_condV_holds M hR hM hmono hj₁ ht₁ hcond
  rw [hjm1] at hd₁
  -- (4)(5) 塔の閉形式は残差から
  obtain ⟨h4, h5⟩ := hres M s₀ s₁ b₀ b₁ hST hmono hcond hadm hd₀ hd₁ hk₁
  exact ⟨s₀, s₁, b₀, b₁, hd₀, hd₁, hk₁, h4, h5⟩

#print axioms condV_setup_holds
#print axioms c1_shape_holds
#print axioms t2_nonzero_condV_holds
#print axioms fseq_condV_holds
#print axioms adm_forms_holds

end PSS
