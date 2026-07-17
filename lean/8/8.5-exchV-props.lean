import «8».«8.5-Trans-fseq-condV»
import «7».«7.4-RightNodes-Mark»
import «7».«7.3-Mark-rightmost1»
import «7».«7.4-RightAnces-RightNodes»
import «7».«7.2-scb-fseq»
import «7».«7.1-buchholz-fseq-lt»

/-!
# §8.5 exchV の named Prop の解消（`ExchV_*` の drop-in）

- 原文: `tmp/content.md` §8.5「補題（条件(V)の下での各種scb分解）」(5213) と
  その周辺（`c₁` の形・`t₂ ≠ 0`・再帰の guard）。
- 対象: ビルド済み «8».«8.5-Trans-fseq-condV» が green-modulo に残した 6 本の
  named Prop。本ファイルは **4 本を無条件に discharge** し、**2 本を削減**する
  （house pattern: 定理の型が Prop そのもの＝drop-in が elaborator により保証される）。
  | Prop | 本ファイル | 状態 |
  |---|---|---|
  | `ExchV_condV_setup` | `condV_setup_holds` | ✅ 無条件 |
  | `ExchV_scbdec_c1_shape` | `c1_shape_holds` | ✅ 無条件 |
  | `ExchV_t2_nonzero_condV` | `t2_nonzero_condV_holds` | ✅ 無条件 |
  | `ExchV_scbdec_fseq_condV` | `fseq_condV_holds` | ✅ 無条件 |
  | `ExchV_scbdec_adm_forms` | `adm_forms_holds` | ⚠️ `ExchVres_adm_M_tower` 上 |
  | `ExchV_nf3x` | `nf3x_holds` | ⚠️ `ExchVres_nadm_M_tower` 上 |

  **残差 2 本はいずれも「`Trans(M[k+1])` の塔閉形式」**（adm 枝／非 adm 枝）で、
  ともに §8.4 `s84x_L` 塔クラスタ（`m_8_4_oper_props_5`）を engine とする。
  `operB`（Buchholz）側は**両枝とも本ファイルで無条件に閉じた**ので、
  残差は純粋にペア数列側の事実のみ。
  ⚠️**ただし 2 本は「同一の Prop」ではない**（統合しようとして反証した）:
  adm 枝は `replicate k` ブロック、非 adm 枝は `e5x_bodyM t₂ e k` 経由で
  `k = j+1` のとき `replicate (j+2)` ブロック＝**塔 1 段分ずれている**
  （`e5x_bodyM t e 0 = t` だけ W を持たないための不連続。Isabelle の
  `nfx_M_tower` :64341 の注記「the step is the ADM proof … shifted by one tower
  level (outer head `u = M₁,j₋₁ ≠ e` and `+1` block from the deeper `L₁` base)」と
  一致）。よって「残差 1 本に一本化」は**偽**であり、2 本のまま報告する。
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
  - `ExchV_nf3x` = `atx_nf3x` (同 :86273) → `wnx_nf3x` (:81434) → `nf3x_NFall`
    (:69697) → `nf2x_NFall` (:66850) → **`nfx_NFall` (:64558)**。本ファイルはこの
    最下段の 2 エンジン分割（`nfx_operB_form` :64249 ／ `nfx_M_tower` :64348）を
    そのまま使い、前者を証明・後者を残差にする。
- 依存（すべてビルド済み）: «8».«8.5-Trans-fseq-condV»（`ExchV_*` の Prop 本体、
  推移的に «7».«7.3-c1-c2-order» = `transC1_single_principal` /
  `principal_reconstruct` / `Marked_index_le_last`、«7».«7.3-Trans-welldefined»
  = `replaceScb_spec` / `Trans_Mark_mono_equations` / `Trans_Mark_invariant` /
  `transC2Core_properties`、«7».«7.2-add-scb» = `add_scb_marked`、
  «5».«5.3-pred-is-oper1» = `pred_is_oper1`）、«7».«7.4-RightNodes-Mark»
  （`Mark_leftend_form_proper`）、«7».«7.3-Mark-rightmost1»
  （`Mark_rightmost1_forward` / `Mark_tail_nonzero`）、
  «7».«7.4-RightAnces-RightNodes»（`RightNodes_transC2_tail`
  ＝ Isabelle `ra_RightNodes_transC2_tail`）、
  **«7».«7.2-scb-fseq»（`scb_fseq_kind1_general` ＝ `m_7_2_scb_fseq_kind1_general`、
  `operB` 塔の唯一のエンジン）**、«7».«7.1-buchholz-fseq-lt»（`domTag_snoc_bf`）、
  «7».«7.2-scb-unique»（`scb_unique_decomp_unconditional`
  ＝ `m_7_2_scb_unique_sb`、推移的）。
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
- 状態: GREEN（sorry 0）。**4/6 無条件 discharge ＋ 2/6 削減**。
  残差は `ExchVres_adm_M_tower` / `ExchVres_nadm_M_tower`（ともに本ファイル定義）の
  2 本のみ。両者は「共有手術 `(s₁,b₁)` の内側での `Trans(M[k+1])` の塔閉形式」で
  **塔の段数が 1 だけずれた adm 枝 / 非 adm 枝**（上記 ⚠️ 参照）であり、ともに
  **§8.4 scb 分解クラスタ（`m_8_4_oper_props_5` :54005 ＋ `s84x_L`/`s84x_Np`/`s84x_Lp`
  の 67 補題、pss_wip 52620–54200）の Lean 未移植**という単一の欠落に帰着する
  （非 adm 枝はさらに `wnx_*`/`ncx_*`/`atx_*`/`nfx_*` の r27–r28 スライス値 ~50 補題を
  要する）。`needs` 参照。
- 🔑**本ラウンドの前進**（`operB` 側の完全除去）: Isabelle の `nfx_NFall` (:64558) は
  2 結論を**別エンジン**で出しており、`operB` 側 (`nfx_operB_form` :64249) は
  **§8.4 クラスタを使わない**（`m_8_5_scbdec_fseq_condV` conjunct (4) ＋
  `nfx_bodyO_flat` の文字列書き換えのみ）。その conjunct (4) 自体も
  `m_7_2_scb_fseq_kind1_general`（＝Lean `scb_fseq_kind1_general`, 7.2-scb-fseq:689、
  **移植済み**）で出る。よって `fseq_condV_full_xv`（4 連言 FULL 版）＋
  `operB_form_xv` により、adm/非 adm 両枝の `operB` 塔を無条件化できた。
  Isabelle が要した `m_8_5_TransCondV_producer` (:38761) は Lean では不要
  （`fseq_condV_holds` が `(s₁,b₁)` を最初から共有対として出すため）。
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

/-- Isabelle `m_8_5_transC2_condV` (pss_wip.thy:51498 で消費)。条件(V) 枝の
  `c₂` の閉形式 `c₂ = D_{transV}(t₂ +_B D_{M₁,j₁} 0_B)`。 -/
private theorem transC2_condV_xv (M : PS) (hcond : transCondV M = true) :
    transC2 M = Dprin (transV M)
      (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) := by
  have hA : (transCondI M || transCondIII M || transCondV M) = true := by
    simp [hcond]
  simp [transC2, transC2Core, hA, transJ1]

/-- `c₂` は principal（`transC2Core_principal` 相当を `transC2_condV_e5` の形から）。 -/
private theorem transC2_principal_xv (M : PS) (hcond : transCondV M = true) :
    ∃ p, transC2 M = .trm [p] :=
  ⟨.db (transV M) _, by simpa [Dprin] using transC2_condV_xv M hcond⟩

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

/-! ## `operB` 側の塔閉形式（Isabelle `m_8_5_scbdec_fseq_condV`, :51466 の conjunct (4)）

**これが残差から Buchholz 側を完全に除去する鍵**（`8.6-condVI-close` の
`operB_fseq_value_v6` と同じ勝ち筋）。Isabelle は conjunct (4) を
`m_7_2_scb_fseq_kind1_general` (＝Lean `scb_fseq_kind1_general`,
7.2-scb-fseq:689、**移植済み・ビルド済み**) に、`body = t₂ +_B D_{M₁,j₁} 0_B` を
差し込んで出している。必要な 6 つの入力はすべて本ファイル内で無条件に揃う:

| 入力 | 供給元 |
|---|---|
| `t = Trans M ∈ T_B` | `Trans_mem_T_B`（＝`m_7_3_Trans_in_T_B`） |
| `u < v`（`u = M₁,j₋₁`, `v = M₁,j₁`） | `condV_uv_xv`（＝`m_8_5_condV_uv`） |
| `body ∈ T_B` | `addBT_mem_T_B` ＋ `c1_shape_holds` の `t₂ ∈ T_B` |
| `domTag body = below (v-1)` | `domTag_addBT_Dv0_xv`（下記、`domTag_snoc_bf` 一発） |
| `inner`（`(s₀,b₀)`） | `add_scb_marked`（＝`m_7_2_add_scb_conj1`） |
| `k1`（`(s₁,b₁)`） | 本ファイルの `fseq_condV_holds` ＋ `transC2_condV_xv` |

Isabelle が要した `m_8_5_TransCondV_producer` (:38761) と一意性段
`m_7_2_scb_unique_sb` は、Lean では `fseq_condV_holds` が `(s₁,b₁)` を
**最初から共有対として**出すので不要。 -/

/-- `domTag (D_v 0_B) = below (v-1)`（`8.6-condVI-close` の `domTag_Dv0_v6` は
  `private` なので同じ証明を複製）。 -/
private theorem domTag_Dv0_xv (v : ℕ) (hv : 0 < v) :
    domTag (Dprin (v : ℕ∞) BZero) = .below (v - 1) := by
  simp [domTag, domTagList, domTagBP, Dprin, BZero,
    show (v : ℕ∞) ≠ 0 by simpa using (Nat.ne_of_gt hv), ENat.coe_ne_top]

/-- Isabelle の `dbbody`（`m_8_5_TransCondV_producer` の conjunct 2）に対応。
  `domTag` は末尾 principal しか見ないので、`t₂ +_B` は素通りする。 -/
private theorem domTag_addBT_Dv0_xv (t : BT) (v : ℕ) (hv : 0 < v) :
    domTag (addBT t (Dprin (v : ℕ∞) BZero)) = .below (v - 1) := by
  rcases t with ⟨ps⟩
  have hsnoc : addBT (.trm ps) (Dprin (v : ℕ∞) BZero)
      = .trm (ps ++ [.db (v : ℕ∞) BZero]) := by
    simp [addBT, Dprin]
  rw [hsnoc, domTag_snoc_bf]
  have := domTag_Dv0_xv v hv
  simpa [domTag, domTagList, Dprin] using this

/-- `t₂ +_B D_v 0_B ≠ 0_B`（末尾に principal が付くので空にならない）。 -/
private theorem addBT_Dv0_ne_BZero_xv (t : BT) (v : ℕ) :
    addBT t (Dprin (v : ℕ∞) BZero) ≠ BZero := by
  rcases t with ⟨ps⟩
  simp [addBT, Dprin, BZero]

/-- **Isabelle `m_8_5_scbdec_fseq_condV` (pss_wip.thy:51466) の 4 連言 FULL 版**。
  `8.5-Trans-fseq-condV` の named Prop `ExchV_scbdec_fseq_condV` は (2)(3) しか
  取っていないが、Isabelle の原形は (1) inner ＋ (4) `operB` 塔閉形式も出す。
  ここで**全 4 連言を無条件に**証明する。 -/
private theorem fseq_condV_full_xv (M : PS) (hR : RTPS M) (hM : TPS M)
    (hmono : monoT M = true) (hj₁ : 0 < transJ1 M) (ht₁ : transT1 M ≠ BZero)
    (hcond : transCondV M = true) :
    ∃ s₀ s₁ b₀ b₁ : List Sym,
      scb_decomp (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero))
        s₀ (flatBT (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) b₀ ∧
      scb_decomp (Trans (oper M 1)) s₁
        (flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M))) b₁ ∧
      scb_kind1 (Trans M) s₁ (flatBT (transC2 M)) b₁ ∧
      (∀ n : ℕ, flatBT (operB (Trans M) (numBT n)) =
        s₁ ++ Sym.dsym (entry M 1 (transJm1 M) : ℕ∞) ::
          (List.replicate (n + 1)
              (s₀ ++ [Sym.dsym (entry M 1 (transJ0 M) : ℕ∞)])).flatten
          ++ [Sym.zero]
          ++ (List.replicate (n + 1) b₀).flatten ++ b₁) := by
  obtain ⟨_hV, _hc₁eq, ht₂TB, _hjm1lt⟩ := c1_shape_holds M hR hM hmono hj₁ ht₁
  obtain ⟨s₁, b₁, hd₁, hk₁⟩ := fseq_condV_holds M hR hM hmono hj₁ ht₁ hcond
  -- 条件(V) の算術: `0 < v₁` と `v₁ - 1 = M₁,j₀`
  have hev := condV_parts_xv hcond
  have hv₁pos : 0 < entry M 1 (transJ1 M) := by
    simp only [transJ1]; exact hev.1
  have hj0v : entry M 1 (transJ1 M) - 1 = entry M 1 (transJ0 M) := by
    simp only [transJ1, transJ0] at *; omega
  -- (1) inner: `(s₀, b₀)`
  have hdvTB : Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero ∈ T_B := by
    apply Dprin_mem_T_B (by simp)
    simp [T_B, BZero, dfree_BT, dfree_BPList]
  obtain ⟨s₀, b₀, hd₀⟩ := add_scb_marked (transT2 M)
    (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero) ht₂TB hdvTB ⟨_, rfl⟩
  refine ⟨s₀, s₁, b₀, b₁, hd₀, hd₁, hk₁, ?_⟩
  -- (4) `operB` 塔: `scb_fseq_kind1_general` 一発
  intro n
  have hk₁body : scb_kind1 (Trans M) s₁
      (flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞)
        (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)))) b₁ := by
    rw [transC2_condV_xv M hcond, _hV] at hk₁
    exact hk₁
  have h := (scb_fseq_kind1_general
      (t := Trans M)
      (body := addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero))
      (u := entry M 1 (transJm1 M)) (v := entry M 1 (transJ1 M)) (n := n)
      (s₀ := s₀) (s₁ := s₁) (b₀ := b₀) (b₁ := b₁)
      (Trans_mem_T_B M hR) (condV_uv_xv M hM hmono hj₁ hcond)
      (addBT_mem_T_B ht₂TB hdvTB)
      (domTag_addBT_Dv0_xv (transT2 M) (entry M 1 (transJ1 M)) hv₁pos)
      (addBT_Dv0_ne_BZero_xv (transT2 M) (entry M 1 (transJ1 M)))
      hd₀ hk₁body).2
  rw [h, hj0v]
  simp [List.append_assoc]

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
Isabelle `m_8_5_scbdec_adm_forms` (pss_wip.thy:57556) の結論 **(5) のみ**
（＝Isabelle `nfx_M_tower` (同 :64348) の adm 版＝`m_8_4_oper_props_5`
(同 :54005) ＋ `s84x_L` 塔帰納が出す `Trans(M[k+1])` の閉形式）。

(1)(2)(3) は `add_scb_marked` ＋ `fseq_condV_holds` が、
**(4)（`operB` 側の塔）は `fseq_condV_full_xv` が `scb_fseq_kind1_general` から**
供給するので、いずれも残差から消えている。＝**残差は Buchholz 側を一切含まず、
純粋にペア数列側（`Trans(M[k+1])` の値）の 1 事実**である。 -/
def ExchVres_adm_M_tower : Prop :=
  ∀ (M : PS) (s₀ s₁ b₀ b₁ : List Sym), STPS M → monoT M = true →
    transCondV M = true → adm M (transJ0 M) = true →
    scb_decomp (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero))
      s₀ (flatBT (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) b₀ →
    scb_decomp (Trans (oper M 1)) s₁
      (flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞) (transT2 M))) b₁ →
    scb_kind1 (Trans M) s₁ (flatBT (transC2 M)) b₁ →
    (∀ k : ℕ, flatBT (Trans (oper M (k + 1))) =
        s₁ ++ Sym.dsym (entry M 1 (transJ0 M) : ℕ∞) ::
          (List.replicate k (s₀ ++ [Sym.dsym (entry M 1 (transJ0 M) : ℕ∞)])).flatten
          ++ flatBT (transT2 M)
          ++ (List.replicate k b₀).flatten ++ b₁)

/-- 許容枝では第 2 基点が潰れる（Isabelle `s85b_jm1_adm`, pss_wip.thy:57138）。 -/
private theorem jm1_adm_xv {M : PS} (h : adm M (transJ0 M) = true) :
    transJm1 M = transJ0 M := by
  simp [transJm1, Adm, h]

theorem adm_forms_holds (hres : ExchVres_adm_M_tower) : ExchV_scbdec_adm_forms := by
  intro M hST hmono hcond hadm
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := STPS_TPS M hST
  obtain ⟨hj₁, ht₁⟩ := condV_setup_holds M hR hM hmono hcond
  have hjm1 : transJm1 M = transJ0 M := jm1_adm_xv hadm
  -- (1)(2)(3)(4) はすべて `fseq_condV_full_xv` が同じ 4 つ組で供給する
  obtain ⟨s₀, s₁, b₀, b₁, hd₀, hd₁, hk₁, h4⟩ :=
    fseq_condV_full_xv M hR hM hmono hj₁ ht₁ hcond
  rw [hjm1] at hd₁ h4
  -- (5) `Trans(M[k+1])` の塔だけが残差
  have h5 := hres M s₀ s₁ b₀ b₁ hST hmono hcond hadm hd₀ hd₁ hk₁
  exact ⟨s₀, s₁, b₀, b₁, hd₀, hd₁, hk₁, h4, h5⟩

/-! ## `ExchV_nf3x` の削減（Isabelle `atx_nf3x`, pss_wip.thy:86273）

Isabelle の連鎖は `atx_nf3x` → `wnx_nf3x` (:81434) → `nf3x_NFall` (:69697)
→ `nf2x_NFall` (:66850) → **`nfx_NFall` (:64558)** であり、その `nfx_NFall` は
2 つの結論を**別々の**エンジンで出している:

- 結論 (2)（`operB` 側）＝ **`nfx_operB_form` (:64249)。adm/非 adm 共通・無条件**で、
  `m_8_5_scbdec_fseq_condV` の conjunct (4) ＋ `nfx_bodyO_flat` (:64207) の
  文字列書き換えだけ。**§8.4 クラスタを一切使わない。**
- 結論 (1)（`Trans(M[k+1])` 側）＝ `nfx_M_tower` (:64348)。こちらが
  `m_8_4_oper_props_5` (:54005) ＋ `s84x_L` 塔帰納（＝§8.4 クラスタ）に乗り、
  さらに非 adm 枝では `PredNp`/`Lpv`/`L1v` の 3 スライス値（`wnx_*`/`atx_c2L1`、
  r27–r28 の数百補題）を要する。

そこで本ファイルは **結論 (2) を `operB_form_xv` で無条件に証明**し、残差を
結論 (1) だけの `ExchVres_nadm_M_tower` に切り出す。これで adm 枝
（`ExchVres_adm_M_tower`）と非 adm 枝の残差が**どちらも「`Trans(M[k+1])` の塔閉形式」
という同一形**にそろい、exchV の未閉部分は **§8.4 の `s84x_L` 塔クラスタ 1 点**に
一本化される。 -/

/-! ### `s85b_W` の flat 機構（`8.5-Trans-fseq-condV` の同名 `_e5` 群が `private`
なので、同じ証明を `_xv` 名で複製する） -/

private theorem flatBP_db_e5_xv (v : ℕ∞) (a : BT) :
    flatBP (.db v a) = Sym.dsym v :: flatBT a := rfl

private theorem s85b_W_principal_xv (u : ℕ) (t c : BT) (k : ℕ) :
    ∃ b, s85b_W u t c k = Dprin (u : ℕ∞) b := by
  cases k with
  | zero => exact ⟨c, rfl⟩
  | succ j => exact ⟨addBT t (s85b_W u t c j), rfl⟩

private theorem s85b_W_mem_T_B_xv {u : ℕ} {t c : BT} (ht : t ∈ T_B) (hc : c ∈ T_B)
    (k : ℕ) : s85b_W u t c k ∈ T_B := by
  induction k with
  | zero => exact Dprin_mem_T_B (by simp) hc
  | succ j ih => exact Dprin_mem_T_B (by simp) (addBT_mem_T_B ht ih)

private theorem flatten_replicate_comm_xv {α : Type} (b : List α) (j : ℕ) :
    (List.replicate j b).flatten ++ b = b ++ (List.replicate j b).flatten := by
  induction j with
  | zero => simp
  | succ i ih =>
      rw [List.replicate_succ, List.flatten_cons, List.append_assoc, ih]

/-- `(replicate j b).flatten ++ b = (replicate (j+1) b).flatten`。 -/
private theorem flatten_replicate_snoc_xv {α : Type} (b : List α) (j : ℕ) :
    (List.replicate j b).flatten ++ b = (List.replicate (j + 1) b).flatten := by
  rw [flatten_replicate_comm_xv, List.replicate_succ, List.flatten_cons]

private theorem rot_cons_xv (x : Sym) (s : List Sym) (k : ℕ) :
    x :: (List.replicate k (s ++ [x])).flatten
      = (List.replicate k (x :: s)).flatten ++ [x] := by
  induction k with
  | zero => simp
  | succ j ih =>
      have : x :: (List.replicate (j + 1) (s ++ [x])).flatten
          = (x :: s) ++ (x :: (List.replicate j (s ++ [x])).flatten) := by
        simp [List.replicate_succ, List.append_assoc]
      rw [this, ih]
      simp [List.replicate_succ, List.append_assoc]

/-- Isabelle `nfx_rot_s0` (pss_wip.thy:64198)。 -/
private theorem rot_s0_xv (s₀ : List Sym) (d : Sym) (j : ℕ) :
    s₀ ++ (List.replicate j (d :: s₀)).flatten
      = (List.replicate j (s₀ ++ [d])).flatten ++ s₀ := by
  induction j with
  | zero => simp
  | succ i ih =>
      calc s₀ ++ (List.replicate (i + 1) (d :: s₀)).flatten
          = (s₀ ++ [d]) ++ (s₀ ++ (List.replicate i (d :: s₀)).flatten) := by
            simp [List.replicate_succ, List.append_assoc]
        _ = (s₀ ++ [d]) ++ ((List.replicate i (s₀ ++ [d])).flatten ++ s₀) := by
            rw [ih]
        _ = (List.replicate (i + 1) (s₀ ++ [d])).flatten ++ s₀ := by
            simp [List.replicate_succ, List.append_assoc]

/-- Isabelle `s85b_W_flat` (pss_wip.thy:58014)。 -/
private theorem s85b_W_flat_xv {u : ℕ} {t c0 c : BT} {s₀ b₀ : List Sym}
    (htTB : t ∈ T_B) (hc0TB : c0 ∈ T_B) (hc0p : ∃ p, c0 = .trm [p])
    (hinner : scb_decomp (addBT t c0) s₀ (flatBT c0) b₀)
    (hcTB : c ∈ T_B) (k : ℕ) :
    flatBT (s85b_W u t c k)
      = (List.replicate k (Sym.dsym (u : ℕ∞) :: s₀)).flatten
        ++ flatBT (Dprin (u : ℕ∞) c) ++ (List.replicate k b₀).flatten := by
  induction k with
  | zero => simp [s85b_W]
  | succ j ih =>
      have hWTB : s85b_W u t c j ∈ T_B := s85b_W_mem_T_B_xv htTB hcTB j
      have hWp : ∃ p, s85b_W u t c j = BT.trm [p] := by
        obtain ⟨b, hb⟩ := s85b_W_principal_xv u t c j
        exact ⟨.db (u : ℕ∞) b, by simpa [Dprin] using hb⟩
      have hsub : scb_decomp (addBT t (s85b_W u t c j)) s₀
          (flatBT (s85b_W u t c j)) b₀ :=
        add_scb_replace_last t c0 (s85b_W u t c j) s₀ b₀ htTB hc0TB hc0p hWTB hWp hinner
      have hfsub : flatBT (addBT t (s85b_W u t c j))
          = s₀ ++ flatBT (s85b_W u t c j) ++ b₀ := hsub.1
      have hstep : flatBT (s85b_W u t c (j + 1))
          = Sym.dsym (u : ℕ∞) :: flatBT (addBT t (s85b_W u t c j)) := by
        simp [s85b_W, Dprin, flatBT, flatBP]
      rw [hstep, hfsub, ih]
      simp only [List.replicate_succ, List.flatten_cons, List.append_assoc,
        List.cons_append]
      rw [flatten_replicate_comm_xv b₀ j]

/-- Isabelle `nfx_bodyO_flat` (pss_wip.thy:64207)。`operB` 側の内部 body の flat 形。 -/
private theorem bodyO_flat_xv {t₂ : BT} {e v₁ : ℕ} {s₀ b₀ : List Sym}
    (ht₂ : t₂ ∈ T_B)
    (hinner : scb_decomp (addBT t₂ (Dprin (v₁ : ℕ∞) BZero)) s₀
      (flatBT (Dprin (v₁ : ℕ∞) BZero)) b₀) (m : ℕ) :
    flatBT (e5x_bodyO t₂ e m)
      = (List.replicate (m + 1) (s₀ ++ [Sym.dsym (e : ℕ∞)])).flatten ++ [Sym.zero]
        ++ (List.replicate (m + 1) b₀).flatten := by
  have hc0TB : Dprin (v₁ : ℕ∞) BZero ∈ T_B := by
    apply Dprin_mem_T_B (by simp)
    simp [T_B, BZero, dfree_BT, dfree_BPList]
  have hBZ : (BZero : BT) ∈ T_B := by
    simp [T_B, BZero, dfree_BT, dfree_BPList]
  -- `W` の flat 形（種 `0_B`）
  have hWflat := s85b_W_flat_xv (u := e) (t := t₂) (c0 := Dprin (v₁ : ℕ∞) BZero)
    (c := BZero) (s₀ := s₀) (b₀ := b₀) ht₂ hc0TB ⟨_, rfl⟩ hinner hBZ m
  -- 外側の `t₂ +_B W` を `add_scb_replace_last` で剥がす
  have hWTB : s85b_W e t₂ BZero m ∈ T_B := s85b_W_mem_T_B_xv ht₂ hBZ m
  have hWp : ∃ p, s85b_W e t₂ BZero m = BT.trm [p] := by
    obtain ⟨b, hb⟩ := s85b_W_principal_xv e t₂ BZero m
    exact ⟨.db (e : ℕ∞) b, by simpa [Dprin] using hb⟩
  have haddf : scb_decomp (addBT t₂ (s85b_W e t₂ BZero m)) s₀
      (flatBT (s85b_W e t₂ BZero m)) b₀ :=
    add_scb_replace_last t₂ (Dprin (v₁ : ℕ∞) BZero) (s85b_W e t₂ BZero m) s₀ b₀
      ht₂ hc0TB ⟨_, rfl⟩ hWTB hWp hinner
  have hbody : flatBT (e5x_bodyO t₂ e m) = s₀ ++ flatBT (s85b_W e t₂ BZero m) ++ b₀ := by
    have : e5x_bodyO t₂ e m = addBT t₂ (s85b_W e t₂ BZero m) := rfl
    rw [this]
    exact haddf.1
  rw [hbody, hWflat]
  -- 文字列代数: 回転 ＋ replicate の snoc
  have hDe : flatBT (Dprin (e : ℕ∞) BZero) = [Sym.dsym (e : ℕ∞), Sym.zero] := by
    simp [Dprin, flatBT, flatBP, BZero]
  rw [hDe]
  have hrot : s₀ ++ (List.replicate m (Sym.dsym (e : ℕ∞) :: s₀)).flatten
      = (List.replicate m (s₀ ++ [Sym.dsym (e : ℕ∞)])).flatten ++ s₀ :=
    rot_s0_xv s₀ (Sym.dsym (e : ℕ∞)) m
  calc s₀ ++ ((List.replicate m (Sym.dsym (e : ℕ∞) :: s₀)).flatten
          ++ [Sym.dsym (e : ℕ∞), Sym.zero] ++ (List.replicate m b₀).flatten) ++ b₀
      = (s₀ ++ (List.replicate m (Sym.dsym (e : ℕ∞) :: s₀)).flatten)
          ++ ([Sym.dsym (e : ℕ∞)] ++ [Sym.zero])
          ++ ((List.replicate m b₀).flatten ++ b₀) := by
        simp [List.append_assoc]
    _ = ((List.replicate m (s₀ ++ [Sym.dsym (e : ℕ∞)])).flatten ++ s₀)
          ++ ([Sym.dsym (e : ℕ∞)] ++ [Sym.zero])
          ++ ((List.replicate m b₀).flatten ++ b₀) := by rw [hrot]
    _ = ((List.replicate m (s₀ ++ [Sym.dsym (e : ℕ∞)])).flatten
          ++ (s₀ ++ [Sym.dsym (e : ℕ∞)])) ++ [Sym.zero]
          ++ ((List.replicate m b₀).flatten ++ b₀) := by simp [List.append_assoc]
    _ = (List.replicate (m + 1) (s₀ ++ [Sym.dsym (e : ℕ∞)])).flatten ++ [Sym.zero]
          ++ (List.replicate (m + 1) b₀).flatten := by
        rw [flatten_replicate_snoc_xv, flatten_replicate_snoc_xv]

/-- **Isabelle `nfx_operB_form` (pss_wip.thy:64249) の Lean 版**。
  条件(V) ホストなら **adm/非 adm を問わず無条件**に、`d1h` が指定する対
  `(s₁,b₁)` の内側で `operB (Trans M) (numBT m)` は `D_{M₁,j₋₁}(e5x_bodyO t₂ e m)`。
  一意性段は `scb_unique_decomp_unconditional`（＝`m_7_2_scb_unique_sb`）。 -/
private theorem operB_form_xv (M : PS) (s₁ b₁ : List Sym) (hR : RTPS M) (hM : TPS M)
    (hmono : monoT M = true) (hj₁ : 0 < transJ1 M) (ht₁ : transT1 M ≠ BZero)
    (hcond : transCondV M = true)
    (hd1h : scb_decomp (Trans (oper M 1)) s₁
      (flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M))) b₁) (m : ℕ) :
    flatBT (operB (Trans M) (numBT m))
      = s₁ ++ flatBP (.db (entry M 1 (transJm1 M) : ℕ∞)
          (e5x_bodyO (transT2 M) (entry M 1 (transJ0 M)) m)) ++ b₁ := by
  obtain ⟨_hV, _hc₁eq, ht₂TB, _hjm1lt⟩ := c1_shape_holds M hR hM hmono hj₁ ht₁
  obtain ⟨s₀, s₁', b₀, b₁', hd₀, hd₁', _hk₁, h4⟩ :=
    fseq_condV_full_xv M hR hM hmono hj₁ ht₁ hcond
  -- `(s₁,b₁)` の同定（両者とも `Trans (M[1])` の同じ core での分解）
  obtain ⟨hs, hb⟩ := scb_unique_decomp_unconditional (Trans (oper M 1)) s₁' s₁
    (flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M))) b₁' b₁ hd₁' hd1h
  subst hs; subst hb
  rw [h4 m]
  -- body の flat 形に畳み戻す
  have hbodyO := bodyO_flat_xv (t₂ := transT2 M) (e := entry M 1 (transJ0 M))
    (v₁ := entry M 1 (transJ1 M)) (s₀ := s₀) (b₀ := b₀) ht₂TB hd₀ m
  rw [flatBP_db_e5_xv, hbodyO]
  simp [List.append_assoc]

/-- **`ExchV_nf3x`（8.5-Trans-fseq-condV:138）の削減**。
Isabelle `nfx_M_tower` (pss_wip.thy:64348) の非 adm 枝の結論のみ
（＝`m_8_4_oper_props_5` (:54005) の `s84x_L` 塔帰納 ＋ 非 adm 3 スライス値
`nf3x_PredNp`/`nf2x_Lpv`/`nf2x_L1v` ＋ `atx_c2L1`）。
`operB` 側の結論 (2) は `operB_form_xv` が無条件に供給するので残差から消えている。 -/
def ExchVres_nadm_M_tower : Prop :=
  ∀ (M : PS) (s₁ b₁ : List Sym), STPS M → monoT M = true → transCondV M = true →
    adm M (parent M 0 (Lng M - 1)) = false →
    scb_decomp (Trans (oper M 1)) s₁
      (flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M))) b₁ →
    scb_kind1 (Trans M) s₁ (flatBT (transC2 M)) b₁ →
    (∀ k : ℕ, flatBT (Trans (oper M (k + 1)))
        = s₁ ++ flatBP (.db (entry M 1 (transJm1 M) : ℕ∞)
            (e5x_bodyM (transT2 M) (entry M 1 (transJ0 M)) k)) ++ b₁)

theorem nf3x_holds (hres : ExchVres_nadm_M_tower) : ExchV_nf3x := by
  intro M s₁ b₁ hST hmono hcond hnadm hd1h hk1h
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := STPS_TPS M hST
  obtain ⟨hj₁, ht₁⟩ := condV_setup_holds M hR hM hmono hcond
  refine ⟨hres M s₁ b₁ hST hmono hcond hnadm hd1h hk1h, ?_⟩
  intro m _hm
  exact operB_form_xv M s₁ b₁ hR hM hmono hj₁ ht₁ hcond hd1h m

#print axioms condV_setup_holds
#print axioms c1_shape_holds
#print axioms t2_nonzero_condV_holds
#print axioms fseq_condV_holds
#print axioms adm_forms_holds
#print axioms nf3x_holds

end PSS
